import math

import pytest

from blowup_lab.enlarged_primary_control import (
    cone_stage_threshold,
    conservative_eigenvalue_gap,
    damping_denominator,
    enlarged_control_report,
    interval_budget_factor,
    reference_min_slope,
    three_halves_cone_stage_threshold,
    three_halves_eigenvalue_gap,
    three_halves_gaussian_constants,
    three_halves_reference_max_slope,
)


def test_gap_is_positive_and_decreases_as_extension_factor_grows():
    g1 = conservative_eigenvalue_gap(M=2.0, rho=1.0)
    g15 = conservative_eigenvalue_gap(M=2.0, rho=1.5)
    g19 = conservative_eigenvalue_gap(M=2.0, rho=1.9)
    assert g1 > g15 > g19 > 0


def test_gap_matches_source_formula_bound():
    M, rho = 2.0, 1.5
    expected = 1.0 / (M * math.sqrt(1 + ((rho + 0.5) * M) ** 2))
    assert conservative_eigenvalue_gap(M=M, rho=rho) == pytest.approx(expected)


def test_exact_three_halves_gap_uses_slot_endpoint_2u():
    lam, u = 0.7, 1.25
    expected = lam / math.sqrt(1 + (2 * u) ** 2)
    assert three_halves_eigenvalue_gap(lam=lam, u=u) == pytest.approx(expected)


def test_family_gap_is_conservative_for_allowed_fixed_parameters():
    M, u, lam = 3.0, 1.7, 0.6
    assert lam >= 1 / M
    assert u <= M
    exact = three_halves_eigenvalue_gap(lam=lam, u=u)
    family = conservative_eigenvalue_gap(M=M, rho=1.5)
    assert exact >= family > 0


def test_three_halves_slope_constants_are_positive_and_ordered():
    lam, u = 0.8, 1.1
    lo = reference_min_slope(lam=lam, u=u)
    hi = three_halves_reference_max_slope(lam=lam, u=u)
    assert damping_denominator(u) > 0
    assert 0 < lo < hi


def test_three_halves_gaussian_constants_match_integrated_derivative_form():
    lam, u = 0.8, 1.1
    g = three_halves_gaussian_constants(lam=lam, u=u)
    assert g["c"] == pytest.approx(u * g["reference_min_slope"] / 2)
    assert g["C"] == pytest.approx(u * g["reference_max_slope_three_halves"] / 2)
    assert 0 < g["c"] < g["C"]


def test_uniform_interval_budget_uses_existing_hslot_assumption():
    budget = interval_budget_factor(M=3.0, rho=1.99)
    assert budget["primary_bounds_length_budget"] == 3.0
    assert budget["valid_from_source_assumptions"] is True


def test_cone_threshold_is_finite_for_every_fixed_rho_below_two():
    for rho in (1.0, 1.5, 1.9, 1.99):
        n = cone_stage_threshold(M=2.0, rho=rho, C=5.0)
        assert isinstance(n, int)
        assert n > 0


def test_exact_three_halves_cone_threshold_is_finite():
    n = three_halves_cone_stage_threshold(lam=0.5, u=1.0, C=5.0)
    assert isinstance(n, int)
    assert n > 0


def test_control_report_records_stage_a_formal_evidence_and_stage_b_pending():
    report = enlarged_control_report(M=2.0, u=1.0, rho=1.5, C=3.0)
    gates = {g["gate_id"]: g for g in report["gates"]}
    assert gates["interval_inside_source_slot"]["status"] == "FORMALIZED_SOURCE_LOCKED"
    assert gates["coefficient_continuity"]["status"] == "FORMALIZED_SOURCE_LOCKED"
    assert gates["enlarged_modal_primary"]["status"] == "FORMAL_AUDIT_PENDING"
    assert report["formal_evidence"]["stage_a_lab_commit"]


def test_control_report_separates_reference_envelope_from_gaussian_sandwich():
    report = enlarged_control_report(M=2.0, u=1.0, rho=1.5, C=3.0)
    gates = {g["gate_id"]: g for g in report["gates"]}
    assert gates["modal_error_bounds"]["status"] == "SOURCE_COVERED"
    assert gates["viscosity_reference_error"]["status"] == "SOURCE_COVERED"
    assert gates["extended_reference_envelope_primary_bounds"]["status"] == "READY_AFTER_STAGE_B_AND_CONE"
    assert gates["simple_gaussian_sandwich_beyond_native_ell"]["status"] == "DERIVED_READY_TO_FORMALIZE"
    assert "Stage B remains pending" in report["claim_boundary"]


def test_three_halves_report_contains_exact_scalar_contract():
    report = enlarged_control_report(M=2.0, u=1.0, rho=1.5, C=3.0, lam_probe=0.75)
    exact = report["derived"]["three_halves"]
    assert exact is not None
    assert exact["slot_magnitude_interval"] == [0.5, 2.0]
    assert exact["gap"] == pytest.approx(three_halves_eigenvalue_gap(lam=0.75, u=1.0))
    assert exact["gaussian_constants"]["c"] > 0
    assert exact["gaussian_constants"]["C"] > exact["gaussian_constants"]["c"]


def test_non_three_halves_report_does_not_overclaim_formalization():
    report = enlarged_control_report(M=2.0, u=1.0, rho=1.75, C=3.0)
    gates = {g["gate_id"]: g for g in report["gates"]}
    assert gates["coefficient_continuity"]["status"] == "DERIVED_READY_TO_FORMALIZE"
    assert report["derived"]["three_halves"] is None


def test_source_slot_boundary_is_fail_closed():
    with pytest.raises(ValueError):
        conservative_eigenvalue_gap(M=2.0, rho=2.0)


def test_invalid_exact_parameters_fail_closed():
    with pytest.raises(ValueError):
        three_halves_eigenvalue_gap(lam=0.0, u=1.0)
    with pytest.raises(ValueError):
        three_halves_gaussian_constants(lam=1.0, u=0.0)
