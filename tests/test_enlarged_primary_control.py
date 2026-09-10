import math

import pytest

from blowup_lab.enlarged_primary_control import (
    cone_stage_threshold,
    conservative_eigenvalue_gap,
    enlarged_control_report,
    interval_budget_factor,
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


def test_uniform_interval_budget_uses_existing_hslot_assumption():
    budget = interval_budget_factor(M=3.0, rho=1.99)
    assert budget["primary_bounds_length_budget"] == 3.0
    assert budget["valid_from_source_assumptions"] is True


def test_cone_threshold_is_finite_for_every_fixed_rho_below_two():
    for rho in (1.0, 1.5, 1.9, 1.99):
        n = cone_stage_threshold(M=2.0, rho=rho, C=5.0)
        assert isinstance(n, int)
        assert n > 0


def test_control_report_separates_reference_envelope_from_gaussian_sandwich():
    report = enlarged_control_report(M=2.0, u=1.0, rho=1.5, C=3.0)
    gates = {g["gate_id"]: g for g in report["gates"]}
    assert gates["modal_error_bounds"]["status"] == "SOURCE_COVERED"
    assert gates["viscosity_reference_error"]["status"] == "SOURCE_COVERED"
    assert gates["extended_reference_envelope_primary_bounds"]["status"] == "READY_AFTER_FORMAL_WRAPPERS"
    assert gates["simple_gaussian_sandwich_beyond_native_ell"]["status"] == "OPEN_NEW_SCALAR_LEMMA"
    assert "No rho>1 primary bound has been Lean-checked" in report["claim_boundary"]


def test_source_slot_boundary_is_fail_closed():
    with pytest.raises(ValueError):
        conservative_eigenvalue_gap(M=2.0, rho=2.0)
