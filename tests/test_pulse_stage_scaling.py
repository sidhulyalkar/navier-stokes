import math

from blowup_lab.pulse_stage_scaling import (
    StageScaling,
    asymptotic_coordinate_report,
    gaussian_fixed_fraction_exponent_bounds,
    stage_from_carrier_bounds,
)


def test_source_scale_relations_are_consistent():
    s = StageScaling(h=0.01, n=100, r0=1.0, tg=2.0)
    lo, hi = s.carrier_bounds()
    assert lo <= hi
    ell_lo, ell_hi = s.slot_length_bounds()
    assert ell_lo == 2 * 100**2
    assert ell_hi == 4 * 100**2


def test_carrier_inversion_contains_original_stage():
    h = 0.01
    n = 100
    k = 2 ** (n * h / 2)
    lo, hi = stage_from_carrier_bounds(h, k)
    assert lo <= n <= hi


def test_fixed_fraction_decay_is_log_squared_in_carrier_coordinate():
    h = 0.02
    k1, k2 = 32.0, 1024.0
    e1 = gaussian_fixed_fraction_exponent_bounds(h=h, k=k1, r0=1, tg=2, c=1, fraction=0.25)[1]
    e2 = gaussian_fixed_fraction_exponent_bounds(h=h, k=k2, r0=1, tg=2, c=1, fraction=0.25)[1]
    ratio = e2 / e1
    expected = (math.log2(k2) / math.log2(k1)) ** 2
    assert math.isclose(ratio, expected, rel_tol=1e-12)


def test_report_promotes_fixed_fraction_cutoff_geometry_to_source_backed():
    report = asymptotic_coordinate_report()
    assert "source-backed" in report["scientific_update"]
    assert any("L/5" in fact and "L/3" in fact for fact in report["source_facts"])
    assert not any("prove the actual pulse cutoff" in item for item in report["open_obligations"])


def test_report_still_refuses_no_cutoff_global_extension_claim():
    report = asymptotic_coordinate_report()
    assert "does not prove that the cutoffs can be removed" in report["claim_boundary"]
