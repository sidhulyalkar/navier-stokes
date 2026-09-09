from fractions import Fraction

from blowup_lab.constraint_ledger import default_h_ledger, intersect_constraints, ledger_report


def test_full_ledger_is_feasible_and_formalization_bound_is_active():
    summary = intersect_constraints(default_h_ledger(), "h")
    assert summary.feasible
    assert summary.lower == Fraction(0)
    assert summary.lower_strict
    assert summary.upper == Fraction(1, 1000)
    assert "H_FORMALIZATION_SMALL_PARAMETERS" in summary.active_upper_ids


def test_ledger_keeps_sharpness_open():
    report = ledger_report()
    assert report["scientific_interpretation"]["sharpness_claimed"] is False
    assert report["scientific_interpretation"]["cheap_scaling_ceiling"] == "1/6"
