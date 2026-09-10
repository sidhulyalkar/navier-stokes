from blowup_lab.enlarged_interval import NormalizedInterval, candidate_interval, enlarged_interval_report


def test_default_candidate_is_one_sided_and_strictly_inside_source_slot():
    I = candidate_interval()
    assert I.left == 0.0
    assert I.right == 1.5
    assert I.inside_source_slot()
    assert I.contains_native()
    assert I.strict_slot_buffer() == 0.5


def test_bad_interval_crossing_source_slot_is_rejected_by_gate():
    report = enlarged_interval_report(NormalizedInterval(0.0, 2.0))
    gate = next(o for o in report["obligations"] if o["obligation_id"] == "candidate_strictly_inside_slot")
    assert gate["status"] == "FAIL"


def test_source_coverage_advances_first_blocker_to_full_wave_residual():
    report = enlarged_interval_report()
    ids = {o["obligation_id"]: o["status"] for o in report["obligations"]}
    assert ids["coefficient_smooth_on_source_slot"] == "PASS"
    assert ids["coefficient_continuous_on_enlarged_interval"] == "DERIVED_READY_TO_FORMALIZE"
    assert ids["normal_nonzero_on_enlarged_interval"] == "DERIVED_READY_TO_FORMALIZE"
    assert ids["kinematics_on_enlarged_interval"] == "DERIVED_READY_TO_FORMALIZE"
    assert ids["finite_interval_homogeneous_solution"] == "READY_ON_CONTINUITY_GATE"
    assert ids["agreement_with_native_primary"] == "READY_ON_CONSTRUCTION_GATE"
    assert report["first_unresolved_after_source_reuse"]["obligation_id"] == "full_wave_residual_after_extension"


def test_report_keeps_formalization_claim_boundary_closed():
    report = enlarged_interval_report()
    assert "does not claim" in report["claim_boundary"]
    assert "Lean-checked" in report["claim_boundary"]
