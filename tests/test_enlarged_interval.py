from blowup_lab.enlarged_interval import (
    NormalizedInterval,
    candidate_interval,
    enlarged_interval_report,
    extension_factor_frontier,
)


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


def test_source_coverage_orders_modal_gate_before_kinematics():
    report = enlarged_interval_report()
    ids = {o["obligation_id"]: o["status"] for o in report["obligations"]}
    order = [o["obligation_id"] for o in report["obligations"]]
    assert ids["coefficient_smooth_on_source_slot"] == "PASS"
    assert ids["coefficient_continuous_on_enlarged_interval"] == "DERIVED_READY_TO_FORMALIZE"
    assert ids["modal_primary_on_enlarged_interval"] == "READY_ON_CONTINUITY_GATE"
    assert ids["agreement_with_native_primary"] == "READY_ON_MODAL_CONSTRUCTION_GATE"
    assert order.index("modal_primary_on_enlarged_interval") < order.index("kinematics_on_enlarged_interval")
    assert ids["normal_nonzero_on_enlarged_interval"] == "DERIVED_READY_TO_FORMALIZE"
    assert ids["kinematics_on_enlarged_interval"] == "DERIVED_READY_TO_FORMALIZE"
    assert report["first_unresolved_after_source_reuse"]["obligation_id"] == "full_wave_residual_after_extension"


def test_source_geometric_frontier_allows_any_sample_below_two_but_not_two():
    frontier = extension_factor_frontier()
    rows = {row["rho"]: row for row in frontier["rows"]}
    assert rows[1.0]["inside_source_slot"] is True
    assert rows[1.5]["inside_source_slot"] is True
    assert rows[1.99]["inside_source_slot"] is True
    assert rows[2.0]["inside_source_slot"] is False
    assert frontier["source_geometric_supremum_factor"] == 2.0
    assert frontier["supremum_attained"] is False


def test_report_keeps_formalization_claim_boundary_closed():
    report = enlarged_interval_report()
    assert "does not claim" in report["claim_boundary"]
    assert "Lean-checked" in report["claim_boundary"]
