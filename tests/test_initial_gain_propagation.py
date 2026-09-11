from blowup_lab.initial_gain_propagation import (
    initial_gain_report,
    propagation_gates,
    shifted_schedule_hypothesis,
)


def test_both_initialization_gates_accept_nine_tenths():
    gates = propagation_gates()
    assert [gate.gate_id for gate in gates] == [
        "zero_mean_self_transport",
        "initialized_mean_update",
    ]
    assert all(gate.passes for gate in gates)
    assert all(gate.actual_rhs == gate.candidate_gamma for gate in gates)


def test_shifted_schedule_is_only_conditional():
    schedule = shifted_schedule_hypothesis()
    assert schedule["source_index_with_same_sigma"] == 2
    assert schedule["decision"] == "PROMOTE_CONDITIONALLY"
    assert "does not imply" in schedule["not_yet_proved"]


def test_report_does_not_claim_end_to_end_improvement():
    report = initial_gain_report()
    assert report["all_source_inequality_gates_pass"] is True
    assert report["formal_validation"] == "PENDING_SOURCE_LOCKED_LEAN_CI"
    hard = report["hard_findings"]
    assert hard["actual_primary_linear_gain_9_10_formalized"] is False
    assert hard["actual_initial_residual_gain_9_10_end_to_end_formalized"] is False
    assert hard["initial_cycle_invariant_sigma_2_5_proved"] is False
    assert hard["correction_cycles_skipped"] == 0
