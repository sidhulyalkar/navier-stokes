from blowup_lab.force_residual_bridge import force_residual_bridge_report


def test_bridge_keeps_both_source_backed_frontiers():
    report = force_residual_bridge_report()
    assert report["global_force_frontier"]["node"] == "incoming.mixed_diagonal_residual"
    assert report["normalized_residual_frontier"]["hard_findings"][
        "harmonic_native_bottleneck_identified"
    ] is True


def test_bridge_is_explicitly_open_not_invented():
    bridge = force_residual_bridge_report()["bridge"]
    assert bridge["status"] == "OPEN"
    assert bridge["from"] == "incoming.mixed_diagonal_residual"
    assert "physical-chart conversion" in bridge["reason"]
    assert len(bridge["required_obligations"]) == 5


def test_sigma_gain_is_only_conditionally_connected_to_terminal_force():
    sigma = force_residual_bridge_report()["sigma_relevance"]
    assert sigma["native_bottleneck"] == "representation.harmonic_sum"
    assert sigma["candidate_delta_for_sigma_plus_one_fifth"] == "h/5"
    assert sigma["terminal_force_relevance"] == "CONDITIONAL"
    assert len(sigma["conditions"]) == 4


def test_bridge_claims_remain_fail_closed():
    hard = force_residual_bridge_report()["hard_findings"]
    assert hard["global_force_ancestry_extracted"] is True
    assert hard["normalized_residual_decomposition_extracted"] is True
    assert hard["exact_bridge_from_normalized_atoms_to_final_diagonal_force_extracted"] is False
    assert hard["sigma_shift_proven_to_reduce_terminal_force"] is False
    assert hard["actual_force_norm_reduced"] is False
    assert hard["unforced_navier_stokes_blowup_proved"] is False
