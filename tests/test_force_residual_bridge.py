from blowup_lab.force_residual_bridge import force_residual_bridge_report


def test_bridge_keeps_both_source_backed_frontiers():
    report = force_residual_bridge_report()
    assert report["global_force_frontier"]["node"] == "incoming.mixed_diagonal_residual"
    assert report["normalized_residual_frontier"]["hard_findings"][
        "harmonic_native_bottleneck_identified"
    ] is True


def test_aggregate_rate_bridge_is_source_backed():
    bridge = force_residual_bridge_report()["aggregate_rate_bridge"]
    assert bridge["status"] == "SOURCE_EXACT"
    assert bridge["path"][0] == "ActualCycleResidualBounds.finite_residual_rates"
    assert bridge["path"][-1] == "JointResidualLimits.VanishingJointJets"
    assert "all-orders flat" in bridge["interpretation"]


def test_termwise_bridge_remains_explicitly_open():
    bridge = force_residual_bridge_report()["termwise_attribution_bridge"]
    assert bridge["status"] == "OPEN"
    assert "physical-chart conversion" in bridge["reason"]
    assert len(bridge["required_obligations"]) == 5


def test_sigma_gain_reaches_diagonal_assembly_but_not_force_norm_automatically():
    sigma = force_residual_bridge_report()["sigma_relevance"]
    assert sigma["native_bottleneck"] == "representation.harmonic_sum"
    assert sigma["candidate_delta_for_sigma_plus_one_fifth"] == "h/5"
    assert sigma["aggregate_diagonal_relevance"] == "SOURCE_BACKED"
    assert sigma["endpoint_flatness_effect"] == "NO_STRICT_IMPROVEMENT_FROM_EXPONENT_ALONE"
    assert "the final forcing norm is smaller" in sigma["not_implied"]


def test_bridge_claims_remain_fail_closed():
    hard = force_residual_bridge_report()["hard_findings"]
    assert hard["global_force_ancestry_extracted"] is True
    assert hard["normalized_residual_decomposition_extracted"] is True
    assert hard["aggregate_rate_bridge_to_mixed_diagonal_flatness_extracted"] is True
    assert hard["exact_termwise_bridge_to_final_force_extracted"] is False
    assert hard["sigma_shift_proven_to_reduce_terminal_force"] is False
    assert hard["actual_force_norm_reduced"] is False
    assert hard["unforced_navier_stokes_blowup_proved"] is False
