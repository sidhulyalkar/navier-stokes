from blowup_lab.stage_residual_attribution import (
    SOURCE_COMMIT,
    current_attribution_frontier,
    finite_residual_producer_chain,
)


def test_stage_residual_attribution_keeps_source_lock():
    assert SOURCE_COMMIT == "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


def test_finite_residual_producer_chain_reaches_exact_reconstruction():
    chain = finite_residual_producer_chain()
    assert [step.step_id for step in chain] == [
        "consumer.stage_estimates",
        "adapter.actual_stage_estimates",
        "producer.cycle_residual_bounds",
        "ledger.native_residual",
        "identity.harmonic_reconstruction",
    ]
    assert chain[-1].source_declaration == (
        "ActualCycleResidualBounds.Invariant.fullResidual_decomposition"
    )


def test_aggregate_interfaces_remain_distinct_from_exact_proof_decomposition():
    chain = finite_residual_producer_chain()
    assert chain[0].additive_decomposition_available is False
    assert chain[1].additive_decomposition_available is False
    assert chain[2].additive_decomposition_available is True
    assert chain[3].additive_decomposition_available is True
    assert chain[4].additive_decomposition_available is True


def test_frontier_embeds_exact_residual_ledger():
    report = current_attribution_frontier()
    exact = report["exact_residual_ledger"]
    hard = exact["hard_findings"]

    assert hard["physical_definition_decomposition_extracted"] is True
    assert hard["harmonic_reconstruction_extracted"] is True
    assert hard["gaussian_is_independent_physical_force_atom"] is False
    assert hard["alias_is_independent_physical_force_atom"] is False


def test_stage_frontier_is_advanced_but_fail_closed():
    hard = current_attribution_frontier()["hard_findings"]
    assert hard["finite_residual_rate_producer_located"] is True
    assert hard["producer_termwise_decomposition_extracted"] is True
    assert hard["harmonic_native_bottleneck_identified"] is True
    assert hard["force_priority_numerically_ranked"] is False
    assert hard["force_norm_reduced"] is False
