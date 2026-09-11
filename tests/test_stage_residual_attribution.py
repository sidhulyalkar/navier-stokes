from blowup_lab.stage_residual_attribution import (
    SOURCE_COMMIT,
    current_attribution_frontier,
    finite_residual_producer_chain,
)


def test_stage_residual_attribution_keeps_source_lock():
    assert SOURCE_COMMIT == "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


def test_finite_residual_producer_chain_reaches_actual_cycle_bounds():
    chain = finite_residual_producer_chain()
    assert [step.step_id for step in chain] == [
        "consumer.stage_estimates",
        "adapter.actual_stage_estimates",
        "producer.cycle_residual_bounds",
    ]
    assert chain[-1].source_declaration == "ActualCycleResidualBounds.finite_residual_rates"


def test_no_layer_fakes_a_termwise_decomposition():
    chain = finite_residual_producer_chain()
    assert all(step.additive_decomposition_available is False for step in chain)
    assert "current attribution frontier" in chain[-1].warning


def test_import_dependencies_are_not_mislabeled_as_force_atoms():
    report = current_attribution_frontier()
    assert "GlobalBaseError" in report["known_dependencies_from_pinned_source"]
    assert "GaugeExcludedBounds" in report["known_dependencies_from_pinned_source"]
    assert "not an additive residual decomposition" in report["interpretation"]


def test_stage_frontier_remains_fail_closed():
    hard = current_attribution_frontier()["hard_findings"]
    assert hard["finite_residual_rate_producer_located"] is True
    assert hard["producer_termwise_decomposition_extracted"] is False
    assert hard["force_priority_numerically_ranked"] is False
