from blowup_lab.final_force_attribution import (
    Evidence,
    ForceClass,
    final_force_attribution,
    final_force_edges,
    final_force_nodes,
    source_lock,
    terminal_region_result,
)


def test_force_attribution_is_pinned_to_reproducibility_source():
    lock = source_lock()
    assert lock["repository"] == "openai/NavierStokesAndEuler"
    assert lock["commit"] == "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


def test_final_force_equals_activated_residual_before_blowup():
    edge = next(
        edge
        for edge in final_force_edges()
        if edge.parent == "force.final" and edge.child == "force.activated_residual"
    )
    assert edge.evidence is Evidence.SOURCE_EXACT
    assert edge.relation == "exact equality"
    assert edge.scope == "0 <= t < 1"


def test_activation_residual_has_exactly_three_source_exact_channels():
    activation_edges = [
        edge for edge in final_force_edges() if edge.parent == "force.activated_residual"
    ]
    assert len(activation_edges) == 3
    assert {edge.child for edge in activation_edges} == {
        "activation.scaled_incoming_residual",
        "activation.switch_derivative",
        "activation.advection_defect",
    }
    assert all(edge.evidence is Evidence.SOURCE_EXACT for edge in activation_edges)


def test_activation_specific_force_disappears_in_terminal_quarter():
    terminal = terminal_region_result()
    assert terminal["region"] == "3/4 < t < 1"
    assert terminal["activated_residual_equals_incoming_residual"] is True
    assert terminal["activation_specific_force_atoms_present"] is False


def test_spatial_localization_edges_remain_local_not_global():
    edges = final_force_edges()
    periodic_to_cut = next(
        edge
        for edge in edges
        if edge.parent == "incoming.periodic_residual" and edge.child == "incoming.cut_residual"
    )
    cut_to_original = next(
        edge
        for edge in edges
        if edge.parent == "incoming.cut_residual" and edge.child == "incoming.original_residual"
    )
    assert periodic_to_cut.evidence is Evidence.SOURCE_LOCAL_EQUALITY
    assert cut_to_original.evidence is Evidence.SOURCE_LOCAL_EQUALITY
    assert "not a global equality" in periodic_to_cut.warning
    assert "Outside the plateau" in cut_to_original.warning


def test_mixed_diagonal_residual_is_exactly_linked_to_original_residual():
    edge = next(
        edge
        for edge in final_force_edges()
        if edge.parent == "incoming.original_residual"
        and edge.child == "incoming.mixed_diagonal_residual"
    )
    assert edge.evidence is Evidence.SOURCE_EXACT
    assert "definitionally equal" in edge.relation


def test_borel_extension_is_not_classified_as_presingular_force_origin():
    node = next(node for node in final_force_nodes() if node.node_id == "extension.post_singular_borel")
    assert node.force_class is ForceClass.EXTENSION_ONLY
    assert "Do not attribute the pre-singular force" in node.warning


def test_attribution_remains_fail_closed():
    report = final_force_attribution()
    hard = report["hard_findings"]
    assert hard["mechanism_level_final_force_decomposition_complete"] is False
    assert hard["actual_force_norm_reduced"] is False
    assert hard["unforced_navier_stokes_blowup_proved"] is False
    assert report["next_extraction"]["stop_rule"].startswith("Unknown stage terms remain UNKNOWN")
