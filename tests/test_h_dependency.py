from blowup_lab.h_dependency import descendants, graph_report, relaxation_priority, source_seed_nodes, validate_graph


def test_seed_graph_valid_and_root_reaches_consumers():
    nodes = source_seed_nodes()
    validate_graph(nodes)
    reach = descendants(nodes, "small_h_root")
    assert "matching_cone_numeric" in reach
    assert "constructed_base_half" in reach


def test_numeric_consumers_rank_before_weak_plumbing():
    ranked = relaxation_priority(source_seed_nodes())
    kinds = [x["kind"] for x in ranked]
    assert kinds[0] == "NUMERIC"
    assert kinds[-1] == "DERIVED_WEAK"


def test_report_is_fail_closed_about_sharpness():
    report = graph_report()
    assert report["counts"]["NUMERIC"] >= 4
    assert "does not yet prove" in report["claim_boundary"]
