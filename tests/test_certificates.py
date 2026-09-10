import pytest

from blowup_lab.certificates import build_certificate_dag


def test_certificate_kind_dependency_resolves_to_prior_hash():
    dag = build_certificate_dag([
        ("source", {"x": 1}, ()),
        ("derived", {"y": 2}, ("source",)),
    ])
    source_id = dag["kind_index"]["source"]
    derived = next(node for node in dag["nodes"] if node["kind"] == "derived")
    assert derived["dependencies"] == (source_id,)


def test_certificate_unknown_dependency_still_fails_closed():
    with pytest.raises(ValueError):
        build_certificate_dag([("derived", {"y": 2}, ("missing",))])


def test_duplicate_kind_is_rejected():
    with pytest.raises(ValueError):
        build_certificate_dag([
            ("same", {"x": 1}, ()),
            ("same", {"x": 2}, ()),
        ])
