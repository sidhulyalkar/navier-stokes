from blowup_lab.proof import unforced_obligations


def test_unforced_requires_exact_zero_residual():
    obs = {o.id: o for o in unforced_obligations()}
    assert "vanishes identically" in obs["U03"].statement


def test_obligation_graph_refs_exist():
    obs = unforced_obligations()
    ids = {o.id for o in obs}
    for o in obs:
        assert set(o.depends_on) <= ids
