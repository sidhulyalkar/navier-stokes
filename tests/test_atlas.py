from blowup_lab.atlas import ResidualAtlas


def test_atlas_is_dag():
    a = ResidualAtlas()
    order = a.topological_order()
    assert len(order) == len(a.atoms)
    assert len(set(order)) == len(order)


def test_annular_stress_reaches_wave_realization():
    a = ResidualAtlas()
    assert "S7_COVARIANCE_REALIZATION" in a.downstream("S4_ANNULAR_STRESS")


def test_force_stage_present():
    a = ResidualAtlas()
    assert "S10_FORCE_RESIDUAL" in a.by_id
    assert a.by_id["S10_FORCE_RESIDUAL"].source.page == 118
