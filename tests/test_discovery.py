from blowup_lab.discovery import local_campaign


def test_reference_candidate_exists():
    cands = local_campaign()
    assert len(cands) == 81
    assert any(c.radial_balance and c.axial_adv_balance and c.axial_diff_subleading and c.finite_dominant_energy for c in cands)


def test_power_count_filter_is_selective():
    cands = local_campaign()
    dispositions = {c.disposition for c in cands}
    assert "PROMOTE" in dispositions
    assert "KILL" in dispositions
