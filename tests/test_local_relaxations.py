from blowup_lab.local_relaxations import natural_entrance_base_source_h_upper, natural_entrance_relaxation


def test_natural_entrance_local_bound_is_wider_than_global_window():
    bound = natural_entrance_base_source_h_upper()
    assert bound > 1e-3
    assert bound < 1e-2


def test_worst_case_bound_preserves_conservative_margin():
    j = 1e-3
    h = natural_entrance_base_source_h_upper(j_upper=j, target=2.9) * 0.99
    lower = 3 - j - h * (17 + 2 * j)
    assert lower > 2.9


def test_report_claim_boundary_stays_local():
    r = natural_entrance_relaxation()
    assert r.expansion_factor > 5
    assert "does not establish" in r.claim_boundary.lower()
