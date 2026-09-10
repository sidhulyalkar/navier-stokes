from blowup_lab.local_relaxations import (
    matching_cone_relaxation,
    matching_cone_shape_axis_h_upper,
    natural_entrance_base_source_h_upper,
    natural_entrance_relaxation,
    relaxation_report,
)


def test_natural_entrance_local_bound_is_wider_than_global_window():
    bound = natural_entrance_base_source_h_upper()
    assert bound > 1e-3
    assert bound < 1e-2


def test_worst_case_bound_preserves_conservative_margin():
    j = 1e-3
    h = natural_entrance_base_source_h_upper(j_upper=j, target=2.9) * 0.99
    lower = 3 - j - h * (17 + 2 * j)
    assert lower > 2.9


def test_matching_cone_local_bound_is_wider_but_tighter_than_entrance():
    cone = matching_cone_shape_axis_h_upper()
    entrance = natural_entrance_base_source_h_upper()
    assert cone > 1e-3
    assert cone < entrance
    assert 0.0035 < cone < 0.0036


def test_matching_cone_bound_preserves_shape_margin():
    j = 1e-3
    ell = 11 / 20
    h = matching_cone_shape_axis_h_upper(j_upper=j, ell_lower=ell, target=8 / 5) * 0.99
    lower = ell * (3 - j) - 2 * j - h * (8 * ell + 9 + 2 * j)
    assert lower > 8 / 5


def test_report_identifies_current_local_bottleneck():
    report = relaxation_report()
    assert report["current_local_bottleneck"]["theorem"] == "NavierStokes.MatchingConeBounds.shape_axis_lower"
    assert report["current_local_bottleneck"]["expansion_factor_over_global"] > 3


def test_claim_boundaries_stay_local():
    entrance = natural_entrance_relaxation()
    cone = matching_cone_relaxation()
    assert entrance.expansion_factor > 5
    assert cone.expansion_factor > 3
    assert "does not establish" in entrance.claim_boundary.lower()
    assert "does not establish" in cone.claim_boundary.lower()
