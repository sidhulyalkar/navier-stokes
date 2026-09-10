from blowup_lab.localization_obstruction import localization_obstruction_report


def test_cutoff_commutator_is_explicit():
    report = localization_obstruction_report()
    identity = report["commutator"]["residual_identity"]
    assert "chi'(v) x(v)" in identity


def test_exact_compact_homogeneous_pulse_lineage_is_killed():
    report = localization_obstruction_report()
    assert report["decision"]["exact_temporal_compactness_plus_homogeneous_nonzero_pulse"] == "KILL"


def test_global_tail_lineage_remains_research_target():
    report = localization_obstruction_report()
    assert report["decision"]["globally_present_gaussian_small_tails"] == "PROMOTE_FOR_ANALYSIS"
    claims = report["uniqueness_obstruction"]["not_claimed"]
    assert any("full Navier-Stokes forcing" in claim for claim in claims)
