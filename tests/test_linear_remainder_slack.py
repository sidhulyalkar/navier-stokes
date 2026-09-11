from blowup_lab.linear_remainder_slack import (
    actual_parameter_ledger,
    cutoff_channel_reclassification,
    improved_remainder_candidate,
    symbolic_slack_atoms,
)


def test_actual_candidate_gain_is_nine_tenths():
    ledger = actual_parameter_ledger()
    assert ledger["source_common_gain"] == "7/10"
    assert ledger["candidate_common_gain"] == "9/10"
    assert ledger["candidate_gain_improvement"] == "1/5"
    assert ledger["candidate_gain_improvement_equals_2kappa"] is True


def test_frontier_atoms_are_exactly_pressure_viscous_and_principal():
    ledger = actual_parameter_ledger()
    assert ledger["frontier_atoms"] == [
        "remainder.pressure_gradient",
        "remainder.viscous_part",
        "constructed_good.curl_principal",
    ]


def test_source_helper_is_not_mislabeled_as_sharp():
    atoms = {atom.atom_id: atom for atom in symbolic_slack_atoms()}
    assert atoms["remainder.phase_defect"].strongest_visible_gain == "alpha + 1/2"
    assert atoms["remainder.base_derivative"].strongest_visible_gain == "alpha + 1"
    assert atoms["remainder.pressure_gradient"].strongest_visible_gain == "alpha + 1/2 - kappa"


def test_cutoff_channel_is_demoted_only_as_rate_bottleneck():
    cutoff = cutoff_channel_reclassification()
    assert cutoff["decision"] == "DEMOTE_AS_RATE_BOTTLENECK__KEEP_AS_EXACT_FORCE_ABLATION"
    assert "does not prove removing the cutoff is irrelevant" in cutoff["claim_boundary"]


def test_formal_candidate_is_fail_closed_until_lean_passes():
    report = improved_remainder_candidate()
    assert report["formal_candidate"]["validation"] == "PENDING_SOURCE_LOCKED_LEAN_CI"
    assert report["hard_findings"]["candidate_formally_validated"] is False
    assert report["hard_findings"]["downstream_iteration_gain_improved"] is False
    assert report["hard_findings"]["actual_force_norm_reduced"] is False
