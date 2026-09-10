from blowup_lab.cutoff_residual_atlas import (
    CutoffScenario,
    cutoff_residual_atlas,
    evaluate_scenario,
)


def test_general_excluded_slot_error_has_two_channels():
    report = evaluate_scenario(CutoffScenario("general"))
    assert report["atom_count"] == 2
    ids = {atom["atom_id"] for atom in report["atoms"]}
    assert ids == {"cutoff.fast_derivative", "cutoff.uncovered_source"}


def test_primary_source_zero_has_only_cutoff_derivative_channel():
    report = evaluate_scenario(CutoffScenario("primary", source_zero=True))
    assert report["atom_count"] == 1
    assert report["atoms"][0]["atom_id"] == "cutoff.fast_derivative"


def test_uncut_localization_identity_vanishes_but_keeps_global_caveat():
    report = evaluate_scenario(CutoffScenario("uncut", cutoff_identically_one=True))
    assert report["atom_count"] == 0
    assert report["local_result"] == "excludedSlotError = 0"
    assert "does not establish global PDE residual closure" in report["caveat"]


def test_product_cutoff_splits_clock_and_slot_commutators():
    report = evaluate_scenario(CutoffScenario("product", product_cutoff=True))
    ids = {atom["atom_id"] for atom in report["atoms"]}
    assert "cutoff.clock_derivative" in ids
    assert "cutoff.slot_derivative" in ids
    assert "cutoff.product_uncovered_source" in ids


def test_primary_product_cutoff_removes_source_exposure_channel():
    report = evaluate_scenario(CutoffScenario("product_primary", source_zero=True, product_cutoff=True))
    ids = {atom["atom_id"] for atom in report["atoms"]}
    assert ids == {"cutoff.clock_derivative", "cutoff.slot_derivative"}


def test_atlas_refuses_global_unforced_claim():
    atlas = cutoff_residual_atlas()
    assert atlas["hard_findings"]["uncut_principal_localization_error_is_zero_if_global_solve_holds"] is True
    assert atlas["hard_findings"]["global_solve_for_uncut_hierarchy_established"] is False
    assert atlas["hard_findings"]["full_unforced_navier_stokes_residual_closed"] is False
