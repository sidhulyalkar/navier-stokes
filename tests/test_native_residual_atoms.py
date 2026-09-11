from blowup_lab.native_residual_atoms import (
    exact_native_atoms,
    rate_hierarchy,
    regional_residual_structure,
)


def test_exact_native_residual_has_five_atoms():
    atoms = exact_native_atoms()
    assert [atom.atom_id for atom in atoms] == [
        "native.harmonic_source_sum",
        "native.mean_good",
        "native.excluded_base",
        "native.excluded_gaussian",
        "native.excluded_alias",
    ]


def test_harmonic_source_sum_is_only_fixed_common_gain_candidate():
    atoms = {atom.atom_id: atom for atom in exact_native_atoms()}
    assert atoms["native.harmonic_source_sum"].proved_native_gain == "h * (1/2 + sigma)"
    assert atoms["native.harmonic_source_sum"].gain_status == "FIXED_GAIN_IN_CURRENT_PROOF"
    assert atoms["native.mean_good"].proved_native_gain == "h * (1 + sigma)"
    assert atoms["native.mean_good"].gain_status == "STRONGER_THAN_COMMON_GAIN"


def test_excluded_error_families_keep_all_power_status():
    atoms = {atom.atom_id: atom for atom in exact_native_atoms()}
    assert atoms["native.excluded_base"].gain_status == "ALL_POWER_FAMILY"
    assert atoms["native.excluded_gaussian"].gain_status == "FLAT_ALL_POWER_FAMILY"
    assert atoms["native.excluded_alias"].gain_status == "FLAT_ALL_POWER_FAMILY"


def test_active_exterior_structure_is_regional_not_additive():
    structure = regional_residual_structure()
    assert structure["gluing"]["additive_force_identity"] is False
    assert "proof-by-region" in structure["gluing"]["warning"]


def test_rate_hierarchy_does_not_claim_sharpness_or_norm_ranking():
    report = rate_hierarchy()
    hard = report["hard_findings"]
    assert report["current_weakest_proved_gain"] == "native.harmonic_source_sum"
    assert hard["harmonic_source_sum_is_weakest_proved_native_gain"] is True
    assert hard["harmonic_source_sum_bound_proved_sharp"] is False
    assert hard["mechanism_level_force_norm_ranking_complete"] is False
    assert report["next_target"]["declaration"] == "HarmonicResidual.residualBlock"
