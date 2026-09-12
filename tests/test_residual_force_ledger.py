from fractions import Fraction

from blowup_lab.residual_force_ledger import (
    exact_residual_attribution_report,
    native_gain_ledger,
    physical_residual_atoms,
    representation_atoms,
    residual_identities,
    sigma_shift_gain,
)


def test_physical_residual_has_only_definition_level_atoms():
    atoms = physical_residual_atoms()
    assert [a.atom_id for a in atoms] == [
        "physical.differential",
        "physical.virtual",
        "physical.base_error",
    ]
    assert all(a.physical_force_atom for a in atoms)


def test_gaussian_and_alias_are_not_independent_force_atoms():
    by_id = {a.atom_id: a for a in representation_atoms()}
    for atom_id in ("bookkeeping.gaussian", "bookkeeping.alias"):
        atom = by_id[atom_id]
        assert not atom.physical_force_atom
        assert not atom.independently_ablatable
        assert atom.bookkeeping_pair is not None


def test_exact_identities_keep_physical_and_representation_layers_distinct():
    by_id = {i.identity_id: i for i in residual_identities()}
    physical = by_id["physical.definition"]
    reconstructed = by_id["representation.harmonic_reconstruction"]

    assert physical.exact and reconstructed.exact
    assert "bookkeeping.gaussian" not in physical.rhs
    assert "bookkeeping.alias" not in physical.rhs
    assert "bookkeeping.gaussian" in reconstructed.rhs
    assert "bookkeeping.alias" in reconstructed.rhs


def test_harmonic_sum_is_unique_native_bottleneck_candidate():
    ledger = native_gain_ledger()
    candidates = [entry.channel_id for entry in ledger if entry.bottleneck_candidate]
    assert candidates == ["representation.harmonic_sum"]

    mean = next(entry for entry in ledger if entry.channel_id == "representation.mean_good")
    assert mean.relative_to_harmonic == "+h/2"

    all_power = {entry.channel_id for entry in ledger if entry.all_power}
    assert all_power == {
        "bookkeeping.base_error",
        "bookkeeping.gaussian",
        "bookkeeping.alias",
    }


def test_sigma_shift_is_fail_closed():
    shift = sigma_shift_gain(Fraction(1, 5))
    assert shift["delta_sigma"] == "1/5"
    assert shift["native_harmonic_gain_delta"] == "h*1/5"
    assert "that correction cycles can be deleted" in shift["not_proved"]
    assert "that the final global force norm is smaller" in shift["not_proved"]


def test_report_never_promotes_force_reduction_or_unforced_blowup():
    report = exact_residual_attribution_report()
    hard = report["hard_findings"]

    assert hard["physical_definition_decomposition_extracted"]
    assert hard["harmonic_reconstruction_extracted"]
    assert hard["harmonic_native_bottleneck_identified"]
    assert not hard["gaussian_is_independent_physical_force_atom"]
    assert not hard["alias_is_independent_physical_force_atom"]
    assert not hard["force_norm_reduced"]
    assert not hard["correction_cycles_deleted"]
    assert not hard["unforced_navier_stokes_blowup_proved"]
