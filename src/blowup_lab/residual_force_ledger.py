from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction


SOURCE_REPOSITORY = "openai/NavierStokesAndEuler"
SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class ResidualAtom:
    atom_id: str
    layer: str
    source_file: str
    source_declaration: str
    exact_role: str
    physical_force_atom: bool
    independently_ablatable: bool
    bookkeeping_pair: str | None = None

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass(frozen=True)
class ResidualIdentity:
    identity_id: str
    source_file: str
    source_declaration: str
    lhs: str
    rhs: tuple[str, ...]
    exact: bool
    interpretation: str

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass(frozen=True)
class NativeGain:
    channel_id: str
    source_file: str
    source_declaration: str
    gain: str
    relative_to_harmonic: str
    all_power: bool
    bottleneck_candidate: bool

    def to_dict(self) -> dict:
        return asdict(self)


def physical_residual_atoms() -> list[ResidualAtom]:
    """Definition-level additive atoms in the normalized physical residual.

    These atoms come directly from `HarmonicResidual.stateFullResidual`.  This
    is intentionally narrower than the harmonic extraction bookkeeping.
    """

    return [
        ResidualAtom(
            atom_id="physical.differential",
            layer="PHYSICAL",
            source_file="NavierStokes/HarmonicResidual.lean",
            source_declaration="HarmonicResidual.stateFullResidual",
            exact_role=(
                "Real part of the literal nonlinear differential residual: the linearized "
                "Navier-Stokes residual plus self-transport of the state perturbation."
            ),
            physical_force_atom=True,
            independently_ablatable=False,
        ),
        ResidualAtom(
            atom_id="physical.virtual",
            layer="PHYSICAL",
            source_file="NavierStokes/HarmonicResidual.lean",
            source_declaration="HarmonicResidual.contextVirtual",
            exact_role=(
                "Virtual-stress divergence contribution [0, -radialDiv(2, virtualTheta), "
                "-radialDiv(1, virtualAxial)]."
            ),
            physical_force_atom=True,
            independently_ablatable=False,
        ),
        ResidualAtom(
            atom_id="physical.base_error",
            layer="PHYSICAL",
            source_file="NavierStokes/HarmonicResidual.lean",
            source_declaration="HarmonicResidual.stateFullResidual",
            exact_role="Fixed base-error field added directly to the normalized residual.",
            physical_force_atom=True,
            independently_ablatable=False,
        ),
    ]


def representation_atoms() -> list[ResidualAtom]:
    """Atoms in the exact harmonic reconstruction of the same residual.

    Gaussian and alias terms are *not* independent physical-force atoms. They
    participate in paired subtraction/restoration bookkeeping during harmonic
    extraction, so an ablation that changes only one side would break the exact
    reconstruction identity.
    """

    return [
        ResidualAtom(
            atom_id="representation.harmonic_sum",
            layer="REPRESENTATION",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.Invariant.fullResidual_decomposition",
            exact_role="Finite sum of nonconstant per-label harmonic residual blocks.",
            physical_force_atom=False,
            independently_ablatable=False,
        ),
        ResidualAtom(
            atom_id="representation.mean_good",
            layer="REPRESENTATION",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.Invariant.fullResidual_decomposition",
            exact_role="Selected angular-mean residual after the harmonic extraction.",
            physical_force_atom=False,
            independently_ablatable=False,
        ),
        ResidualAtom(
            atom_id="bookkeeping.base_error",
            layer="BOOKKEEPING",
            source_file="NavierStokes/CorrectionState.lean",
            source_declaration="CorrectionState.ExcludedErrors.total",
            exact_role="Base component of the stored excluded-error reconstruction.",
            physical_force_atom=True,
            independently_ablatable=False,
        ),
        ResidualAtom(
            atom_id="bookkeeping.gaussian",
            layer="BOOKKEEPING",
            source_file="NavierStokes/HarmonicResidual.lean",
            source_declaration="HarmonicResidual.LabelData.residualCoefficients",
            exact_role=(
                "Gaussian coefficient is subtracted inside each harmonic residual block and "
                "restored through ExcludedErrors.total."
            ),
            physical_force_atom=False,
            independently_ablatable=False,
            bookkeeping_pair="harmonic-subtraction/restored-gaussian-error",
        ),
        ResidualAtom(
            atom_id="bookkeeping.alias",
            layer="BOOKKEEPING",
            source_file="NavierStokes/HarmonicResidual.lean",
            source_declaration="HarmonicResidual.LabelData.residualCoefficients",
            exact_role=(
                "Alias coefficient is subtracted inside each harmonic residual block and "
                "restored through ExcludedErrors.total / angular-mean cancellation."
            ),
            physical_force_atom=False,
            independently_ablatable=False,
            bookkeeping_pair="harmonic-subtraction/restored-alias-error",
        ),
    ]


def residual_identities() -> list[ResidualIdentity]:
    return [
        ResidualIdentity(
            identity_id="physical.definition",
            source_file="NavierStokes/HarmonicResidual.lean",
            source_declaration="HarmonicResidual.stateFullResidual",
            lhs="normalized physical residual",
            rhs=("physical.differential", "physical.virtual", "physical.base_error"),
            exact=True,
            interpretation=(
                "Definition-level physical decomposition. Gaussian and alias do not occur as "
                "independent summands here."
            ),
        ),
        ResidualIdentity(
            identity_id="representation.harmonic_reconstruction",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.Invariant.fullResidual_decomposition",
            lhs="same normalized physical residual",
            rhs=(
                "representation.harmonic_sum",
                "representation.mean_good",
                "bookkeeping.base_error",
                "bookkeeping.gaussian",
                "bookkeeping.alias",
            ),
            exact=True,
            interpretation=(
                "Exact local harmonic reconstruction. Gaussian and alias are coupled extraction "
                "bookkeeping and must not be ranked as standalone force mechanisms."
            ),
        ),
        ResidualIdentity(
            identity_id="bookkeeping.excluded_total",
            source_file="NavierStokes/CorrectionState.lean",
            source_declaration="CorrectionState.ExcludedErrors.total",
            lhs="excluded-error total",
            rhs=("bookkeeping.base_error", "bookkeeping.gaussian", "bookkeeping.alias"),
            exact=True,
            interpretation="Definition-level split of the stored excluded-error field.",
        ),
    ]


def native_gain_ledger() -> list[NativeGain]:
    """Native exponents visible before conversion to the physical chart.

    The values are symbolic because the theorem is parameterized by h and
    sigma.  `baseError_native`, `gaussianFlat`, and `axisFlat` can be requested
    at arbitrary finite powers before the proof weakens them to a common
    residual exponent.
    """

    return [
        NativeGain(
            channel_id="representation.harmonic_sum",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.Invariant.source_sum_native",
            gain="h*(1/2 + sigma)",
            relative_to_harmonic="0",
            all_power=False,
            bottleneck_candidate=True,
        ),
        NativeGain(
            channel_id="representation.mean_good",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.Invariant.mean_native",
            gain="h*(1 + sigma)",
            relative_to_harmonic="+h/2",
            all_power=False,
            bottleneck_candidate=False,
        ),
        NativeGain(
            channel_id="bookkeeping.base_error",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.baseError_native",
            gain="arbitrary h*alpha",
            relative_to_harmonic="arbitrarily stronger before weakening",
            all_power=True,
            bottleneck_candidate=False,
        ),
        NativeGain(
            channel_id="bookkeeping.gaussian",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="CycleAnalyticInvariant.gaussianFlat",
            gain="arbitrary finite power",
            relative_to_harmonic="arbitrarily stronger before weakening",
            all_power=True,
            bottleneck_candidate=False,
        ),
        NativeGain(
            channel_id="bookkeeping.alias",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="CycleAnalyticInvariant.axisFlat",
            gain="arbitrary finite power",
            relative_to_harmonic="arbitrarily stronger before weakening",
            all_power=True,
            bottleneck_candidate=False,
        ),
    ]


def sigma_shift_gain(delta_sigma: Fraction = Fraction(1, 5)) -> dict:
    """Symbolic consequence of raising sigma while keeping the chart loss fixed."""

    return {
        "delta_sigma": f"{delta_sigma.numerator}/{delta_sigma.denominator}",
        "native_harmonic_gain_delta": f"h*{delta_sigma.numerator}/{delta_sigma.denominator}",
        "physical_residual_rate_delta_if_same_state_requalifies": (
            f"h*{delta_sigma.numerator}/{delta_sigma.denominator}"
        ),
        "assumptions": [
            "the same literal cycle state is formally requalified at sigma + delta_sigma",
            "ResidualChartData.residual_jetRate is applied with the stronger invariant",
            "the physical loss term is unchanged",
        ],
        "not_proved": [
            "that correction cycles can be deleted",
            "that the final global force norm is smaller",
            "that an unforced Navier-Stokes singularity exists",
        ],
    }


def exact_residual_attribution_report() -> dict:
    return {
        "schema": "exact-residual-attribution-v2",
        "source_lock": {"repository": SOURCE_REPOSITORY, "commit": SOURCE_COMMIT},
        "physical_atoms": [atom.to_dict() for atom in physical_residual_atoms()],
        "representation_atoms": [atom.to_dict() for atom in representation_atoms()],
        "identities": [identity.to_dict() for identity in residual_identities()],
        "native_gain_ledger": [entry.to_dict() for entry in native_gain_ledger()],
        "sigma_shift_candidate": sigma_shift_gain(),
        "hard_findings": {
            "physical_definition_decomposition_extracted": True,
            "harmonic_reconstruction_extracted": True,
            "producer_termwise_decomposition_extracted": True,
            "harmonic_native_bottleneck_identified": True,
            "gaussian_is_independent_physical_force_atom": False,
            "alias_is_independent_physical_force_atom": False,
            "force_norm_reduced": False,
            "correction_cycles_deleted": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "next_frontier": (
            "Bind the exact harmonic residual blocks to their stage mechanisms and quantify which "
            "part of the harmonic source remains bottleneck after spatial localization, time "
            "activation, and physical-chart conversion."
        ),
    }
