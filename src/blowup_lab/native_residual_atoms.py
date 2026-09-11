from __future__ import annotations

from dataclasses import asdict, dataclass


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class NativeResidualAtom:
    atom_id: str
    expression: str
    identity_source: str
    bound_source: str
    proved_native_gain: str
    gain_status: str
    role: str
    warning: str = ""

    def to_dict(self) -> dict:
        return asdict(self)


def exact_native_atoms() -> list[NativeResidualAtom]:
    """Exact additive atoms of `LiftedMeanResidual.fullResidual` in the active chart.

    The five-atom expansion combines the exact `fullResidual_decomposition`
    theorem with `CorrectionState.ExcludedErrors.total = base + gaussian +
    aliasError`. Bounds below describe what the pinned actual-cycle proof can
    prove for each atom; they are not lower bounds and do not establish
    sharpness.
    """

    return [
        NativeResidualAtom(
            atom_id="native.harmonic_source_sum",
            expression="sum_l (ActualCycleResidualBounds.source(x,l).oscillation)",
            identity_source="ActualCycleResidualBounds.Invariant.fullResidual_decomposition",
            bound_source="ActualCycleResidualBounds.Invariant.source_sum_native",
            proved_native_gain="h * (1/2 + sigma)",
            gain_status="FIXED_GAIN_IN_CURRENT_PROOF",
            role=(
                "sum of harmonic residual blocks built from the current wave block, Gaussian coefficients, "
                "and alias coefficients"
            ),
            warning=(
                "This is the weakest explicit native gain currently proved among the five atoms. That makes it a "
                "priority candidate, not a proof that the bound is sharp or that this atom dominates any force norm."
            ),
        ),
        NativeResidualAtom(
            atom_id="native.mean_good",
            expression="state.meanGoodResidual(context)",
            identity_source="ActualCycleResidualBounds.Invariant.fullResidual_decomposition",
            bound_source="ActualCycleResidualBounds.Invariant.mean_native",
            proved_native_gain="h * (1 + sigma)",
            gain_status="STRONGER_THAN_COMMON_GAIN",
            role="mean residual after subtracting the actual angular mean of explicitly stored excluded errors",
            warning=(
                "native_residual weakens this stronger rate to h*(1/2+sigma) only so all atoms can be added at a "
                "common exponent."
            ),
        ),
        NativeResidualAtom(
            atom_id="native.excluded_base",
            expression="state.errors.base",
            identity_source="CorrectionState.ExcludedErrors.total",
            bound_source="ActualCycleResidualBounds.baseError_native",
            proved_native_gain="h * alpha for arbitrary requested alpha in baseError_native",
            gain_status="ALL_POWER_FAMILY",
            role="fixed base-flat residual error retained explicitly in the correction state",
            warning="The all-power estimate does not mean the field is identically zero.",
        ),
        NativeResidualAtom(
            atom_id="native.excluded_gaussian",
            expression="state.errors.gaussian",
            identity_source="CorrectionState.ExcludedErrors.total",
            bound_source="ActualCycleResidualBounds.Invariant.gaussian_field_native",
            proved_native_gain="h * alpha for arbitrary alpha supplied to gaussian_field_native",
            gain_status="FLAT_ALL_POWER_FAMILY",
            role="Gaussian excluded error reconstructed from nonzero Fourier modes",
            warning="Flatness/super-polynomial control is not exact cancellation.",
        ),
        NativeResidualAtom(
            atom_id="native.excluded_alias",
            expression="state.errors.aliasError",
            identity_source="CorrectionState.ExcludedErrors.total",
            bound_source="ActualCycleResidualBounds.Invariant.axis_native + alias_eq_lift",
            proved_native_gain="h * alpha for arbitrary alpha supplied through axis_native",
            gain_status="FLAT_ALL_POWER_FAMILY",
            role="accumulated axisymmetric alias error retained in the residual grouping",
            warning="Its cancellation with mean structure is source-backed separately; do not silently drop it.",
        ),
    ]


def regional_residual_structure() -> dict:
    return {
        "active_region": {
            "identity": (
                "fullResidual = harmonic_source_sum + meanGoodResidual + excluded_base + "
                "excluded_gaussian + excluded_alias"
            ),
            "identity_sources": [
                "ActualCycleResidualBounds.Invariant.fullResidual_decomposition",
                "CorrectionState.ExcludedErrors.total",
            ],
            "common_rate_used_by_native_residual": "h * (1/2 + sigma)",
        },
        "exterior_region": {
            "mechanism": "actual field agrees locally with FinalSlowBase velocity/pressure outside active set",
            "source": "ActualCycleResidualBounds.base_residual_germ",
            "bound": "ActualCycleResidualBounds.base_exterior_jetRate",
            "rate_status": "all requested powers inherited from GlobalBaseError.error_joint_jetRate",
        },
        "gluing": {
            "source": "ActualCycleResidualBounds.selected_residual_jetRate",
            "method": (
                "regional case split: active points use selected_residual_jet_bound; exterior points use local "
                "eventual equality to the base residual; constants combine as B+C"
            ),
            "additive_force_identity": False,
            "warning": (
                "The active/exterior split is a proof-by-region decomposition, not a statement that the physical "
                "force is globally the sum of an active force field and an exterior force field."
            ),
        },
    }


def rate_hierarchy() -> dict:
    atoms = exact_native_atoms()
    return {
        "schema": "native-residual-atoms-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "exact_additive_atoms": [atom.to_dict() for atom in atoms],
        "regional_structure": regional_residual_structure(),
        "current_weakest_proved_gain": "native.harmonic_source_sum",
        "why": (
            "source_sum_native is proved at h*(1/2+sigma). mean_native is stronger at h*(1+sigma), while the "
            "base, Gaussian, and alias families admit arbitrary requested native powers before being weakened to "
            "the common residual gain."
        ),
        "claim_boundary": (
            "Weakest proved gain is not a sharpness theorem and does not by itself rank Lp force norms. It is an "
            "information-gain criterion for choosing the next source decomposition."
        ),
        "next_target": {
            "declaration": "HarmonicResidual.residualBlock",
            "question": (
                "Decompose the harmonic source-sum atom into principal solve, cutoff/localization, Gaussian, alias, "
                "transport, viscous, pressure, and interaction channels using exact source identities."
            ),
            "v56_bridge_test": (
                "Determine whether the slot/clock cutoff commutators studied in v5.6 are explicit descendants of "
                "this harmonic residualBlock source sum. Only then should no-cutoff pulse work remain top priority."
            ),
        },
        "hard_findings": {
            "native_full_residual_five_atom_identity_source_backed": True,
            "active_exterior_gluing_is_additive_force_identity": False,
            "harmonic_source_sum_is_weakest_proved_native_gain": True,
            "harmonic_source_sum_bound_proved_sharp": False,
            "mechanism_level_force_norm_ranking_complete": False,
        },
    }
