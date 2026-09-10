from __future__ import annotations

from dataclasses import asdict, dataclass


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class MechanismNode:
    name: str
    role: str
    source_file: str
    source_declarations: tuple[str, ...]
    status: str
    forcing_role: str
    consequence: str

    def to_dict(self) -> dict:
        return asdict(self)


def pulse_localization_audit() -> dict:
    """Source-backed separation of pulse amplification from pulse localization.

    This deliberately answers a narrower question than "can forcing be removed?".
    The pinned Lean source already constructs the primary slot pulse as a
    homogeneous ODE solution.  The unresolved forcing-ablation target is the
    localization/global-extension layer surrounding that solution.
    """

    nodes = (
        MechanismNode(
            name="reference_envelope",
            role="sets the growing/decaying scalar amplitude profile in one slot",
            source_file="NavierStokes/GaussianEnvelope.lean",
            source_declarations=(
                "GaussianEnvelope.referenceRate",
                "GaussianEnvelope.gaussian_envelope_bounds",
            ),
            status="SOURCE_FORMALIZED",
            forcing_role="NONE_IN_REFERENCE_AMPLITUDE_ODE",
            consequence="The reference amplitude has a source-backed Gaussian envelope around the slot midpoint.",
        ),
        MechanismNode(
            name="primary_seed",
            role="initial datum for the primary two-mode ODE at the slot entrance",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declarations=("PrimaryODE.primarySeed",),
            status="SOURCE_FORMALIZED",
            forcing_role="INITIAL_DATA",
            consequence="The growing primary mode is seeded by (P(a), 0), not by an in-slot source term.",
        ),
        MechanismNode(
            name="primary_homogeneous_solution",
            role="evolves the primary two-mode perturbation inside the slot",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declarations=(
                "PrimaryODE.primary",
                "PrimaryODE.homogeneous_forward_bound",
                "PrimaryODE.ambient_homogeneous_forward_bound",
            ),
            status="SOURCE_FORMALIZED",
            forcing_role="ZERO",
            consequence="Within its slot the canonical primary pulse is a homogeneous zero-forcing ODE solution.",
        ),
        MechanismNode(
            name="slot_cutoff",
            role="turns the homogeneous pulse into a compactly localized slot pulse",
            source_file="NavierStokes/GaussianTailFlat.lean",
            source_declarations=(
                "GaussianTailFlat.slotCutoff",
                "GaussianTailFlat.slotCutoff_deriv_support",
                "GaussianTailFlat.reference_envelope_off_plateau",
                "GaussianTailFlat.gaussian_beats_Q_power",
            ),
            status="SOURCE_FORMALIZED",
            forcing_role="GENERATES_CUTOFF_DERIVATIVE_ERRORS",
            consequence=(
                "Cutoff derivatives live where L/5 <= |v-L/2| <= L/3, exactly where the homogeneous envelope is Gaussian-small."
            ),
        ),
        MechanismNode(
            name="cutoff_pulse",
            role="physical pulse used by the construction",
            source_file="NavierStokes/PrimaryPulseBounds.lean",
            source_declarations=("PrimaryPulseBounds.cutoffPulse",),
            status="SOURCE_FORMALIZED",
            forcing_role="LOCALIZATION_LAYER",
            consequence="The physical pulse is slotCutoff times the homogeneous primary solution.",
        ),
        MechanismNode(
            name="global_no_cutoff_extension",
            role="hypothetical extension of each homogeneous primary beyond its assigned slot",
            source_file="",
            source_declarations=(),
            status="OPEN_REPLACEMENT",
            forcing_role="TARGET_FOR_ABLATION",
            consequence=(
                "No source-backed construction currently shows that the infinite pulse hierarchy can be extended globally without the slot/clock localization machinery."
            ),
        ),
        MechanismNode(
            name="all_pulses_from_global_initial_data",
            role="hypothetical single smooth initial datum containing every future pulse seed",
            source_file="",
            source_declarations=(),
            status="OPEN_REPLACEMENT",
            forcing_role="TARGET_FOR_ABLATION",
            consequence=(
                "Even if individual entry seeds are Gaussian-small, simultaneous smooth/Gevrey summability, nonlinear compatibility, divergence constraints, and exact residual closure remain open."
            ),
        ),
    )

    return {
        "schema": "pulse-localization-audit-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "nodes": [node.to_dict() for node in nodes],
        "hard_findings": {
            "within_slot_primary_is_homogeneous": True,
            "within_slot_primary_uses_zero_forcing": True,
            "slot_cutoff_tail_region_is_source_backed": True,
            "gaussian_tail_beats_every_fixed_Q_power": True,
            "global_no_cutoff_extension_constructed": False,
            "all_pulses_encoded_in_one_global_initial_datum": False,
            "unforced_navier_stokes_residual_closed": False,
        },
        "research_pivot": {
            "obsolete_question": "Can the primary pulse be generated without forcing inside its slot?",
            "answer": "Yes for the canonical primary ODE: the pinned source already does this with a nonzero entry seed and zero in-slot forcing.",
            "next_question": (
                "Can the localized homogeneous pulse hierarchy be replaced by globally defined homogeneous perturbations, initialized from one smooth datum, while preserving all support, interaction, and residual estimates?"
            ),
        },
        "next_obligations": [
            "Identify every residual term created by differentiating slotCutoff and clockWindow cutoffs.",
            "Construct or rule out a no-cutoff extension of one canonical primary through neighboring slots.",
            "Bound cross-slot and cross-frequency interactions for a simultaneous hierarchy.",
            "Prove all-order initial-data summability in the actual physical coordinates.",
            "Recompute the exact Navier-Stokes residual after removing localization; do not infer closure from amplitude smallness.",
        ],
    }
