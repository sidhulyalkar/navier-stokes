from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class SlackAtom:
    atom_id: str
    strongest_visible_gain: str
    source_helper_gain: str
    source_declaration: str
    primitive_reason: str
    frontier_at_actual_parameters: bool

    def to_dict(self) -> dict:
        return asdict(self)


def symbolic_slack_atoms() -> list[SlackAtom]:
    """Proof-level gain ledger extracted from pinned LinearWaveBounds.

    `strongest_visible_gain` records the common exponent obtained directly
    from the primitive estimates used inside the source proof, before its
    final `mono_exponent` weakening.  These are source-proof lower bounds on
    class regularity, not sharp asymptotics or lower bounds on the fields.
    """

    old = "alpha + 1/2 - 3*kappa"
    candidate = "alpha + 1/2 - kappa"
    return [
        SlackAtom(
            atom_id="remainder.slow_transport",
            strongest_visible_gain="alpha + 1 - kappa",
            source_helper_gain=old,
            source_declaration="LinearWaveBounds.InputBounds.slowTransport_mem",
            primitive_reason="radial branch is weakest among alpha+1, alpha+1-kappa, alpha+1",
            frontier_at_actual_parameters=False,
        ),
        SlackAtom(
            atom_id="remainder.phase_defect",
            strongest_visible_gain="alpha + 1/2",
            source_helper_gain=old,
            source_declaration="LinearWaveBounds.InputBounds.phaseDefect_mem",
            primitive_reason="defect has exponent 1 and frequency multiplication costs 1/2",
            frontier_at_actual_parameters=False,
        ),
        SlackAtom(
            atom_id="remainder.base_derivative",
            strongest_visible_gain="alpha + 1",
            source_helper_gain=old,
            source_declaration="LinearWaveBounds.InputBounds.baseDerivativeRemainder_mem",
            primitive_reason="all three component branches are weakened from alpha+1",
            frontier_at_actual_parameters=False,
        ),
        SlackAtom(
            atom_id="remainder.pressure_gradient",
            strongest_visible_gain=candidate,
            source_helper_gain=old,
            source_declaration="LinearWaveBounds.InputBounds.pressureGradient_mem",
            primitive_reason="radial derivative loses kappa from pressure class alpha+1/2",
            frontier_at_actual_parameters=True,
        ),
        SlackAtom(
            atom_id="remainder.viscous_part",
            strongest_visible_gain=candidate,
            source_helper_gain=old,
            source_declaration="LinearWaveBounds.InputBounds.viscousPart_mem",
            primitive_reason=(
                "after epsilon restores one exponent, frequency-weighted normal cross/divergence terms have "
                "gain alpha+1/2-kappa; Drr fits the same target when kappa<=1/2"
            ),
            frontier_at_actual_parameters=True,
        ),
        SlackAtom(
            atom_id="constructed_good.curl_principal",
            strongest_visible_gain=candidate,
            source_helper_gain=old,
            source_declaration="LinearWaveBounds.InputBounds.curl_principal_gain",
            primitive_reason=(
                "principalVelocity_class preserves the curl-correction gain alpha+1/2-kappa exactly; the source "
                "helper then weakens it by an extra 2*kappa only to match the old remainder target"
            ),
            frontier_at_actual_parameters=True,
        ),
    ]


def actual_parameter_ledger() -> dict:
    alpha = Fraction(1, 2)
    kappa = Fraction(1, 10)
    old = alpha + Fraction(1, 2) - 3 * kappa
    candidate = alpha + Fraction(1, 2) - kappa

    gains = {
        "remainder.slow_transport": alpha + 1 - kappa,
        "remainder.phase_defect": alpha + Fraction(1, 2),
        "remainder.base_derivative": alpha + 1,
        "remainder.pressure_gradient": candidate,
        "remainder.viscous_part": candidate,
        "constructed_good.curl_principal": candidate,
    }
    return {
        "alpha": str(alpha),
        "kappa": str(kappa),
        "source_common_gain": str(old),
        "candidate_common_gain": str(candidate),
        "candidate_gain_improvement": str(candidate - old),
        "candidate_gain_improvement_equals_2kappa": candidate - old == 2 * kappa,
        "primitive_visible_gains": {key: str(value) for key, value in gains.items()},
        "frontier_atoms": [key for key, value in gains.items() if value == candidate],
    }


def cutoff_channel_reclassification() -> dict:
    return {
        "source_identity": (
            "PrimaryPiece.linearResidual = PrimaryPiece.linearGoodField + PrimaryPiece.excluded"
        ),
        "excluded_definition": "PrimaryPiece.excluded is the vectorMode of LinearWaveBounds.excludedSlotError",
        "actual_gaussian_representation": (
            "ActualInitialization.gaussianBlock.oscillation = primaryPiece.excluded"
        ),
        "first_particular_source": (
            "ActualInitialization.initialResidualBlock = HarmonicResidual.residualBlock(context, initialState, "
            "primaryBlock, gaussianBlock.velocity, 0)"
        ),
        "residual_block_operation": (
            "realCoefficients(nonlinearResidual(base+mean,wave,pressure) - gaussian - alias), then nonconstant"
        ),
        "decision": "DEMOTE_AS_RATE_BOTTLENECK__KEEP_AS_EXACT_FORCE_ABLATION",
        "reason": (
            "The cutoff-derived excluded field is explicitly supplied as the Gaussian subtraction before the first "
            "nonconstant residual source. It remains a real nonzero excluded-error channel, but the source proves "
            "Gaussian excluded errors as flat/all-power whereas the constructed-good residual carries the finite "
            "primary rate."
        ),
        "claim_boundary": (
            "This does not prove removing the cutoff is irrelevant to an exact unforced construction. It only shows "
            "that the pinned correction architecture already separates/cancels that channel from the finite-rate "
            "harmonic source sent to the first particular solve."
        ),
    }


def improved_remainder_candidate() -> dict:
    return {
        "schema": "linear-remainder-slack-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "symbolic_atoms": [atom.to_dict() for atom in symbolic_slack_atoms()],
        "actual_parameters": actual_parameter_ledger(),
        "cutoff_channel": cutoff_channel_reclassification(),
        "formal_candidate": {
            "file": "formal/V570ImprovedLinearRemainder.lean",
            "target": "WaveClass s P (alpha + 1/2 - kappa) (a.remainder s d)",
            "hypotheses_added_beyond_source_InputBounds": ["kappa <= 1/2"],
            "note": "kappa <= 1/2 is already assumed by the pinned goodCoefficient_class theorem",
            "validation": "PENDING_SOURCE_LOCKED_LEAN_CI",
        },
        "hard_findings": {
            "old_helper_gain_actual": "7/10",
            "candidate_gain_actual": "9/10",
            "candidate_formally_validated": False,
            "downstream_iteration_gain_improved": False,
            "actual_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "next_gate_if_formal_candidate_passes": (
            "Propagate the 9/10 primary residual class through ActualInitialization, then inspect whether the "
            "correction ledger can start from sigma=2/5 rather than sigma=1/5 without violating later nonlinear, "
            "particular-wave, mean-update, or excluded-error constraints."
        ),
    }
