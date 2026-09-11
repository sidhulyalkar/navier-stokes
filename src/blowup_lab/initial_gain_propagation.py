from __future__ import annotations

from dataclasses import dataclass, asdict
from fractions import Fraction


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class PropagationGate:
    gate_id: str
    condition: str
    actual_rhs: Fraction
    candidate_gamma: Fraction
    source_declaration: str
    passes: bool
    interpretation: str

    def to_dict(self) -> dict:
        out = asdict(self)
        out["actual_rhs"] = str(self.actual_rhs)
        out["candidate_gamma"] = str(self.candidate_gamma)
        return out


def propagation_gates() -> list[PropagationGate]:
    alpha = Fraction(1, 2)
    chart_kappa = Fraction(1, 10)
    mean_increment = Fraction(9, 10)
    gamma = Fraction(9, 10)

    nonlinear_rhs = 2 * alpha - chart_kappa
    mean_rhs = alpha + mean_increment - Fraction(1, 2)

    return [
        PropagationGate(
            gate_id="zero_mean_self_transport",
            condition="gamma <= 2*alpha - chart_kappa",
            actual_rhs=nonlinear_rhs,
            candidate_gamma=gamma,
            source_declaration="ActualInitialization.zeroMean_residual_uniform",
            passes=gamma <= nonlinear_rhs,
            interpretation=(
                "At alpha=1/2 and chart_kappa=1/10 the nonlinear self-transport ceiling is exactly 9/10, so a "
                "9/10 linear-good input is not weakened by the zero-mean residual theorem."
            ),
        ),
        PropagationGate(
            gate_id="initialized_mean_update",
            condition="gamma <= alpha + H - 1/2",
            actual_rhs=mean_rhs,
            candidate_gamma=gamma,
            source_declaration="CorrectionStep.meanStage_residual_uniform",
            passes=gamma <= mean_rhs,
            interpretation=(
                "The actual cumulative mean is already converted to H=9/10 by meanIncrement_of_cumulative; with "
                "alpha=1/2 the mean-stage ceiling is exactly 9/10."
            ),
        ),
    ]


def shifted_schedule_hypothesis() -> dict:
    return {
        "source_schedule": "sigma(J) = 1/5 + J/10",
        "source_sigma_zero": "1/5",
        "candidate_initial_sigma": "2/5",
        "source_index_with_same_sigma": 2,
        "arithmetic_observation": (
            "ExponentLedger correction inequalities are stated uniformly for sigma >= 1/5, so sigma=2/5 is "
            "arithmetically admissible."
        ),
        "not_yet_proved": (
            "The actual initial CycleAnalyticInvariant is currently constructed at sigma=1/5. A stronger residual "
            "bound alone does not imply all other invariant fields satisfy the sigma=2/5 requirements."
        ),
        "next_gate": (
            "Audit every sigma-dependent field of CycleAnalyticInvariant at the literal initial state and determine "
            "whether the existing initial data satisfy the invariant at sigma=2/5."
        ),
        "decision": "PROMOTE_CONDITIONALLY",
    }


def initial_gain_report() -> dict:
    gates = propagation_gates()
    return {
        "schema": "initial-gain-propagation-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "candidate_linear_gain": "9/10",
        "gates": [gate.to_dict() for gate in gates],
        "all_source_inequality_gates_pass": all(gate.passes for gate in gates),
        "formal_propagation_file": "formal/V570InitialResidualPropagation.lean",
        "formal_validation": "PENDING_SOURCE_LOCKED_LEAN_CI",
        "shifted_schedule": shifted_schedule_hypothesis(),
        "hard_findings": {
            "nonlinear_zero_mean_ceiling_clips_candidate": False,
            "initialized_mean_stage_clips_candidate": False,
            "actual_primary_linear_gain_9_10_formalized": False,
            "actual_initial_residual_gain_9_10_end_to_end_formalized": False,
            "initial_cycle_invariant_sigma_2_5_proved": False,
            "correction_cycles_skipped": 0,
        },
    }
