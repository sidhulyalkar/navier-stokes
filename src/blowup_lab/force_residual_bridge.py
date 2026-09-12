from __future__ import annotations

from blowup_lab.final_force_attribution import final_force_attribution
from blowup_lab.residual_force_ledger import exact_residual_attribution_report


def force_residual_bridge_report() -> dict:
    """Join the global force DAG and normalized residual ledger at the right granularity.

    The source now supports two different bridge statements that must not be
    conflated:

    1. an **aggregate rate bridge** is explicit: finite physical residual
       `JetRate` estimates are installed in `StageEstimates`, consumed by the
       diagonal schedule theorem, and yield vanishing jets for the infinite
       mixed residual;
    2. the **termwise attribution bridge** is still open: the exact normalized
       harmonic/mean/base bookkeeping decomposition has not been carried as
       separate additive channels through physical-chart conversion, diagonal
       summation, spatial localization and periodization.

    Keeping these separate prevents a stronger finite-prefix exponent from
    being mislabeled as a smaller final force.
    """

    force = final_force_attribution()
    residual = exact_residual_attribution_report()

    return {
        "schema": "force-residual-bridge-v2",
        "source_lock": force["source_lock"],
        "global_force_frontier": {
            "node": "incoming.mixed_diagonal_residual",
            "terminal_region": force["terminal_region"],
            "hard_findings": force["hard_findings"],
        },
        "normalized_residual_frontier": {
            "physical_atoms": residual["physical_atoms"],
            "representation_atoms": residual["representation_atoms"],
            "identities": residual["identities"],
            "native_gain_ledger": residual["native_gain_ledger"],
            "hard_findings": residual["hard_findings"],
        },
        "aggregate_rate_bridge": {
            "status": "SOURCE_EXACT",
            "input": "finite uncut residual JetRate with exponent gain(J) - residualLoss(m)",
            "path": [
                "ActualCycleResidualBounds.finite_residual_rates",
                "ActualStageEstimates.stageEstimates_of_representations.finite_residual",
                "MixedCandidateAssembly.StageEstimates.exists_schedule",
                "MixedDiagonalResidual.exists_physical_schedule_residual_zero",
                "MixedDiagonalResidual.physical_vanishingJointJets",
                "JointResidualLimits.VanishingJointJets",
            ],
            "output": "the infinite mixed diagonal residual has vanishing jets of every finite order at the endpoint",
            "interpretation": (
                "The finite-stage residual exponent is a genuine input to diagonal assembly. "
                "However, the final endpoint conclusion is already all-orders flat, so increasing "
                "the finite exponent does not by itself produce a strictly stronger endpoint-flatness class."
            ),
        },
        "termwise_attribution_bridge": {
            "from": "normalized physical residual / harmonic reconstruction",
            "to": "incoming.mixed_diagonal_residual and final force channels",
            "status": "OPEN",
            "reason": (
                "No extracted identity yet carries each normalized harmonic, mean and base channel "
                "separately through physical-chart conversion, diagonal summation, spatial cutoff, "
                "periodization and time localization."
            ),
            "required_obligations": [
                "identify the physical-chart image of each normalized residual channel",
                "track diagonal summation without merging independently bounded channels",
                "separate spatial-cutoff derivative cost from the interior original residual",
                "separate periodization-region cost from the interior cut residual",
                "bind any norm-sensitive final-force quantity to the separately tracked channels",
            ],
        },
        "sigma_relevance": {
            "native_bottleneck": "representation.harmonic_sum",
            "candidate_delta_for_sigma_plus_one_fifth": "h/5",
            "aggregate_diagonal_relevance": "SOURCE_BACKED",
            "immediate_effect_if_requalified": "stronger finite-prefix residual JetRate",
            "endpoint_flatness_effect": "NO_STRICT_IMPROVEMENT_FROM_EXPONENT_ALONE",
            "possible_nonredundant_effects_to_test": [
                "less aggressive admissible diagonal schedule",
                "smaller finite-prefix depth for a fixed residual target",
                "better quantitative constants or rates away from the endpoint",
                "a norm-sensitive reduction after localization, if separately proved",
            ],
            "not_implied": [
                "two correction cycles are deleted",
                "the infinite mixed residual is in a stronger-than-all-orders endpoint class",
                "the final forcing norm is smaller",
                "an unforced Navier-Stokes singularity exists",
            ],
        },
        "hard_findings": {
            "global_force_ancestry_extracted": True,
            "normalized_residual_decomposition_extracted": True,
            "aggregate_rate_bridge_to_mixed_diagonal_flatness_extracted": True,
            "exact_termwise_bridge_to_final_force_extracted": False,
            "sigma_shift_proven_to_reduce_terminal_force": False,
            "actual_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "next_frontier": (
            "Quantify whether a stronger finite residual rate changes the selected diagonal schedule "
            "or a norm-sensitive force quantity.  In parallel, carry the harmonic bottleneck as a "
            "separate channel through physical-chart conversion and localization.  Endpoint flatness "
            "alone is no longer a useful success metric because the source already proves all-orders flatness."
        ),
    }
