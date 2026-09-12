from __future__ import annotations

from blowup_lab.final_force_attribution import final_force_attribution
from blowup_lab.residual_force_ledger import exact_residual_attribution_report


def force_residual_bridge_report() -> dict:
    """Join the global force DAG and normalized residual ledger without inventing a bridge.

    The repository now has two source-backed descriptions at different levels:

    * the global force ancestry from the final smooth force down to the incoming
      mixed diagonal residual;
    * the exact normalized cycle-residual decomposition into physical and
      harmonic-reconstruction channels.

    What is *not* yet source-extracted as one explicit theorem-level map is the
    attribution bridge identifying each normalized residual channel with a
    corresponding additive contribution to the mixed diagonal residual after
    physical-chart conversion and spatial localization.  This report makes that
    remaining gap first-class instead of silently equating the two ledgers.
    """

    force = final_force_attribution()
    residual = exact_residual_attribution_report()

    return {
        "schema": "force-residual-bridge-v1",
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
        "bridge": {
            "from": "incoming.mixed_diagonal_residual",
            "to": "normalized physical residual / harmonic reconstruction",
            "status": "OPEN",
            "reason": (
                "The source-backed ledgers live on opposite sides of physical-chart conversion, "
                "diagonal summation, spatial localization, and periodization.  v5.7 has not yet "
                "extracted one exact additive identity carrying every normalized atom through "
                "those wrappers into the final mixed diagonal residual."
            ),
            "required_obligations": [
                "identify the exact physical-chart image of each normalized residual channel",
                "track diagonal summation without merging independently bounded channels",
                "separate spatial-cutoff derivative cost from the interior original residual",
                "separate periodization-region cost from the interior cut residual",
                "prove which channel controls the terminal 3/4 < t < 1 residual rate",
            ],
        },
        "sigma_relevance": {
            "native_bottleneck": "representation.harmonic_sum",
            "candidate_delta_for_sigma_plus_one_fifth": "h/5",
            "terminal_force_relevance": "CONDITIONAL",
            "conditions": [
                "the same literal state is formally requalified at sigma + 1/5",
                "the stronger harmonic residual rate survives physical-chart conversion",
                "the stronger rate survives diagonal summation and spatial localization",
                "the terminal incoming residual is actually improved rather than merely reindexed",
            ],
        },
        "hard_findings": {
            "global_force_ancestry_extracted": True,
            "normalized_residual_decomposition_extracted": True,
            "exact_bridge_from_normalized_atoms_to_final_diagonal_force_extracted": False,
            "sigma_shift_proven_to_reduce_terminal_force": False,
            "actual_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "next_frontier": (
            "Extract the smallest exact bridge from ActualCycleResidualBounds / physical residual "
            "conversion into MixedDiagonalResidual.  Do not optimize Gaussian, alias, activation, "
            "or Borel-extension terms before that bridge identifies what survives into the "
            "terminal forcing channel."
        ),
    }
