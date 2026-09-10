from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

from .ablation import default_routes, route_dict
from .atlas import ResidualAtlas
from .certificates import build_certificate_dag
from .constraint_ledger import ledger_report
from .cutoff_residual_atlas import cutoff_residual_atlas
from .discovery import campaign_dict, local_campaign
from .enlarged_interval import enlarged_interval_report
from .exact_relaxations import exact_relaxation_report
from .h_dependency import graph_report
from .initial_data_transfer import default_transfer_campaign
from .local_relaxations import relaxation_report
from .localization_obstruction import localization_obstruction_report
from .one_pulse_extension import one_pulse_extension_audit
from .primary_residual_layers import primary_linear_residual_layers
from .proof import obligations_dict
from .pulse_localization_audit import pulse_localization_audit
from .pulse_stage_scaling import asymptotic_coordinate_report
from .pulse_transfer_bounds import source_extraction_plan
from .scaling import SimilarityScaling, leading_balance_family


VERSION = "5.6.0"


def dump(path: Path, obj: dict) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def run(outdir: Path) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    atlas = ResidualAtlas().to_dict()
    routes = [route_dict(r) for r in default_routes()]
    scaling = SimilarityScaling.openai_reference()
    scaling_report = {
        "reference": scaling.to_dict(),
        "balances": scaling.balance_report(),
        "leading_balance_family": leading_balance_family(),
    }
    discovery = campaign_dict(local_campaign())
    proof = obligations_dict()
    transfer = default_transfer_campaign()
    constraints = ledger_report()
    legacy_pulse_plan = source_extraction_plan()
    pulse_scaling = asymptotic_coordinate_report()
    h_graph = graph_report()
    local_h = relaxation_report()
    exact_h = exact_relaxation_report()
    pulse_localization = pulse_localization_audit()
    localization_obstruction = localization_obstruction_report()
    cutoff_atlas = cutoff_residual_atlas()
    enlarged = enlarged_interval_report()
    one_pulse = one_pulse_extension_audit()
    primary_layers = primary_linear_residual_layers()

    dump(outdir / "residual_atlas.json", atlas)
    dump(outdir / "ablation_campaign.json", {"routes": routes})
    dump(outdir / "scaling_reference.json", scaling_report)
    dump(outdir / "candidate_search.json", discovery)
    dump(outdir / "proof_obligations.json", proof)
    dump(outdir / "initial_data_transfer.json", transfer)
    dump(outdir / "constraint_ledger.json", constraints)
    dump(outdir / "pulse_transfer_bounds_legacy.json", legacy_pulse_plan)
    dump(outdir / "pulse_stage_scaling.json", pulse_scaling)
    dump(outdir / "h_dependency.json", h_graph)
    dump(outdir / "local_h_relaxations.json", local_h)
    dump(outdir / "exact_h_relaxations.json", exact_h)
    dump(outdir / "pulse_localization_audit.json", pulse_localization)
    dump(outdir / "localization_obstruction.json", localization_obstruction)
    dump(outdir / "cutoff_residual_atlas.json", cutoff_atlas)
    dump(outdir / "enlarged_interval.json", enlarged)
    dump(outdir / "one_pulse_extension.json", one_pulse)
    dump(outdir / "primary_residual_layers.json", primary_layers)

    with (outdir / "ablation_matrix.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["route_id", "status", "score", "disabled", "alternatives", "hard_failures", "open_obligations"])
        for r in routes:
            w.writerow([
                r["route_id"], r["status"], r["score"], ";".join(r["disabled"]),
                ";".join(r["enabled_alternatives"]), ";".join(r["hard_failures"]),
                ";".join(r["open_obligations"]),
            ])

    cert = build_certificate_dag([
        ("reference_scaling", scaling_report, ()),
        ("source_residual_atlas", atlas, ()),
        ("pulse_localization_audit", pulse_localization, ("source_residual_atlas",)),
        ("localization_obstruction", localization_obstruction, ("pulse_localization_audit",)),
        ("cutoff_residual_atlas", cutoff_atlas, ("localization_obstruction",)),
        ("enlarged_interval_source_coverage", enlarged, ("cutoff_residual_atlas",)),
        ("one_pulse_extension", one_pulse, ("enlarged_interval_source_coverage",)),
        ("primary_residual_layers", primary_layers, ("one_pulse_extension",)),
        ("exact_h_relaxations", exact_h, ("reference_scaling",)),
    ])

    report = {
        "version": VERSION,
        "scientific_status": "ONE_SIDED_ENLARGED_PRIMARY_READY_TO_FORMALIZE",
        "claims": {
            "published_proof_architecture_encoded": True,
            "leading_scaling_balances_reproduced": True,
            "within_slot_primary_homogeneous_zero_forcing_source_backed": True,
            "excluded_slot_error_two_channel_identity_source_backed": True,
            "primary_source_zero_eliminates_uncovered_source_channel": True,
            "slot_cutoff_tail_geometry_source_backed": True,
            "uncut_principal_localization_error_zero_under_solve_hypothesis": True,
            "naive_clamped_tail_is_homogeneous_continuation": False,
            "source_analysis_slot_wider_than_native_ode_interval": True,
            "one_sided_interval_0_to_3L_over_2_strictly_inside_source_slot": True,
            "constructed_good_remains_explicit_after_psi_one": True,
            "constructed_good_proved_nonzero": False,
            "generalized_enlarged_interval_kinematics_lean_checked": False,
            "enlarged_homogeneous_primary_constructed": False,
            "actual_openai_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "cutoff_atlas": {
            "scenario_count": len(cutoff_atlas["scenarios"]),
            "hard_findings": cutoff_atlas["hard_findings"],
            "naive_uncut_clamped_reuse": cutoff_atlas["naive_uncut_clamped_reuse"],
        },
        "enlarged_interval": {
            "candidate": enlarged["candidate"],
            "formalization_queue": enlarged["formalization_queue"],
            "first_unresolved_after_source_reuse": enlarged["first_unresolved_after_source_reuse"],
        },
        "one_pulse_extension": {
            "first_active_gate": one_pulse["first_active_gate"],
            "killed_lineages": one_pulse["killed_lineages"],
            "next_candidate": one_pulse["next_candidate"],
        },
        "post_localization_residual": {
            "exact_identity": primary_layers["exact_identity"],
            "psi_one_counterfactual": primary_layers["psi_one_counterfactual"],
            "next_question": primary_layers["next_question"],
        },
        "h_relaxations": exact_h,
        "upstream_policy": {
            "source_lock": "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538",
            "lock_migrated": False,
        },
        "next_blocker": (
            "Lean-check coefficient continuity and FrameData.Kinematics on [0,3L/2], instantiate the same-seed "
            "homogeneous solution there, prove agreement with the canonical primary on [0,L] by "
            "TangentODE.linear_solution_unique, then recompute constructedGood with psi=1 and classify its "
            "curl-principal and corrected-remainder pieces before touching two-pulse interactions."
        ),
        "certificate_dag": cert,
    }
    dump(outdir / "v560_report.json", report)
    return report


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, default=Path("artifacts/v560"))
    args = p.parse_args()
    report = run(args.out)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
