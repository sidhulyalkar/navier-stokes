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
from .exact_relaxations import exact_relaxation_report
from .h_dependency import graph_report
from .initial_data_transfer import default_transfer_campaign
from .local_relaxations import relaxation_report
from .localization_obstruction import localization_obstruction_report
from .one_pulse_extension import one_pulse_extension_audit
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
    one_pulse = one_pulse_extension_audit()

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
    dump(outdir / "one_pulse_extension.json", one_pulse)

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
        ("one_pulse_extension", one_pulse, ("cutoff_residual_atlas",)),
        ("exact_h_relaxations", exact_h, ("reference_scaling",)),
    ])

    report = {
        "version": VERSION,
        "scientific_status": "CUTOFF_RESIDUAL_ATLAS_AND_ONE_PULSE_DOMAIN_OBSTRUCTION",
        "claims": {
            "published_proof_architecture_encoded": True,
            "leading_scaling_balances_reproduced": True,
            "within_slot_primary_homogeneous_zero_forcing_source_backed": True,
            "excluded_slot_error_two_channel_identity_source_backed": True,
            "primary_source_zero_eliminates_uncovered_source_channel": True,
            "slot_cutoff_tail_geometry_source_backed": True,
            "uncut_principal_localization_error_zero_under_solve_hypothesis": True,
            "existing_differentiable_extension_is_source_backed_global_homogeneous_solution": False,
            "global_no_cutoff_pulse_extension_constructed": False,
            "actual_openai_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "cutoff_atlas": {
            "scenario_count": len(cutoff_atlas["scenarios"]),
            "hard_findings": cutoff_atlas["hard_findings"],
        },
        "one_pulse_extension": {
            "first_blocker": one_pulse["first_blocker"],
            "next_candidate": one_pulse["next_candidate"],
        },
        "h_relaxations": exact_h,
        "upstream_policy": {
            "source_lock": "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538",
            "lock_migrated": False,
        },
        "next_blocker": (
            "Prove or kill an enlarged-interval homogeneous primary by extending the actual frame/coefficient "
            "hypotheses beyond Icc(0,L), then recompute the non-principal residual and two-pulse interaction terms."
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
