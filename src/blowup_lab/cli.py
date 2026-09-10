from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

from .ablation import default_routes, route_dict
from .atlas import ResidualAtlas
from .certificates import build_certificate_dag
from .constraint_ledger import ledger_report
from .discovery import campaign_dict, local_campaign
from .exact_relaxations import exact_relaxation_report
from .h_dependency import graph_report
from .initial_data_transfer import default_transfer_campaign
from .local_relaxations import relaxation_report
from .localization_obstruction import localization_obstruction_report
from .proof import obligations_dict
from .pulse_localization_audit import pulse_localization_audit
from .pulse_stage_scaling import asymptotic_coordinate_report
from .pulse_transfer_bounds import source_extraction_plan
from .scaling import SimilarityScaling, leading_balance_family


VERSION = "5.5.0"


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
        ("exact_h_relaxations", exact_h, ("reference_scaling",)),
    ])

    report = {
        "version": VERSION,
        "scientific_status": "LOCALIZATION_OBSTRUCTION_AND_UPSTREAM_AWARE_BOTTLENECK_AUDIT",
        "claims": {
            "published_proof_architecture_encoded": True,
            "leading_scaling_balances_reproduced": True,
            "within_slot_primary_homogeneous_zero_forcing_source_backed": True,
            "slot_cutoff_tail_geometry_source_backed": True,
            "gaussian_tail_beats_every_fixed_Q_power_source_backed": True,
            "exact_temporal_compactness_compatible_with_nonzero_homogeneous_linear_pulse": False,
            "global_no_cutoff_pulse_extension_constructed": False,
            "actual_openai_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "atlas": {"atoms": len(atlas["atoms"]), "hash": atlas["atlas_hash"]},
        "ablation": {
            "routes": len(routes),
            "promote": sum(r["status"] == "PROMOTE" for r in routes),
            "hold": sum(r["status"] == "HOLD" for r in routes),
            "kill": sum(r["status"] == "KILL" for r in routes),
        },
        "scaling_search": {k: discovery[k] for k in ("candidate_count", "promoted", "held", "killed")},
        "h_relaxations": exact_h,
        "pulse_localization": pulse_localization["hard_findings"],
        "localization_obstruction": localization_obstruction["decision"],
        "research_pivot": pulse_localization["research_pivot"],
        "next_blocker": (
            "Map every cutoff-generated residual/source term and test a globally present Gaussian-small tail hierarchy; "
            "in parallel trace the selected-construction dependency that keeps h at 1/1000 despite broader manuscript-range axis results."
        ),
        "certificate_dag": cert,
    }
    dump(outdir / "v550_report.json", report)
    return report


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, default=Path("artifacts/v550"))
    args = p.parse_args()
    report = run(args.out)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
