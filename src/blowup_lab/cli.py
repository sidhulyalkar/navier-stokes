from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from .ablation import default_routes, route_dict
from .atlas import ResidualAtlas
from .certificates import build_certificate_dag
from .discovery import campaign_dict, local_campaign
from .proof import obligations_dict
from .initial_data_transfer import default_transfer_campaign
from .scaling import SimilarityScaling, leading_balance_family
from .constraint_ledger import ledger_report
from .pulse_transfer_bounds import source_extraction_plan


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
    pulse_bounds = source_extraction_plan()

    dump(outdir / "residual_atlas.json", atlas)
    dump(outdir / "ablation_campaign.json", {"routes": routes})
    dump(outdir / "scaling_reference.json", scaling_report)
    dump(outdir / "candidate_search.json", discovery)
    dump(outdir / "proof_obligations.json", proof)
    dump(outdir / "initial_data_transfer.json", transfer)
    dump(outdir / "constraint_ledger.json", constraints)
    dump(outdir / "pulse_transfer_bounds.json", pulse_bounds)

    with (outdir / "ablation_matrix.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["route_id", "status", "score", "disabled", "alternatives", "hard_failures", "open_obligations"])
        for r in routes:
            w.writerow([r["route_id"], r["status"], r["score"], ";".join(r["disabled"]),
                        ";".join(r["enabled_alternatives"]), ";".join(r["hard_failures"]),
                        ";".join(r["open_obligations"])])

    atlas_hash = atlas["atlas_hash"]
    cert = build_certificate_dag([
        ("reference_scaling", scaling_report, ()),
        ("source_residual_atlas", atlas, ()),
    ])
    report = {
        "version": "5.2.0",
        "scientific_status": "CONSTRAINT_PROVENANCE_AND_PULSE_TRANSFER_EXTRACTION",
        "claims": {
            "published_proof_architecture_encoded": True,
            "leading_scaling_balances_reproduced": True,
            "actual_openai_profiles_numerically_reproduced": False,
            "actual_openai_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
            "constraint_provenance_ledger_added": True,
            "actual_pulse_transfer_exponents_extracted": False,
        },
        "atlas": {"atoms": len(atlas["atoms"]), "hash": atlas_hash},
        "ablation": {
            "routes": len(routes),
            "promote": sum(r["status"] == "PROMOTE" for r in routes),
            "hold": sum(r["status"] == "HOLD" for r in routes),
            "kill": sum(r["status"] == "KILL" for r in routes),
            "top_non_killed": sorted(
                [r for r in routes if r["status"] != "KILL"],
                key=lambda x: float(x["score"]), reverse=True)[:4],
        },
        "scaling_search": {k: discovery[k] for k in ("candidate_count", "promoted", "held", "killed")},
        "scaling_frontier": leading_balance_family(),
        "initial_data_transfer": {
            "model": transfer["model"],
            "source_parameters_known": transfer["source_construction_parameters_known"],
            "criterion": "tail suppression must dominate backward amplification strongly enough for all-Sobolev summability",
        },
        "constraint_ledger": constraints["scientific_interpretation"],
        "pulse_transfer": {"status": pulse_bounds["verdict"]["status"], "claim": pulse_bounds["claim"]},
        "next_blocker": "Extract certified Section 7 pulse-tail and backward-propagator exponent intervals; then trace which downstream inequalities genuinely require the formalization's concrete h <= 1/1000 window.",
        "certificate_dag": cert,
    }
    dump(outdir / "v520_report.json", report)
    return report


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, default=Path("artifacts/v520"))
    args = p.parse_args()
    report = run(args.out)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
