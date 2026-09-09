from __future__ import annotations

from dataclasses import asdict
from .models import ProofObligation


def unforced_obligations() -> list[ProofObligation]:
    return [
        ProofObligation("U01", "Construct smooth divergence-free initial data u0 with the required spatial decay/energy.", "initial-data"),
        ProofObligation("U02", "Construct a classical Navier-Stokes solution on [0,1) from u0 with no external force.", "PDE", ["U01"]),
        ProofObligation("U03", "Prove the exact residual R(u,p) vanishes identically, not merely to all orders at t=1.", "PDE", ["U02"]),
        ProofObligation("U04", "Preserve the concentrating inner velocity growth causing ||u(t)||_infty to become unbounded as t->1.", "blowup", ["U02"]),
        ProofObligation("U05", "Prove kinetic energy remains uniformly bounded on [0,1).", "energy", ["U02"]),
        ProofObligation("U06", "Replace the externally seeded pulse schedule by initial-data or endogenous dynamics while retaining covariance stress delivery.", "wave-dynamics", ["U01", "U03"]),
        ProofObligation("U07", "Either realize the annular stress internally or construct a background profile whose annular residual vanishes.", "stress", ["U03"]),
        ProofObligation("U08", "Control all zero-mode, cross-wave, and higher-order nonlinear residuals without reintroducing forcing.", "correction", ["U03", "U06", "U07"]),
        ProofObligation("U09", "Globalize the construction with smooth decay without spatial/temporal cutoff forcing, or prove those cutoff residuals cancel exactly.", "globalization", ["U03"]),
        ProofObligation("U10", "Prove compatibility with a theorem/continuation criterion that converts the constructed singular trajectory into breakdown of global smooth bounded-energy solutions.", "theorem", ["U04", "U05", "U09"]),
    ]


def obligations_dict() -> dict:
    obs = unforced_obligations()
    return {"target": "UNFORCED_NAVIER_STOKES_BLOWUP_RESEARCH", "claim_level": "OPEN_RESEARCH_OBLIGATIONS", "obligations": [asdict(o) for o in obs]}
