from __future__ import annotations

from dataclasses import dataclass, asdict
from fractions import Fraction
from itertools import product
from .scaling import SimilarityScaling


@dataclass(frozen=True)
class ScalingCandidate:
    id: str
    h: Fraction
    beta_r: Fraction
    beta_z: Fraction
    alpha_r: Fraction
    alpha_t: Fraction
    radial_balance: bool
    axial_adv_balance: bool
    axial_diff_subleading: bool
    finite_dominant_energy: bool
    velocity_blowup: bool
    score: int
    disposition: str


def evaluate_scaling(h: Fraction, beta_r: Fraction, beta_z: Fraction,
                     alpha_r: Fraction, alpha_t: Fraction, idx: int) -> ScalingCandidate:
    s = SimilarityScaling(h, beta_r, beta_z, alpha_r, alpha_t, alpha_t)
    t = s.time_derivative("z")
    radial = t == s.advection("r", "r", "z") == s.diffusion("r", "z")
    axial_adv = t == s.advection("z", "z", "z")
    axial_diff_sub = s.diffusion("z", "z") < t
    finite_energy = s.energy_exponent("z") > 0
    blowup = alpha_t > 0
    booleans = [radial, axial_adv, axial_diff_sub, finite_energy, blowup]
    score = sum(booleans)
    disposition = "PROMOTE" if score == 5 else ("HOLD" if score == 4 else "KILL")
    return ScalingCandidate(f"SC{idx:03d}", h, beta_r, beta_z, alpha_r, alpha_t,
                            radial, axial_adv, axial_diff_sub, finite_energy, blowup,
                            score, disposition)


def local_campaign() -> list[ScalingCandidate]:
    h = Fraction(1, 200)
    vals_br = [Fraction(49, 100), Fraction(1, 2), Fraction(51, 100)]
    vals_bz = [Fraction(49, 100) - h, Fraction(1, 2) - h, Fraction(51, 100) - h]
    vals_ar = [Fraction(49, 100), Fraction(1, 2), Fraction(51, 100)]
    vals_at = [Fraction(49, 100) + h, Fraction(1, 2) + h, Fraction(51, 100) + h]
    out = []
    for idx, vals in enumerate(product(vals_br, vals_bz, vals_ar, vals_at), 1):
        out.append(evaluate_scaling(h, *vals, idx))
    return out


def campaign_dict(cands: list[ScalingCandidate]) -> dict:
    def convert(c):
        d = asdict(c)
        for k, v in list(d.items()):
            if isinstance(v, Fraction):
                d[k] = str(v)
        return d
    return {
        "candidate_count": len(cands),
        "promoted": sum(c.disposition == "PROMOTE" for c in cands),
        "held": sum(c.disposition == "HOLD" for c in cands),
        "killed": sum(c.disposition == "KILL" for c in cands),
        "candidates": [convert(c) for c in cands],
        "interpretation": "Cheap power-counting filter only. Promotion means scaling-consistent, not existence of a PDE profile or singular solution.",
    }
