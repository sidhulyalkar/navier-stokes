from __future__ import annotations

import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class StageScaling:
    h: float
    n: int
    r0: float
    tg: float

    def epsilon(self) -> float:
        return 2.0 ** (-self.n * self.h)

    def carrier_bounds(self) -> tuple[float, float]:
        """Source-backed continuous bounds implied by 1 <= eps*k^2 <= 4."""
        eps = self.epsilon()
        return eps ** -0.5, 2.0 * eps ** -0.5

    def slot_length_bounds(self) -> tuple[float, float]:
        """Source-backed bounds from ChartScales.slotLength_bounds."""
        s = float(self.n * self.n)
        return 2.0 * self.r0 * s, 2.0 * self.r0 * self.tg * s

    def to_dict(self) -> dict:
        out = asdict(self)
        out.update(
            epsilon=self.epsilon(),
            carrier_bounds=self.carrier_bounds(),
            slot_length_bounds=self.slot_length_bounds(),
        )
        return out


def stage_from_carrier_bounds(h: float, k: float) -> tuple[float, float]:
    """Bound dyadic stage n from 2^(nh/2) <= k <= 2*2^(nh/2)."""
    if h <= 0 or k <= 0:
        raise ValueError("h and k must be positive")
    lo = max(0.0, 2.0 * math.log2(k / 2.0) / h)
    hi = 2.0 * math.log2(k) / h
    return lo, hi


def gaussian_fixed_fraction_exponent_bounds(
    *, h: float, k: float, r0: float, tg: float, c: float, fraction: float
) -> tuple[float, float]:
    """Decay-exponent bounds for a Gaussian envelope at fixed slot fraction.

    GaussianEnvelope gives envelope <= exp(-c*Delta^2/(2 ell)). When
    |Delta| >= fraction*ell, the exponent is at least c*fraction^2*ell/2.
    GaussianTailFlat proves fraction=1/5 on support of slot-cutoff derivatives.
    """
    if min(h, k, r0, tg, c, fraction) <= 0:
        raise ValueError("all parameters must be positive")
    n_lo, n_hi = stage_from_carrier_bounds(h, k)
    ell_lo = 2.0 * r0 * n_lo * n_lo
    ell_hi = 2.0 * r0 * tg * n_hi * n_hi
    pref = c * fraction * fraction / 2.0
    return pref * ell_lo, pref * ell_hi


def asymptotic_coordinate_report() -> dict:
    return {
        "schema": "pulse-stage-scaling-v2",
        "source_facts": [
            "SlotColoring.dyadicQ: Q_n = 2^(-n)",
            "ChartScales.epsilon: epsilon_n = Q_n^h = 2^(-n h)",
            "ChartScales.carrier_viscosity_bounds: 1 <= epsilon_n k_n^2 <= 4",
            "ChartScales.slotLength_bounds: ell_n = Theta(n^2)",
            "GaussianTailFlat.slotCutoff_deriv_support: L/5 <= |v-L/2| <= L/3 on cutoff-derivative support",
            "GaussianTailFlat.reference_envelope_off_plateau: envelope <= exp(-(u*referenceMinSlope/50)*L)",
            "GaussianTailFlat.gaussian_beats_Q_power: polynomial(S)*exp(-c*S) is bounded by every fixed real power of Q",
            "ActualGaussianCoverage.length_uniform_lower: actual scaled slot length has a uniform multiple of S=n^2",
        ],
        "derived": {
            "carrier_vs_stage": "2^(n h/2) <= k_n <= 2*2^(n h/2)",
            "stage_vs_carrier": "n = Theta(log k_n) for fixed h>0",
            "slot_vs_carrier": "ell_n = Theta((log k_n)^2)",
            "cutoff_tail": (
                "On the actual slot-cutoff derivative region the fixed-fraction separation is source-backed, "
                "so any uniform positive Gaussian rate and slot-length coefficient yield exp(-C*n^2) decay."
            ),
        },
        "scientific_update": (
            "The fixed-fraction tail condition is now source-backed for slot-cutoff derivatives. "
            "The remaining quantitative task is to track the uniform positive rate/length constants through the "
            "selected actual construction and then study what happens if the cutoff is removed."
        ),
        "open_obligations": [
            "extract the selected construction's explicit uniform lower bounds for Gaussian rate and scaled slot length",
            "enumerate all source/residual terms caused by slot and clock cutoffs",
            "construct or obstruct a globally defined no-cutoff homogeneous pulse through neighboring slots",
            "control cross-frequency interactions if all pre-activation tails are simultaneously present",
        ],
        "claim_boundary": (
            "The source proves Gaussian flatness for cutoff errors and dyadic super-polynomial absorption. "
            "This does not prove that the cutoffs can be removed or that a global unforced pulse hierarchy exists."
        ),
    }
