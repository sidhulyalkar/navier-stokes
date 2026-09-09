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
        """Source-backed continuous bounds implied by 1 <= eps*k^2 <= 4.

        The true carrier is an integer. These are real-number comparison bounds.
        """
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
    """Bound dyadic stage n from the continuous carrier inequalities.

    From 2^(nh/2) <= k <= 2*2^(nh/2), for h>0 and k>0:
      2 log2(k/2)/h <= n <= 2 log2(k)/h.
    The lower bound is clipped at zero for small k.
    """
    if h <= 0 or k <= 0:
        raise ValueError("h and k must be positive")
    lo = max(0.0, 2.0 * math.log2(k / 2.0) / h)
    hi = 2.0 * math.log2(k) / h
    return lo, hi


def gaussian_fixed_fraction_exponent_bounds(
    *, h: float, k: float, r0: float, tg: float, c: float, fraction: float
) -> tuple[float, float]:
    """Conditional exponent bounds for a Gaussian envelope at fixed slot fraction.

    GaussianEnvelope gives envelope <= exp(-c * Delta^2/(2 ell)). If
    |Delta| = fraction * ell, the positive decay exponent is
        c * fraction^2 * ell / 2.

    Combining stage/carrier and ell~n^2 yields bounds in carrier coordinates.
    This is conditional on the actual evaluation/cutoff location remaining a
    fixed positive fraction of the slot length.
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
        "schema": "pulse-stage-scaling-v1",
        "source_facts": [
            "SlotColoring.dyadicQ: Q_n = 2^(-n)",
            "ChartScales.epsilon: epsilon_n = Q_n^h = 2^(-n h)",
            "ChartScales.carrier_viscosity_bounds: 1 <= epsilon_n k_n^2 <= 4",
            "ChartScales.slotLength_bounds: 2 r0 n^2 <= ell_n <= 2 r0 Tg n^2",
            "GaussianEnvelope.gaussian_envelope_bounds: envelope <= exp(-c Delta_t^2/(2 ell_n))",
        ],
        "derived": {
            "carrier_vs_stage": "2^(n h/2) <= k_n <= 2*2^(n h/2)",
            "stage_vs_carrier": "n = Theta(log k_n) for fixed h>0",
            "slot_vs_carrier": "ell_n = Theta((log k_n)^2) for fixed h,r0>0",
            "conditional_fixed_fraction_tail": (
                "If |Delta_t| >= a*ell_n for a fixed a>0 in the region where the Gaussian "
                "bound applies, then envelope <= exp(-C*n^2) = exp(-Theta((log k_n)^2))."
            ),
        },
        "scientific_update": (
            "The v5.1 toy model exp(-c*k^gamma) is not the source-natural carrier parametrization "
            "for this Gaussian slot estimate. The source-natural stage tail is Gaussian in n, "
            "which is log-squared in carrier frequency k."
        ),
        "open_obligations": [
            "prove the actual pulse cutoff/evaluation region lies a uniform positive fraction of a slot from the midpoint when this tail is used",
            "identify the correct backward propagator norm in the same stage or carrier coordinate",
            "compare backward growth against exp(-C*n^2), not against an assumed exp(-c*k^gamma)",
            "control constants uniformly across pulse labels, derivatives, and correction stages",
        ],
        "claim_boundary": (
            "All algebraic scale conversions above follow from pinned source definitions/bounds. "
            "The fixed-fraction tail conclusion is conditional and is not yet asserted for the full actual pulse hierarchy."
        ),
    }
