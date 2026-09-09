from __future__ import annotations

from dataclasses import dataclass, asdict
from math import exp, log


@dataclass(frozen=True)
class TransferAsymptotic:
    id: str
    tail_c: float
    tail_gamma: float
    backward_d: float
    backward_delta: float
    classification: str
    reason: str


def classify_stretched_exponential(tail_c: float, tail_gamma: float,
                                   backward_d: float, backward_delta: float,
                                   case_id: str = "case") -> TransferAsymptotic:
    """Classify a model initial-pulse amplitude

        a0(k) ~ exp(-c k^gamma + d k^delta).

    SUPERPOLYNOMIAL means this toy asymptotic is small enough to beat every fixed
    Sobolev polynomial weight k^s. This is a generic criterion, not a measurement
    of the OpenAI construction.
    """
    if tail_c <= 0 or backward_d < 0 or tail_gamma <= 0 or backward_delta <= 0:
        raise ValueError("invalid positive asymptotic parameters")
    if tail_gamma > backward_delta:
        cls = "SUPERPOLYNOMIAL"
        reason = "tail suppression exponent dominates backward amplification exponent"
    elif tail_gamma < backward_delta:
        cls = "FAIL"
        reason = "backward amplification exponent dominates tail suppression"
    elif tail_c > backward_d:
        cls = "SUPERPOLYNOMIAL"
        reason = "equal exponents but suppression coefficient is larger"
    elif tail_c == backward_d:
        cls = "BORDERLINE"
        reason = "leading stretched-exponential factors cancel; subleading terms decide"
    else:
        cls = "FAIL"
        reason = "equal exponents but backward amplification coefficient is larger"
    return TransferAsymptotic(case_id, tail_c, tail_gamma, backward_d, backward_delta, cls, reason)


def finite_sobolev_budget(tail_c: float, tail_gamma: float, backward_d: float,
                          backward_delta: float, max_level: int = 12,
                          max_s: int = 8, base_frequency: float = 2.0) -> dict:
    """Finite diagnostic for the toy schedule k_n=base_frequency^n.

    Returns log-contributions to avoid overflow. A negative and rapidly decreasing
    log contribution is favorable. No theorem about the source construction is inferred.
    """
    rows = []
    for n in range(1, max_level + 1):
        k = base_frequency ** n
        log_a0 = -tail_c * (k ** tail_gamma) + backward_d * (k ** backward_delta)
        row = {"n": n, "k": k, "log_abs_a0": log_a0}
        for s in range(max_s + 1):
            row[f"log_H{s}_contribution"] = log_a0 + s * log(k)
        rows.append(row)
    return {"rows": rows, "max_level": max_level, "max_s": max_s, "base_frequency": base_frequency}


def default_transfer_campaign() -> dict:
    cases = [
        classify_stretched_exponential(1.0, 1.0, 0.5, 0.5, "T1_SUPPRESSION_WINS_EXPONENT"),
        classify_stretched_exponential(1.0, 1.0, 0.5, 1.0, "T2_SUPPRESSION_WINS_COEFFICIENT"),
        classify_stretched_exponential(1.0, 1.0, 1.0, 1.0, "T3_BORDERLINE"),
        classify_stretched_exponential(0.5, 1.0, 1.0, 1.0, "T4_BACKWARD_WINS_COEFFICIENT"),
        classify_stretched_exponential(1.0, 0.5, 0.5, 1.0, "T5_BACKWARD_WINS_EXPONENT"),
    ]
    diagnostic = finite_sobolev_budget(1.0, 1.0, 0.5, 1.0)
    return {
        "model": "a0(k) ~ exp(-c k^gamma + d k^delta)",
        "claim_level": "GENERIC_ASYMPTOTIC_CRITERION",
        "cases": [asdict(c) for c in cases],
        "source_construction_parameters_known": False,
        "next_measurements": [
            "Extract the Gaussian/tail suppression scale for each leading pulse from Section 7.",
            "Derive a backward evolution bound from global t=0 to each pulse activation interval.",
            "Relate the pulse frequency hierarchy to the activation-level index.",
            "Check all-s Sobolev/Gevrey summability of the pulled-back hierarchy.",
            "Bound nonlinear cross-scale interactions before each pulse becomes active.",
        ],
        "finite_diagnostic_example": diagnostic,
    }
