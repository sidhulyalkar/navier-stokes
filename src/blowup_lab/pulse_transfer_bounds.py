from __future__ import annotations

from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class ExponentInterval:
    name: str
    lower: float | None = None
    upper: float | None = None
    evidence: str = "UNKNOWN"
    source_ref: str = ""

    def validate(self) -> None:
        if self.lower is not None and self.upper is not None and self.lower > self.upper:
            raise ValueError(f"invalid interval for {self.name}")


@dataclass(frozen=True)
class TransferVerdict:
    status: str
    reason: str
    suppression: ExponentInterval
    backward: ExponentInterval

    def to_dict(self) -> dict:
        return {
            "status": self.status,
            "reason": self.reason,
            "suppression": asdict(self.suppression),
            "backward": asdict(self.backward),
        }


def compare_exponent_intervals(suppression: ExponentInterval, backward: ExponentInterval) -> TransferVerdict:
    """Fail-closed comparison of gamma vs delta in exp(-c k^gamma + d k^delta).

    We only declare an exponent-level win when the supplied intervals are disjoint.
    Unknown or overlapping bounds remain OPEN instead of being filled in by an agent.
    """
    suppression.validate()
    backward.validate()
    if suppression.lower is None or suppression.upper is None or backward.lower is None or backward.upper is None:
        return TransferVerdict(
            "OPEN",
            "one or both exponent intervals are not quantitatively bounded",
            suppression,
            backward,
        )
    if suppression.lower > backward.upper:
        return TransferVerdict(
            "SUPPRESSION_WINS",
            "every admissible suppression exponent exceeds every admissible backward-amplification exponent",
            suppression,
            backward,
        )
    if suppression.upper < backward.lower:
        return TransferVerdict(
            "BACKWARD_WINS",
            "every admissible backward-amplification exponent exceeds every admissible suppression exponent",
            suppression,
            backward,
        )
    return TransferVerdict(
        "OPEN",
        "exponent intervals overlap; coefficients and sharper asymptotics are required",
        suppression,
        backward,
    )


def source_extraction_plan() -> dict:
    unknown = ExponentInterval(
        "gamma_tail",
        evidence="SOURCE_EXTRACTION_REQUIRED",
        source_ref="OpenAI Navier-Stokes Section 7 pulse Gaussian/tail bounds",
    )
    backward = ExponentInterval(
        "delta_backward",
        evidence="NEW_BOUND_REQUIRED",
        source_ref="backward propagator from t=0 to pulse activation time",
    )
    verdict = compare_exponent_intervals(unknown, backward)
    return {
        "model": "|a_n(0)| ~ exp(-c k_n^gamma_tail + d k_n^delta_backward)",
        "verdict": verdict.to_dict(),
        "measurement_contract": [
            "Extract a quantitative tail bound with explicit dependence on pulse frequency/scale.",
            "Define the exact linearized/homogeneous pulse propagator used on each activation interval.",
            "Bound the inverse/backward map from the global initial slice to the pulse activation slice.",
            "Relate pulse index, activation scale, and frequency without asymptotic handwaving.",
            "Only compare gamma_tail and delta_backward after both have certified intervals.",
            "If exponents overlap, compare leading coefficients c and d with explicit error bars.",
            "After single-pulse transfer succeeds, prove all-Sobolev summability and nonlinear cross-pulse compatibility.",
        ],
        "claim": "No numerical gamma_tail or delta_backward is asserted in v5.2.",
    }
