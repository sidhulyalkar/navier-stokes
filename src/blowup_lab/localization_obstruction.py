from __future__ import annotations

from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CutoffCommutator:
    equation: str
    assumption: str
    residual_identity: str
    implication: str
    scope: str

    def to_dict(self) -> dict:
        return asdict(self)


def homogeneous_cutoff_commutator() -> CutoffCommutator:
    """Exact product-rule identity for a cutoff homogeneous linear pulse.

    For x' = A(v)x and y = chi(v)x,
        y' - A(v)y = chi'(v)x.

    This is algebraic.  It does not claim that all Navier-Stokes localization
    errors reduce to this one term; spatial/frame/cutoff operations introduce
    additional commutators in the full construction.
    """
    return CutoffCommutator(
        equation="x'(v) = A(v) x(v)",
        assumption="y(v) = chi(v) x(v)",
        residual_identity="y'(v) - A(v)y(v) = chi'(v) x(v)",
        implication=(
            "A nonconstant temporal cutoff applied to a nonzero homogeneous pulse generally creates a source. "
            "The source is small when x is small on supp(chi'), but small is not zero."
        ),
        scope="two-mode linear pulse subsystem; full PDE has further localization commutators",
    )


def compact_support_uniqueness_obstruction() -> dict:
    """Fail-closed statement of the finite-dimensional uniqueness obstruction."""
    return {
        "schema": "homogeneous-time-localization-obstruction-v1",
        "assumptions": [
            "x solves a homogeneous linear ODE x'=A(v)x on a connected interval",
            "the ODE has uniqueness for initial data (continuous linear coefficients suffice)",
            "x vanishes on a nonempty interval before its intended activation",
        ],
        "conclusion": "x is identically zero on the connected solution interval",
        "research_consequence": (
            "A nontrivial zero-source pulse cannot retain exact compact temporal support. "
            "An unforced replacement must instead carry nonzero pre/post-slot tails or change the mechanism class."
        ),
        "not_claimed": [
            "This does not prove the full Navier-Stokes forcing is necessary.",
            "This does not rule out an unforced singular construction with globally present pulse tails.",
            "This does not rule out a different nonlinear mechanism that avoids the linear pulse architecture.",
        ],
    }


def localization_obstruction_report() -> dict:
    return {
        "commutator": homogeneous_cutoff_commutator().to_dict(),
        "uniqueness_obstruction": compact_support_uniqueness_obstruction(),
        "decision": {
            "exact_temporal_compactness_plus_homogeneous_nonzero_pulse": "KILL",
            "globally_present_gaussian_small_tails": "PROMOTE_FOR_ANALYSIS",
            "different_intrinsic_nonlinear_mechanism": "HOLD",
        },
    }
