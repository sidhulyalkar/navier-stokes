from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
import math


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class RationalInterval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("interval lower endpoint exceeds upper endpoint")

    def contains(self, other: "RationalInterval") -> bool:
        return self.lo <= other.lo and other.hi <= self.hi

    def disjoint(self, other: "RationalInterval") -> bool:
        return self.hi < other.lo or other.hi < self.lo

    def to_dict(self) -> dict:
        return {
            "lo": str(self.lo),
            "hi": str(self.hi),
            "lo_float": float(self.lo),
            "hi_float": float(self.hi),
        }


NATIVE_SUPPORT = RationalInterval(Fraction(1, 6), Fraction(5, 6))
NATIVE_PLATEAU = RationalInterval(Fraction(3, 10), Fraction(7, 10))
NATIVE_LEFT_DERIVATIVE = RationalInterval(Fraction(1, 6), Fraction(3, 10))
NATIVE_RIGHT_DERIVATIVE = RationalInterval(Fraction(7, 10), Fraction(5, 6))

PATCH_SUPPORT = RationalInterval(Fraction(2, 5), Fraction(3, 2))
PATCH_PLATEAU = RationalInterval(Fraction(27, 40), Fraction(49, 40))
PATCH_LEFT_DERIVATIVE = RationalInterval(Fraction(2, 5), Fraction(27, 40))
PATCH_RIGHT_DERIVATIVE = RationalInterval(Fraction(49, 40), Fraction(3, 2))

DELAYED_SUPPORT = RationalInterval(Fraction(1, 6), Fraction(3, 2))
DELAYED_PLATEAU = RationalInterval(Fraction(3, 10), Fraction(49, 40))


def affine_patch_center() -> Fraction:
    """Center of the source-style affine patch, measured in native slot lengths."""
    return Fraction(19, 20)


def affine_patch_half_width() -> Fraction:
    """Outer support half-width of the affine patch, measured in native slot lengths."""
    return Fraction(11, 20)


def gaussian_extra_square_distance() -> Fraction:
    """Extra normalized squared distance paid by moving the right derivative collar.

    Native right collar starts at v/L = 7/10, hence distance from midpoint is 1/5.
    Delayed right collar starts at v/L = 49/40, hence distance from midpoint is 29/40.
    """
    return Fraction(29, 40) ** 2 - Fraction(1, 5) ** 2


def gaussian_extra_suppression(*, c: float, L: float) -> float:
    """Conditional gain factor exp(-(777/1600)cL) for the right localization channel.

    This assumes an already-certified Gaussian upper envelope
        exp(-c (v-L/2)^2 / L).
    It is not a total-force estimate.
    """
    if c < 0:
        raise ValueError("c must be nonnegative")
    if L <= 0:
        raise ValueError("L must be positive")
    return math.exp(-float(gaussian_extra_square_distance()) * c * L)


def delayed_cutoff_geometry_report() -> dict:
    old_right_erased = PATCH_PLATEAU.contains(NATIVE_RIGHT_DERIVATIVE)
    no_new_left_commutator = NATIVE_PLATEAU.contains(PATCH_LEFT_DERIVATIVE)
    native_left_untouched = NATIVE_LEFT_DERIVATIVE.disjoint(PATCH_SUPPORT)
    delayed_right_after_native_support = PATCH_RIGHT_DERIVATIVE.lo > NATIVE_SUPPORT.hi

    if not all(
        (old_right_erased, no_new_left_commutator, native_left_untouched, delayed_right_after_native_support)
    ):
        raise AssertionError("delayed cutoff rational geometry contract is inconsistent")

    extra = gaussian_extra_square_distance()
    return {
        "schema": "delayed-right-cutoff-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "definition": {
            "native": "chi_L(v) = GaussianTailFlat.slotCutoff L v",
            "patch": (
                "eta_L(v) = SmoothCutoffs.cutoff((v/L - 19/20)/(11/20)); "
                "equivalently an affine copy of the pinned smooth cutoff"
            ),
            "delayed": "chi_tilde = chi + eta*(1-chi)",
            "derivative_identity": "chi_tilde' = (1-eta)*chi' + eta'*(1-chi)",
        },
        "intervals_in_units_of_L": {
            "native_support": NATIVE_SUPPORT.to_dict(),
            "native_plateau": NATIVE_PLATEAU.to_dict(),
            "native_left_derivative": NATIVE_LEFT_DERIVATIVE.to_dict(),
            "native_right_derivative": NATIVE_RIGHT_DERIVATIVE.to_dict(),
            "patch_support": PATCH_SUPPORT.to_dict(),
            "patch_plateau": PATCH_PLATEAU.to_dict(),
            "patch_left_derivative": PATCH_LEFT_DERIVATIVE.to_dict(),
            "patch_right_derivative": PATCH_RIGHT_DERIVATIVE.to_dict(),
            "delayed_support": DELAYED_SUPPORT.to_dict(),
            "delayed_plateau": DELAYED_PLATEAU.to_dict(),
        },
        "exact_geometry_checks": {
            "old_right_derivative_inside_patch_plateau": old_right_erased,
            "patch_left_derivative_inside_native_plateau": no_new_left_commutator,
            "native_left_derivative_disjoint_from_patch_support": native_left_untouched,
            "patch_right_derivative_after_native_support": delayed_right_after_native_support,
        },
        "right_channel_gaussian_gain": {
            "old_distance_from_midpoint": "1/5",
            "new_distance_from_midpoint": "29/40",
            "extra_square_distance": str(extra),
            "expected_exact_value": "777/1600",
            "conditional_factor": "exp(-(777/1600)*c*L)",
            "scope": "right cutoff localization channel only",
        },
        "formal_gates": [
            {
                "gate": "delayed_cutoff_support_and_plateau",
                "status": "ALGEBRAIC_SPEC_READY_FOR_LEAN",
            },
            {
                "gate": "three_halves_common_cover_separation",
                "status": "SOURCE_WRAPPER_READY_FOR_LEAN",
                "identity": (
                    "(3/2)*slotLength(r0,h,n) = slotLength(3*r0/2,h,n), "
                    "with 3*r0/2 < 2*r0 for r0>0"
                ),
            },
            {
                "gate": "delayed_cutoff_derivative_support",
                "status": "PENDING_AFTER_GEOMETRY_FORMALIZATION",
            },
            {
                "gate": "delayed_cutoff_unweighted_class",
                "status": "OPEN_HIGH_VALUE_GATE",
                "reason": (
                    "If proved, pinned LinearWaveBounds.InputBounds.with_cutoff and "
                    "constructed_goodCoefficient_class preserve the downstream remainder class."
                ),
            },
        ],
        "claim_boundary": (
            "This contract moves one cutoff derivative collar and computes a conditional Gaussian gain. "
            "It does not prove that the actual OpenAI force norm is smaller, that all nonlinear overlap "
            "terms remain admissible, or that an unforced Navier-Stokes solution exists."
        ),
    }
