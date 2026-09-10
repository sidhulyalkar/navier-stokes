from __future__ import annotations

from fractions import Fraction


def natural_entrance_h_upper_exact(j_upper: Fraction = Fraction(1, 1000)) -> Fraction:
    """Exact sufficient h threshold for the v5.4 NaturalEntrance certificate.

    From source >= 3 - j - h(17+2j) and target source > 29/10.
    """
    if not Fraction(0) <= j_upper < Fraction(1, 10):
        raise ValueError("j_upper must lie in [0, 1/10)")
    return (Fraction(1, 10) - j_upper) / (Fraction(17) + 2 * j_upper)


def matching_cone_h_upper_exact(
    j_upper: Fraction = Fraction(1, 1000),
    ell_lower: Fraction = Fraction(11, 20),
) -> Fraction:
    """Exact threshold for the conservative v5.4 shape-axis certificate.

    Lower bound:
      ell(3-j) - 2j - h(8ell + 9 + 2j) > 8/5.

    The reported worst case uses the minimum ell.  Its monotonicity is valid
    throughout the returned small-h regime because d/dell of the lower bound
    is 3-j-8h > 0 there.
    """
    if not Fraction(0) <= j_upper < Fraction(1, 10):
        raise ValueError("j_upper must lie in [0, 1/10)")
    if ell_lower <= 0:
        raise ValueError("ell_lower must be positive")
    intercept = ell_lower * (Fraction(3) - j_upper) - 2 * j_upper
    coefficient = 8 * ell_lower + 9 + 2 * j_upper
    threshold = (intercept - Fraction(8, 5)) / coefficient
    if threshold <= 0:
        raise ValueError("assumptions do not leave a positive h margin")
    if Fraction(3) - j_upper - 8 * threshold <= 0:
        raise ValueError("ell monotonicity is not certified over the threshold window")
    return threshold


def exact_relaxation_report() -> dict:
    entrance = natural_entrance_h_upper_exact()
    cone = matching_cone_h_upper_exact()
    return {
        "schema": "exact-local-h-relaxations-v1",
        "arithmetic": "fractions.Fraction exact rational arithmetic",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538",
        },
        "natural_entrance": {
            "exact": f"{entrance.numerator}/{entrance.denominator}",
            "decimal": float(entrance),
        },
        "matching_cone_shape_axis": {
            "exact": f"{cone.numerator}/{cone.denominator}",
            "decimal": float(cone),
        },
        "active_of_these_two": "NavierStokes.MatchingConeBounds.shape_axis_lower",
        "claim_boundary": (
            "These are exact values for the project's conservative sufficient inequalities, not sharp thresholds for the source theorems or the complete construction."
        ),
    }
