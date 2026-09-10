from fractions import Fraction

from blowup_lab.exact_relaxations import (
    matching_cone_h_upper_exact,
    natural_entrance_h_upper_exact,
)


def test_natural_entrance_exact_threshold():
    assert natural_entrance_h_upper_exact() == Fraction(99, 17002)


def test_matching_cone_exact_threshold():
    assert matching_cone_h_upper_exact() == Fraction(949, 268040)


def test_matching_cone_remains_the_tighter_of_two_certificates():
    assert matching_cone_h_upper_exact() < natural_entrance_h_upper_exact()


def test_matching_cone_ell_monotonicity_at_certified_threshold():
    h = matching_cone_h_upper_exact()
    j = Fraction(1, 1000)
    assert Fraction(3) - j - 8 * h > 0
