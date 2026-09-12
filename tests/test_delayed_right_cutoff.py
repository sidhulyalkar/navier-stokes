from fractions import Fraction

import pytest

from blowup_lab.delayed_right_cutoff import (
    DELAYED_PLATEAU,
    DELAYED_SUPPORT,
    NATIVE_LEFT_DERIVATIVE,
    NATIVE_PLATEAU,
    NATIVE_RIGHT_DERIVATIVE,
    NATIVE_SUPPORT,
    PATCH_LEFT_DERIVATIVE,
    PATCH_PLATEAU,
    PATCH_RIGHT_DERIVATIVE,
    PATCH_SUPPORT,
    affine_patch_center,
    affine_patch_half_width,
    delayed_cutoff_geometry_report,
    gaussian_extra_square_distance,
    gaussian_extra_suppression,
)


def test_affine_patch_has_exact_center_and_half_width():
    assert affine_patch_center() == Fraction(19, 20)
    assert affine_patch_half_width() == Fraction(11, 20)
    assert affine_patch_center() - affine_patch_half_width() == Fraction(2, 5)
    assert affine_patch_center() + affine_patch_half_width() == Fraction(3, 2)


def test_patch_left_transition_is_hidden_inside_native_plateau():
    assert NATIVE_PLATEAU.contains(PATCH_LEFT_DERIVATIVE)


def test_native_right_transition_is_erased_by_patch_plateau():
    assert PATCH_PLATEAU.contains(NATIVE_RIGHT_DERIVATIVE)


def test_native_left_transition_is_untouched():
    assert NATIVE_LEFT_DERIVATIVE.disjoint(PATCH_SUPPORT)


def test_new_right_transition_occurs_after_native_support():
    assert PATCH_RIGHT_DERIVATIVE.lo > NATIVE_SUPPORT.hi


def test_delayed_support_and_plateau_are_exact():
    assert DELAYED_SUPPORT.lo == Fraction(1, 6)
    assert DELAYED_SUPPORT.hi == Fraction(3, 2)
    assert DELAYED_PLATEAU.lo == Fraction(3, 10)
    assert DELAYED_PLATEAU.hi == Fraction(49, 40)


def test_exact_extra_gaussian_square_distance():
    assert gaussian_extra_square_distance() == Fraction(777, 1600)


def test_gaussian_suppression_is_strict_for_positive_c_and_L():
    factor = gaussian_extra_suppression(c=0.2, L=20.0)
    assert 0 < factor < 1


def test_gaussian_suppression_fails_closed_on_invalid_inputs():
    with pytest.raises(ValueError):
        gaussian_extra_suppression(c=-0.1, L=1.0)
    with pytest.raises(ValueError):
        gaussian_extra_suppression(c=0.1, L=0.0)


def test_report_keeps_total_force_claim_closed():
    report = delayed_cutoff_geometry_report()
    checks = report["exact_geometry_checks"]
    assert all(checks.values())
    assert report["right_channel_gaussian_gain"]["extra_square_distance"] == "777/1600"
    assert "does not prove that the actual OpenAI force norm is smaller" in report["claim_boundary"]
