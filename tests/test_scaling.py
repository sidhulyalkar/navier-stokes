from fractions import Fraction
from blowup_lab.scaling import SimilarityScaling, mixed_norm_tau_power, time_integrability


def test_openai_volume_and_energy():
    s = SimilarityScaling.openai_reference(Fraction(1,200))
    assert s.volume_exponent == Fraction(299,200)
    assert s.energy_exponent("z") == Fraction(97,200)
    assert s.energy_exponent("z") > 0


def test_radial_balance_reference():
    s = SimilarityScaling.openai_reference()
    r = s.balance_report()["z"]
    assert r["radial_leading_balance"] is True
    assert r["axial_advection_leading"] is True
    assert r["axial_diffusion_gap"] == str(2*s.h)


def test_mixed_norm_classifier():
    p = mixed_norm_tau_power(Fraction(3,2), Fraction(3,2), Fraction(3,2))
    assert p == Fraction(-1,2)
    assert time_integrability(p, Fraction(2,1)) == "borderline-log"


def test_leading_balance_family_wider_than_paper_window():
    from blowup_lab.scaling import leading_balance_family
    f = leading_balance_family()
    assert f["solution"]["equivalent_h_interval_if_beta_z=1/2-h"] == "0 < h < 1/6"
    assert f["paper_reference_range"] == "0 < h < 1/100"
