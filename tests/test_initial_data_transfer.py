from blowup_lab.initial_data_transfer import classify_stretched_exponential, finite_sobolev_budget


def test_suppression_exponent_wins():
    r = classify_stretched_exponential(1, 1, 10, 0.5)
    assert r.classification == "SUPERPOLYNOMIAL"


def test_backward_exponent_wins():
    r = classify_stretched_exponential(1, 0.5, 0.01, 1)
    assert r.classification == "FAIL"


def test_equal_exponent_coefficient_test():
    assert classify_stretched_exponential(2, 1, 1, 1).classification == "SUPERPOLYNOMIAL"
    assert classify_stretched_exponential(1, 1, 1, 1).classification == "BORDERLINE"
    assert classify_stretched_exponential(1, 1, 2, 1).classification == "FAIL"


def test_finite_budget_has_all_requested_sobolev_columns():
    d = finite_sobolev_budget(1, 1, 0.5, 1, max_level=4, max_s=3)
    assert len(d["rows"]) == 4
    assert "log_H3_contribution" in d["rows"][-1]
