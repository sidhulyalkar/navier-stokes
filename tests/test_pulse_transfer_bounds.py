from blowup_lab.pulse_transfer_bounds import ExponentInterval, compare_exponent_intervals, source_extraction_plan


def test_fail_closed_when_unknown():
    plan = source_extraction_plan()
    assert plan["verdict"]["status"] == "OPEN"


def test_disjoint_interval_classification():
    s = ExponentInterval("gamma", 1.0, 1.2)
    b = ExponentInterval("delta", 0.4, 0.8)
    assert compare_exponent_intervals(s, b).status == "SUPPRESSION_WINS"
    assert compare_exponent_intervals(b, s).status == "BACKWARD_WINS"


def test_overlap_stays_open():
    s = ExponentInterval("gamma", 0.8, 1.2)
    b = ExponentInterval("delta", 1.0, 1.4)
    assert compare_exponent_intervals(s, b).status == "OPEN"
