from blowup_lab.pulse_localization_audit import pulse_localization_audit


def test_primary_is_source_backed_homogeneous_zero_forcing():
    report = pulse_localization_audit()
    findings = report["hard_findings"]
    assert findings["within_slot_primary_is_homogeneous"] is True
    assert findings["within_slot_primary_uses_zero_forcing"] is True


def test_localization_removal_remains_open():
    report = pulse_localization_audit()
    findings = report["hard_findings"]
    assert findings["global_no_cutoff_extension_constructed"] is False
    assert findings["all_pulses_encoded_in_one_global_initial_datum"] is False
    assert findings["unforced_navier_stokes_residual_closed"] is False


def test_cutoff_tail_geometry_is_no_longer_conditional():
    report = pulse_localization_audit()
    assert report["hard_findings"]["slot_cutoff_tail_region_is_source_backed"] is True
    cutoff = next(node for node in report["nodes"] if node["name"] == "slot_cutoff")
    assert "L/5" in cutoff["consequence"]
    assert "L/3" in cutoff["consequence"]
