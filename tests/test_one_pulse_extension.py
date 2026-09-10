from blowup_lab.one_pulse_extension import one_pulse_extension_audit


def test_extension_is_defined_but_dynamics_are_not_globally_certified():
    report = one_pulse_extension_audit()
    gates = {gate["gate_id"]: gate for gate in report["gates"]}
    assert gates["function_defined_on_R"]["status"] == "PASS"
    assert gates["homogeneous_ode_on_native_interval"]["status"] == "PASS"
    assert gates["homogeneous_ode_outside_native_interval"]["status"] == "OPEN"


def test_first_blocker_is_dynamics_scope_not_function_definition():
    report = one_pulse_extension_audit()
    assert report["first_blocker"]["gate_id"] == "homogeneous_ode_outside_native_interval"


def test_uncut_principal_localization_error_is_only_local_progress():
    report = one_pulse_extension_audit()
    gates = {gate["gate_id"]: gate for gate in report["gates"]}
    assert gates["uncut_principal_error_on_native_interval"]["status"] == "PASS"
    assert gates["uncut_full_pde_residual_global"]["status"] == "FAIL_NOT_ESTABLISHED"


def test_unforced_claim_remains_false():
    report = one_pulse_extension_audit()
    assert report["hard_nonclaims"]["global_homogeneous_extension_exists"] is False
    assert report["hard_nonclaims"]["unforced_blowup_proved"] is False
