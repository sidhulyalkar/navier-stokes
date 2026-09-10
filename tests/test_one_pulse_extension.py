from blowup_lab.one_pulse_extension import one_pulse_extension_audit


def test_clamped_tail_is_killed_but_wider_source_slot_exists():
    report = one_pulse_extension_audit()
    gates = {gate["gate_id"]: gate for gate in report["gates"]}
    assert gates["function_defined_on_R"]["status"] == "PASS"
    assert gates["homogeneous_ode_on_native_interval"]["status"] == "PASS"
    assert gates["naive_clamped_tail_homogeneous"]["status"] == "KILL"
    assert gates["wider_source_slot_available"]["status"] == "PASS"


def test_first_active_gate_is_enlarged_coefficient_continuity():
    report = one_pulse_extension_audit()
    assert report["first_active_gate"]["gate_id"] == "one_sided_coefficient_continuity"
    assert report["first_active_gate"]["status"] == "READY_TO_FORMALIZE"


def test_modal_continuation_precedes_ambient_kinematics():
    report = one_pulse_extension_audit()
    gates = {gate["gate_id"]: gate for gate in report["gates"]}
    ids = [gate["gate_id"] for gate in report["gates"]]
    assert ids.index("one_sided_modal_primary") < ids.index("one_sided_kinematics_wrapper")
    assert gates["one_sided_modal_primary"]["status"] == "READY_AFTER_CONTINUITY"
    assert gates["one_sided_kinematics_wrapper"]["status"] == "READY_TO_FORMALIZE"


def test_one_sided_candidate_keeps_same_seed_and_has_uniqueness_bridge():
    report = one_pulse_extension_audit()
    gates = {gate["gate_id"]: gate for gate in report["gates"]}
    assert report["next_candidate"]["interval"] == "[0, 3L/2]"
    assert gates["agreement_with_native_primary"]["source_declaration"] == "TangentODE.linear_solution_unique"
    assert gates["constructed_good_after_psi_one"]["status"] == "OPEN"
    assert gates["uncut_full_pde_residual_after_extension"]["status"] == "OPEN"


def test_unforced_claim_remains_false():
    report = one_pulse_extension_audit()
    assert report["hard_nonclaims"]["enlarged_coefficient_continuity_lean_checked"] is False
    assert report["hard_nonclaims"]["enlarged_modal_primary_lean_checked"] is False
    assert report["hard_nonclaims"]["generalized_kinematics_lean_checked"] is False
    assert report["hard_nonclaims"]["enlarged_homogeneous_extension_constructed"] is False
    assert report["hard_nonclaims"]["unforced_blowup_proved"] is False
