from blowup_lab.ablation import evaluate_ablation, default_routes
from blowup_lab.models import RouteStatus


def test_naive_force_zero_fails_closed():
    r = evaluate_ablation("x", ["pulse_seeding", "localized_force"])
    assert r.status == RouteStatus.KILL
    assert r.hard_failures


def test_initial_data_route_survives_structural_filter():
    r = evaluate_ablation("x", ["pulse_seeding", "temporal_cutoff"], ["initial_data_pulses"])
    assert r.status != RouteStatus.KILL
    assert not r.hard_failures


def test_stress_removal_without_replacement_fails():
    r = evaluate_ablation("x", ["stress_cone"])
    assert r.status == RouteStatus.KILL


def test_default_routes_include_shooting():
    ids = {r.route_id for r in default_routes()}
    assert "R5_UNFORCED_SHOOTING" in ids


def test_intrinsic_balance_can_remove_wave_seed_structurally():
    r = evaluate_ablation(
        "x",
        ["annular_stress", "stress_cone", "pulse_seeding", "amplify_then_damp"],
        ["intrinsic_annular_balance"],
    )
    assert r.status != RouteStatus.KILL
