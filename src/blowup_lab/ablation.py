from __future__ import annotations

from dataclasses import asdict
from .models import AblationResult, RouteStatus
from .openai_reference import mechanisms


MECH = {m.id: m for m in mechanisms()}

# Fail-closed dependency rules.  A disabled mechanism is not treated as impossible
# if the route explicitly supplies a named alternative that discharges its obligation.
HARD_RULES = {
    "similarity_profile": "No singular background candidate remains.",
    "uniqueness_transfer": "No theorem-level breakdown conclusion remains.",
}

ALTERNATIVE_COVERS = {
    "initial_data_pulses": {"pulse_seeding", "temporal_cutoff"},
    "endogenous_instability_seed": {"pulse_seeding"},
    "intrinsic_annular_balance": {"annular_stress", "stress_cone"},
    "global_decay_no_cutoff": {"spatial_localization"},
    "exact_zero_residual": {"localized_force", "terminal_extension", "flat_summation"},
    "closed_form_base": {"higher_order_base", "correction_cycle"},
    "div_free_basis": {"curl_realization"},
    "cross_interaction_control": {"support_separation"},
    "intrinsic_zero_modes": {"mean_corrections", "moment_repair"},
}

FORCE_BENEFITS = {
    "pulse_seeding": "removes direct external pulse seeding",
    "spatial_localization": "removes spatial cutoff derivative contribution",
    "temporal_cutoff": "removes temporal cutoff derivative contribution and relaxes zero initial data",
    "localized_force": "targets the final residual itself",
    "terminal_extension": "becomes unnecessary if force is exactly zero",
}


def evaluate_ablation(route_id: str, disabled: list[str], alternatives: list[str] | None = None) -> AblationResult:
    alternatives = alternatives or []
    unknown = [m for m in disabled if m not in MECH]
    if unknown:
        raise KeyError(f"unknown mechanisms: {unknown}")
    coverage: set[str] = set()
    for alt in alternatives:
        coverage |= ALTERNATIVE_COVERS.get(alt, set())

    hard: list[str] = []
    open_obs: list[str] = []
    benefits: list[str] = []
    for mid in disabled:
        if mid in FORCE_BENEFITS:
            benefits.append(FORCE_BENEFITS[mid])
        if mid in coverage:
            open_obs.append(f"VERIFY alternative '{[a for a in alternatives if mid in ALTERNATIVE_COVERS.get(a,set())][0]}' actually replaces {mid}: {MECH[mid].replacement_obligation}")
        elif mid in HARD_RULES:
            hard.append(HARD_RULES[mid])
        else:
            open_obs.append(MECH[mid].replacement_obligation)

    wave_stress_still_needed = not (
        "stress_cone" in disabled
        and "annular_stress" in disabled
        and "intrinsic_annular_balance" in alternatives
    )
    if ("pulse_seeding" in disabled and wave_stress_still_needed
            and "initial_data_pulses" not in alternatives
            and "endogenous_instability_seed" not in alternatives):
        hard.append("Pulse amplitudes have no nonzero source: zero-source evolution from zero pulse data cannot realize the required covariance.")
    if "stress_cone" in disabled and "intrinsic_annular_balance" not in alternatives:
        hard.append("Leading annular stress has no internal cancellation mechanism.")
    if "correction_cycle" in disabled and "closed_form_base" not in alternatives and "exact_zero_residual" not in alternatives:
        hard.append("Residual improvement to all orders has no replacement.")
    if "localized_force" in disabled and "exact_zero_residual" not in alternatives:
        hard.append("Declaring f=0 without proving R(u,p)=0 is invalid.")

    hard = sorted(set(hard))
    open_obs = sorted(set(open_obs))
    benefits = sorted(set(benefits))

    if hard:
        status = RouteStatus.KILL
        score = float("-inf")
        rationale = "Fail-closed: at least one current proof invariant is left without a replacement mechanism."
    else:
        force_gain = len(benefits)
        score = 2.0 * force_gain - 0.65 * len(open_obs) - 0.15 * max(0, len(disabled) - force_gain)
        status = RouteStatus.PROMOTE if score >= 2.2 else RouteStatus.HOLD
        rationale = "No logical contradiction in the structural atlas; route remains conjectural until its replacement obligations are discharged."

    return AblationResult(route_id, disabled, alternatives, hard, open_obs, benefits, status, score, rationale)


def default_routes() -> list[AblationResult]:
    specs = [
        ("R0_NAIVE_FORCE_ZERO", ["pulse_seeding", "spatial_localization", "temporal_cutoff", "localized_force", "terminal_extension"], []),
        ("R1_INITIAL_DATA_PULSES", ["pulse_seeding", "temporal_cutoff"], ["initial_data_pulses"]),
        ("R2_ENDOGENOUS_SEED", ["pulse_seeding"], ["endogenous_instability_seed"]),
        ("R3_GLOBAL_NO_SPATIAL_CUTOFF", ["spatial_localization"], ["global_decay_no_cutoff"]),
        ("R4_INTRINSIC_ANNULAR_BALANCE", ["annular_stress", "stress_cone", "pulse_seeding", "amplify_then_damp"], ["intrinsic_annular_balance"]),
        ("R5_UNFORCED_SHOOTING", ["pulse_seeding", "temporal_cutoff", "spatial_localization"], ["initial_data_pulses", "global_decay_no_cutoff"]),
        ("R6_EXACT_RESIDUAL_ROUTE", ["localized_force", "terminal_extension", "flat_summation"], ["exact_zero_residual"]),
        ("R7_REMOVE_CORRECTION_CYCLE_NAIVE", ["correction_cycle"], []),
        ("R8_PROFILE_PLUS_GLOBAL", ["annular_stress", "stress_cone", "pulse_seeding", "spatial_localization", "temporal_cutoff"], ["intrinsic_annular_balance", "global_decay_no_cutoff", "initial_data_pulses"]),
    ]
    return [evaluate_ablation(*s) for s in specs]


def route_dict(r: AblationResult) -> dict:
    d = asdict(r)
    d["status"] = r.status.value
    if r.score == float("-inf"):
        d["score"] = "-inf"
    return d
