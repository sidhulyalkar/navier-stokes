from __future__ import annotations

from dataclasses import asdict, dataclass
import math


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
STAGE_A_FORMAL_COMMIT = "cd41ae7ca50f5cb1968010328603f226a0638a4b"
THREE_HALVES = 1.5


@dataclass(frozen=True)
class ControlGate:
    gate_id: str
    status: str
    evidence: str
    statement: str
    source_file: str
    source_declaration: str
    notes: str

    def to_dict(self) -> dict:
        return asdict(self)


def damping_denominator(u: float) -> float:
    """The source denominator (1+u^2)*sqrt(1+u^2)."""
    return (1.0 + u * u) * math.sqrt(1.0 + u * u)


def conservative_eigenvalue_gap(*, M: float, rho: float) -> float:
    """Elementary M-uniform lower bound on [0,rho*ell].

    Source facts used:
      lam >= 1/M,
      0 < u <= M,
      slotMagnitude(u,ell,v) = u/2 + u*v/ell,
      referenceEigenvalue = lam/sqrt(1 + slotMagnitude^2).

    For 0 <= v <= rho*ell, slotMagnitude <= (rho+1/2)M.  This is a
    conservative family-level bound, not the sharper fixed-(lam,u) value.
    """
    if M < 1:
        raise ValueError("M must be at least 1")
    if not (0 <= rho < 2):
        raise ValueError("rho must lie in [0,2) for the source-slot audit")
    smax = (rho + 0.5) * M
    return 1.0 / (M * math.sqrt(1.0 + smax * smax))


def three_halves_eigenvalue_gap(*, lam: float, u: float) -> float:
    """Sharp elementary lower gap produced by the 3/2 interval audit.

    On 0 <= v <= 3*ell/2, slotMagnitude lies in [u/2, 2u]. Therefore
    referenceEigenvalue(lam,u,ell,v) >= lam/sqrt(1+(2u)^2).
    """
    if lam <= 0:
        raise ValueError("lam must be positive")
    if u < 0:
        raise ValueError("u must be nonnegative")
    return lam / math.sqrt(1.0 + 4.0 * u * u)


def reference_min_slope(*, lam: float, u: float) -> float:
    """OpenAI's native positive lower magnitude for d/ds reference rate."""
    if lam <= 0 or u <= 0:
        raise ValueError("lam and u must be positive")
    return lam * u / damping_denominator(u)


def three_halves_reference_max_slope(*, lam: float, u: float) -> float:
    """Conservative |d/ds reference-rate| upper constant for s in [u/2,2u].

    The source native proof on [u/2,3u/2] bounds its two positive pieces by
    3*lam*u/2 and 3*lam*u/denom(u). Replaying the same inequalities at the
    enlarged endpoint s<=2u gives 2*lam*u and 4*lam*u/denom(u).
    """
    if lam <= 0 or u <= 0:
        raise ValueError("lam and u must be positive")
    return 2.0 * lam * u + 4.0 * lam * u / damping_denominator(u)


def three_halves_gaussian_constants(*, lam: float, u: float) -> dict:
    """Candidate scalar Gaussian constants for the Stage-C Lean theorem.

    If the replayed derivative bound is formalized, the exact reference
    envelope on [0,3ell/2] obeys

      exp(-C*(t-ell/2)^2/ell) <= P(t)
      P(t) <= exp(-c*(t-ell/2)^2/ell),

    with c = u*minSlope/2 and C = u*maxSlopeThreeHalves/2.
    """
    min_slope = reference_min_slope(lam=lam, u=u)
    max_slope = three_halves_reference_max_slope(lam=lam, u=u)
    return {
        "c": u * min_slope / 2.0,
        "C": u * max_slope / 2.0,
        "reference_min_slope": min_slope,
        "reference_max_slope_three_halves": max_slope,
    }


def cone_stage_threshold(*, M: float, rho: float, C: float) -> int:
    """Sufficient integer n when S=n^2 for the family-level cone condition."""
    if C < 0:
        raise ValueError("C must be nonnegative")
    gap = conservative_eigenvalue_gap(M=M, rho=rho)
    return math.ceil(math.sqrt(8.0 * (C + 1.0) / gap))


def three_halves_cone_stage_threshold(*, lam: float, u: float, C: float) -> int:
    """Fixed-parameter sufficient n for 2*coneConstant(gap,C)<=S=n^2."""
    if C < 0:
        raise ValueError("C must be nonnegative")
    gap = three_halves_eigenvalue_gap(lam=lam, u=u)
    return math.ceil(math.sqrt(8.0 * (C + 1.0) / gap))


def interval_budget_factor(*, M: float, rho: float) -> dict:
    """Source-derived slot-length budget for [0,rho*ell].

    Source gives ell <= 2*r0*Tg*S and assumes 4*r0*Tg <= M. Hence for
    rho <= 2, rho*ell <= M*S. We use the uniform primary_bounds budget M.
    """
    if M < 0:
        raise ValueError("M must be nonnegative")
    if not (0 <= rho <= 2):
        raise ValueError("rho must lie in [0,2]")
    return {
        "rho": rho,
        "primary_bounds_length_budget": M,
        "inequality": "rho*ell <= rho*(2*r0*Tg)*S <= (4*r0*Tg)*S <= M*S",
        "valid_from_source_assumptions": True,
    }


def enlarged_control_report(
    *, M: float = 2.0, u: float = 1.0, rho: float = THREE_HALVES,
    C: float = 1.0, lam_probe: float | None = None,
) -> dict:
    if not (0 < u <= M):
        raise ValueError("require 0 < u <= M")
    gap = conservative_eigenvalue_gap(M=M, rho=rho)
    threshold = cone_stage_threshold(M=M, rho=rho, C=C)
    budget = interval_budget_factor(M=M, rho=rho)
    is_three_halves = math.isclose(rho, THREE_HALVES, rel_tol=0.0, abs_tol=1e-12)
    lam = lam_probe if lam_probe is not None else 1.0 / M
    exact_three_halves = None
    if is_three_halves:
        exact_gap = three_halves_eigenvalue_gap(lam=lam, u=u)
        exact_three_halves = {
            "lam_probe": lam,
            "gap": exact_gap,
            "cone_stage_threshold_n": three_halves_cone_stage_threshold(lam=lam, u=u, C=C),
            "gaussian_constants": three_halves_gaussian_constants(lam=lam, u=u),
            "slot_magnitude_interval": [u / 2.0, 2.0 * u],
        }

    continuity_status = "FORMALIZED_SOURCE_LOCKED" if is_three_halves else "DERIVED_READY_TO_FORMALIZE"
    continuity_evidence = "LEAN_SOURCE_AUDIT" if is_three_halves else "SOURCE_JETS_PLUS_RESTRICTION"

    gates = [
        ControlGate(
            gate_id="interval_inside_source_slot",
            status="FORMALIZED_SOURCE_LOCKED" if is_three_halves else "PASS",
            evidence="LEAN_SOURCE_AUDIT" if is_three_halves else "ALGEBRAIC_FROM_SOURCE_DOMAIN",
            statement="[0,rho*ell] is contained in (-ell,2ell) for rho<2.",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.slot",
            notes=(
                f"rho={rho}; right source-slot buffer={(2-rho):.6g}*ell. "
                + (f"rho=3/2 checked at lab commit {STAGE_A_FORMAL_COMMIT}." if is_three_halves else "")
            ),
        ),
        ControlGate(
            gate_id="coefficient_continuity",
            status=continuity_status,
            evidence=continuity_evidence,
            statement="coefficient 1 is continuous on carrier x [0,rho*ell].",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.coefficient_jets",
            notes=(
                f"The source jet theorem is on the larger open slot. rho=3/2 was Lean-checked at {STAGE_A_FORMAL_COMMIT}."
                if is_three_halves else "The rho-generic restriction has not been Lean-checked."
            ),
        ),
        ControlGate(
            gate_id="enlarged_modal_primary",
            status="FORMAL_AUDIT_PENDING" if is_three_halves else "NOT_SCHEDULED",
            evidence="UPSTREAM_PRIMARY_CONSTRUCTOR",
            statement="Instantiate PrimaryODE.primary from the unchanged t=0 seed on [0,3ell/2].",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.primary / primary_hasDerivAt / TangentODE.linear_solution_unique",
            notes="Stage B is committed but remains unpromoted until the source-locked Lean audit is green.",
        ),
        ControlGate(
            gate_id="modal_error_bounds",
            status="SOURCE_COVERED",
            evidence="SOURCE_EXACT_ON_OPEN_SLOT",
            statement="All four modal errors retain C/S-type bounds on the enlarged interval.",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.modal_errors",
            notes="modal_errors accepts any v in the larger source slot.",
        ),
        ControlGate(
            gate_id="viscosity_reference_error",
            status="SOURCE_COVERED",
            evidence="SOURCE_EXACT_ON_OPEN_SLOT",
            statement="Viscosity remains within D/S of referenceViscosity(lam,u,ell,v).",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.damping_error",
            notes="damping_error also accepts any v in the larger source slot.",
        ),
        ControlGate(
            gate_id="reference_eigenvalue_identity",
            status="SOURCE_COVERED",
            evidence="DEFINITIONAL_IN_SOURCE_CONSTRUCTION",
            statement="The frame eigenvalue uses referenceEigenvalue with the original native ell for all slot times.",
            source_file="NavierStokes/PhaseJetBounds.lean / BasePhaseGeometry.lean",
            source_declaration="PhaseFamily.frameData / FamilyData.frame",
            notes="The native CoefficientControl wrapper is narrower than the underlying definition.",
        ),
        ControlGate(
            gate_id="positive_extended_spectral_gap",
            status="DERIVED_READY_TO_FORMALIZE",
            evidence="SOURCE_FORMULAS_PLUS_ELEMENTARY_MONOTONICITY",
            statement="A positive stage-independent lower spectral gap exists for every fixed rho<2.",
            source_file="NavierStokes/PulseGrowth.lean / ViscousPropagator.lean / BasePhaseGeometry.lean",
            source_declaration="slotMagnitude / referenceEigenvalue / FamilyData.lambda_bound",
            notes=(
                f"Family conservative gap={gap:.12g}. "
                + (f"At rho=3/2 and lam={lam:.6g}, exact source-form gap={exact_three_halves['gap']:.12g}." if exact_three_halves else "")
            ),
        ),
        ControlGate(
            gate_id="primary_bounds_interval_budget",
            status="DERIVED_SOURCE_COVERED",
            evidence="SOURCE_SLOT_LENGTH_BOUND",
            statement="The longer interval obeys b-a <= M*S for every rho<2.",
            source_file="NavierStokes/ChartScales.lean / BasePhaseGeometry.lean",
            source_declaration="ChartScales.slotLength_bounds / FamilyData hslot assumption",
            notes=budget["inequality"],
        ),
        ControlGate(
            gate_id="large_stage_cone_condition",
            status="EXPLICIT_ADDITIONAL_HYPOTHESIS",
            evidence="EXPLICIT_FROM_PRIMARY_BOUNDS",
            statement="The enlarged spectral gap requires 2*coneConstant(gap,C) <= S; native LargeBand does not encode this condition.",
            source_file="NavierStokes/GrowingMode.lean / PrimaryODE.lean / BasePhaseGeometry.lean",
            source_declaration="GrowingMode.coneConstant / PrimaryODE.primary_bounds / LargeBand",
            notes=f"Illustrative family-level sufficient n >= {threshold} for M={M}, rho={rho}, C={C}.",
        ),
        ControlGate(
            gate_id="reference_envelope_differential_identity",
            status="SOURCE_REPLAYABLE",
            evidence="SOURCE_GENERIC_IDENTITY",
            statement="The exact reference envelope solves the scalar rate equation globally in slot time.",
            source_file="NavierStokes/PrimaryPulseBounds.lean / ViscousPropagator.lean",
            source_declaration="referenceP_hasDerivAt / reference_rate_split",
            notes="This is exact reference-envelope control, not yet the extended Gaussian sandwich theorem.",
        ),
        ControlGate(
            gate_id="extended_reference_envelope_primary_bounds",
            status="READY_AFTER_STAGE_B_AND_CONE",
            evidence="GENERIC_SOURCE_THEOREM",
            statement="PrimaryODE.primary_bounds can be replayed on [0,rho*ell] without changing the native reference ell.",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.primary_bounds",
            notes="The theorem separates interval endpoints a,b from its scale-budget constant.",
        ),
        ControlGate(
            gate_id="simple_gaussian_sandwich_beyond_native_ell",
            status="DERIVED_READY_TO_FORMALIZE" if is_three_halves else "OPEN_NEW_SCALAR_LEMMA",
            evidence="SOURCE_PROOF_REPLAY" if is_three_halves else "NOT_IN_READY_MADE_SOURCE_THEOREM",
            statement="Convert exact reference-envelope control into explicit Gaussian upper/lower bounds beyond ell.",
            source_file="NavierStokes/GaussianEnvelope.lean",
            source_declaration="referenceSlope_bounds / gaussian_envelope_bounds",
            notes=(
                "For rho=3/2, slotMagnitude lies in [u/2,2u]. The source proof replays with the same min slope and "
                "max slope 2*lam*u + 4*lam*u/dampingDenominator(u). This has not yet been Lean-checked."
                if is_three_halves else "A rho-specific slope interval and constants must be derived."
            ),
        ),
    ]

    return {
        "schema": "enlarged-primary-control-v2",
        "source_lock": {"repository": "openai/NavierStokesAndEuler", "commit": SOURCE_COMMIT},
        "formal_evidence": {"stage_a_lab_commit": STAGE_A_FORMAL_COMMIT},
        "parameters": {"M": M, "u": u, "rho": rho, "C_probe": C},
        "derived": {
            "conservative_reference_eigenvalue_gap": gap,
            "illustrative_cone_stage_threshold_n": threshold,
            "uniform_primary_bounds_length_budget": M,
            "three_halves": exact_three_halves,
        },
        "gates": [g.to_dict() for g in gates],
        "scientific_update": (
            "At rho=3/2, interval containment and coefficient continuity are formally checked against the pinned source. "
            "The next quantitative layer is structurally a replay of generic PrimaryODE.primary_bounds with wider-slot "
            "modal/viscosity estimates, an explicit enlarged-gap cone hypothesis, and a new scalar Gaussian sandwich."
        ),
        "claim_boundary": (
            "Stage B remains pending until its source-locked Lean audit passes. No rho>1 primary_bounds theorem or "
            "extended Gaussian sandwich is yet claimed formal. Numeric thresholds using C_probe are illustrative. "
            "No full residual closure, force reduction, or unforced blowup is claimed."
        ),
    }
