from __future__ import annotations

from dataclasses import asdict, dataclass
import math


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


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


def conservative_eigenvalue_gap(*, M: float, rho: float) -> float:
    """Elementary lower bound for the reference eigenvalue on [0,rho*ell].

    Source facts used:
      lam >= 1/M,
      0 < u <= M,
      slotMagnitude(u,ell,v) = u/2 + u*v/ell,
      referenceEigenvalue = lam/sqrt(1 + slotMagnitude^2).

    For 0 <= v <= rho*ell and rho >= 0, slotMagnitude <= (rho+1/2)M.
    The returned positive gap is conservative and is not claimed sharp.
    """
    if M < 1:
        raise ValueError("M must be at least 1")
    if not (0 <= rho < 2):
        raise ValueError("rho must lie in [0,2) for the source-slot audit")
    smax = (rho + 0.5) * M
    return 1.0 / (M * math.sqrt(1.0 + smax * smax))


def cone_stage_threshold(*, M: float, rho: float, C: float) -> int:
    """Sufficient integer n when S=n^2 for the primary_bounds cone condition.

    GrowingMode.coneConstant(gap,C) = 4*(C+1)/gap and primary_bounds asks
    2*coneConstant <= S. Thus n^2 >= 8*(C+1)/gap is sufficient.
    """
    if C < 0:
        raise ValueError("C must be nonnegative")
    gap = conservative_eigenvalue_gap(M=M, rho=rho)
    return math.ceil(math.sqrt(8.0 * (C + 1.0) / gap))


def interval_budget_factor(*, M: float, rho: float) -> dict:
    """Source-derived slot-length budget for [0,rho*ell].

    Source gives ell <= 2*r0*Tg*S and assumes 4*r0*Tg <= M. Hence for
    rho <= 2, rho*ell <= M*S. We use the uniform primary_bounds budget K=M.
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


def enlarged_control_report(*, M: float = 2.0, u: float = 1.0, rho: float = 1.5, C: float = 1.0) -> dict:
    if not (0 < u <= M):
        raise ValueError("require 0 < u <= M")
    gap = conservative_eigenvalue_gap(M=M, rho=rho)
    threshold = cone_stage_threshold(M=M, rho=rho, C=C)
    budget = interval_budget_factor(M=M, rho=rho)

    gates = [
        ControlGate(
            gate_id="interval_inside_source_slot",
            status="PASS",
            evidence="ALGEBRAIC_FROM_SOURCE_DOMAIN",
            statement="[0,rho*ell] is contained in (-ell,2ell) for rho<2.",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.slot",
            notes=f"rho={rho}; right source-slot buffer={(2-rho):.6g}*ell.",
        ),
        ControlGate(
            gate_id="coefficient_continuity",
            status="READY_TO_FORMALIZE",
            evidence="SOURCE_JETS_PLUS_RESTRICTION",
            statement="coefficient 1 is continuous on carrier x [0,rho*ell].",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.coefficient_jets",
            notes="The source jet theorem is already on the larger open slot.",
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
            statement="Viscosity remains within D/S of the original referenceViscosity(lam,u,ell,v).",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.damping_error",
            notes="damping_error also accepts any v in the larger source slot.",
        ),
        ControlGate(
            gate_id="reference_eigenvalue_identity",
            status="SOURCE_COVERED",
            evidence="DEFINITIONAL_IN_SOURCE_CONSTRUCTION",
            statement="The frame eigenvalue is the referenceEigenvalue using the original native ell.",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.coefficientControl eigenvalue field / frame construction",
            notes="The native coefficientControl wrapper restricts time, but the underlying eigenvalue formula is not redefined at ell.",
        ),
        ControlGate(
            gate_id="positive_extended_spectral_gap",
            status="DERIVED_READY_TO_FORMALIZE",
            evidence="SOURCE_FORMULAS_PLUS_ELEMENTARY_MONOTONICITY",
            statement="A positive stage-independent lower spectral gap exists for every fixed rho<2.",
            source_file="NavierStokes/PulseGrowth.lean / ViscousPropagator.lean / BasePhaseGeometry.lean",
            source_declaration="slotMagnitude / referenceEigenvalue / FamilyData.lambda_bound",
            notes=f"Conservative gap for M={M}, rho={rho}: {gap:.12g}.",
        ),
        ControlGate(
            gate_id="primary_bounds_interval_budget",
            status="DERIVED_SOURCE_COVERED",
            evidence="SOURCE_SLOT_LENGTH_BOUND",
            statement="The longer interval obeys b-a <= M*S for every rho<2.",
            source_file="NavierStokes/ChartScales.lean / BasePhaseGeometry.lean",
            source_declaration="ChartScales.slotLength_bounds / FamilyData construction hslot assumption",
            notes=budget["inequality"],
        ),
        ControlGate(
            gate_id="large_stage_cone_condition",
            status="FINITE_ADDITIONAL_THRESHOLD",
            evidence="EXPLICIT_FROM_PRIMARY_BOUNDS",
            statement="For fixed rho,M,C, sufficiently large stage n satisfies 2*coneConstant(gap,C) <= S=n^2.",
            source_file="NavierStokes/GrowingMode.lean / PrimaryODE.lean",
            source_declaration="GrowingMode.coneConstant / PrimaryODE.primary_bounds",
            notes=f"Illustrative sufficient n >= {threshold} for M={M}, rho={rho}, C={C}. C is an input here, not silently identified with the source modalConstant.",
        ),
        ControlGate(
            gate_id="reference_envelope_differential_identity",
            status="SOURCE_REPLAYABLE",
            evidence="SOURCE_GENERIC_IDENTITY",
            statement="The exact reference envelope solves the required scalar differential equation on the enlarged interval once eigenvalue identity is inserted.",
            source_file="NavierStokes/ViscousPropagator.lean / PrimaryODE.lean",
            source_declaration="hasDerivAt_envelope / PrimaryODE.primary_bounds",
            notes="This is control relative to the exact reference envelope, not yet a simple Gaussian sandwich beyond ell.",
        ),
        ControlGate(
            gate_id="extended_reference_envelope_primary_bounds",
            status="READY_AFTER_FORMAL_WRAPPERS",
            evidence="GENERIC_SOURCE_THEOREM",
            statement="PrimaryODE.primary_bounds can be replayed on [0,rho*ell] with the original reference envelope and a larger interval budget.",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.primary_bounds",
            notes="The generic theorem separates interval endpoints a,b from its dimensionless length-budget constant.",
        ),
        ControlGate(
            gate_id="simple_gaussian_sandwich_beyond_native_ell",
            status="OPEN_NEW_SCALAR_LEMMA",
            evidence="NOT_IN_READY_MADE_SOURCE_THEOREM",
            statement="Convert the exact reference-envelope control on [0,rho*ell] into explicit exp(-c*(v-ell/2)^2/ell) upper/lower bounds.",
            source_file="NavierStokes/GaussianEnvelope.lean",
            source_declaration="reference_uniform_gaussian_bounds",
            notes="The published ready-made Gaussian sandwich is scoped to v in [0,ell]. A rho>1 version must be proved rather than assumed.",
        ),
    ]

    return {
        "schema": "enlarged-primary-control-v1",
        "source_lock": {"repository": "openai/NavierStokesAndEuler", "commit": SOURCE_COMMIT},
        "parameters": {"M": M, "u": u, "rho": rho, "C_probe": C},
        "derived": {
            "conservative_reference_eigenvalue_gap": gap,
            "illustrative_cone_stage_threshold_n": threshold,
            "uniform_primary_bounds_length_budget": M,
        },
        "gates": [g.to_dict() for g in gates],
        "scientific_update": (
            "The generic primary bound appears structurally compatible with any fixed one-sided rho<2 after direct "
            "reuse of slot-level error/viscosity estimates and a rho-dependent positive spectral gap. The source's "
            "native CoefficientControl wrapper is narrower than the underlying hypotheses. The remaining quantitative "
            "novelty is chiefly formal wrapper replay plus an explicit Gaussian sandwich beyond the native ell interval."
        ),
        "claim_boundary": (
            "No rho>1 primary bound has been Lean-checked here. The numeric stage threshold is illustrative because C "
            "is supplied as a probe rather than instantiated with the full source modalConstant. The report does not "
            "claim an extended Gaussian sandwich, full residual closure, force reduction, or unforced blowup."
        ),
    }
