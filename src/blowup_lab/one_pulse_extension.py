from __future__ import annotations

from dataclasses import asdict, dataclass

from .enlarged_interval import enlarged_interval_report


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class ExtensionGate:
    gate_id: str
    question: str
    status: str
    evidence: str
    source_file: str
    source_declaration: str
    consequence: str

    def to_dict(self) -> dict:
        return asdict(self)


def one_pulse_extension_audit() -> dict:
    """Audit the first no-cutoff counterfactual for one canonical primary pulse.

    v5.6 distinguishes the source's continuous clamped representation from a
    genuine enlarged homogeneous trajectory. The preferred first construction
    is one-sided, [0, 3L/2], so it retains the canonical seed at t=0 and stays
    strictly inside BasePhaseGeometry's wider source slot (-L, 2L).
    """
    enlarged = enlarged_interval_report()
    gates = [
        ExtensionGate(
            gate_id="function_defined_on_R",
            question="Is the source primary represented by a function on all real slot times?",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/PrimaryODE.lean / PrimaryPulseBounds.lean",
            source_declaration="PrimaryODE.solution / PrimaryPulseBounds.canonicalPrimaryPulse",
            consequence="A continuous/differentiable extension exists as an R-indexed object, but it is not global ODE dynamics.",
        ),
        ExtensionGate(
            gate_id="agrees_with_volterra_on_native_interval",
            question="Does the extension equal the actual Volterra solution on [0,L]?",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.extendedFamily_eq_path",
            consequence="Inside the native interval, the extended object is the constructed finite-interval solution.",
        ),
        ExtensionGate(
            gate_id="homogeneous_ode_on_native_interval",
            question="For the canonical primary with zero physical forcing, is the ODE identity proved on [0,L]?",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.solution_hasDerivAt + FrameData.forcing_zero",
            consequence="Within the native interval, the primary follows the homogeneous coefficient ODE.",
        ),
        ExtensionGate(
            gate_id="naive_clamped_tail_homogeneous",
            question="Can the source's clamped off-slot extension be reused as the homogeneous tail after psi=1?",
            status="KILL",
            evidence="ALGEBRAIC_OBSTRUCTION",
            source_file="NavierStokes/PrimaryPulseBounds.lean",
            source_declaration="PrimaryPulseBounds.canonicalPrimaryPulse",
            consequence=(
                "No. A clamped endpoint tail has derivative zero; relative to x'=A(v)x its defect is "
                "-A(v)x_endpoint unless the endpoint happens to be an equilibrium."
            ),
        ),
        ExtensionGate(
            gate_id="wider_source_slot_available",
            question="Do the primitive frame/coefficient estimates exist beyond [0,L]?",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.slot / normal_nonzero / coefficient_jets",
            consequence=(
                "Yes. The source analysis slot is (-L,2L); normal nondegeneracy and coefficient jets are established "
                "on that larger slot domain."
            ),
        ),
        ExtensionGate(
            gate_id="one_sided_kinematics_wrapper",
            question="Can the source kinematics proof be generalized from [0,L] to [0,3L/2]?",
            status="READY_TO_FORMALIZE",
            evidence="SOURCE_PROOF_GENERALIZATION",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.kinematics / normal_nonzero / coefficient_jets",
            consequence=(
                "The published proof uses [0,L] mainly through inclusion into (-L,2L). The candidate [0,3L/2] has "
                "the same inclusion with an L/2 buffer, so the wrapper has a direct proof path but is not yet Lean-checked here."
            ),
        ),
        ExtensionGate(
            gate_id="one_sided_homogeneous_solution",
            question="Can a same-seed homogeneous solution be constructed on [0,3L/2]?",
            status="READY_AFTER_WRAPPER",
            evidence="SOURCE_LIBRARY_THEOREM",
            source_file="NavierStokes/TangentODE.lean",
            source_declaration="TangentODE.exists_linear_solution",
            consequence="Finite-interval existence has no smallness restriction on interval length once coefficient continuity is available.",
        ),
        ExtensionGate(
            gate_id="agreement_with_native_primary",
            question="Will the enlarged solution agree with the canonical primary on [0,L]?",
            status="READY_AFTER_CONSTRUCTION",
            evidence="SOURCE_LIBRARY_THEOREM",
            source_file="NavierStokes/TangentODE.lean",
            source_declaration="TangentODE.linear_solution_unique",
            consequence="Same seed plus the same ODE on [0,L] gives the intended uniqueness bridge.",
        ),
        ExtensionGate(
            gate_id="uncut_principal_error_on_enlarged_interval",
            question="If psi=1 and the principal solve identity holds on the enlarged interval, does excludedSlotError vanish there?",
            status="READY_AFTER_CONSTRUCTION",
            evidence="ALGEBRAIC_PLUS_SOURCE_IDENTITY",
            source_file="NavierStokes/LinearWaveBounds.lean",
            source_declaration="LinearWaveBounds.excludedSlotError / principal_cutoff_of_solve",
            consequence="The principal localization error then vanishes on the enlarged interval, not just on the native slot.",
        ),
        ExtensionGate(
            gate_id="uncut_full_pde_residual_after_extension",
            question="Do all remaining wave/PDE residual channels close after the longer pulse replaces the cutoff?",
            status="OPEN",
            evidence="NOT_YET_EVALUATED",
            source_file="",
            source_declaration="",
            consequence="This is now the first genuinely new scientific gate after the interval wrappers and enlarged ODE are built.",
        ),
    ]

    unresolved = [g for g in gates if g.status in {"READY_TO_FORMALIZE", "READY_AFTER_WRAPPER", "READY_AFTER_CONSTRUCTION", "OPEN"}]
    return {
        "schema": "one-pulse-extension-audit-v2",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "gates": [g.to_dict() for g in gates],
        "killed_lineages": [g.to_dict() for g in gates if g.status == "KILL"],
        "first_active_gate": unresolved[0].to_dict(),
        "enlarged_interval": enlarged,
        "scientific_result": (
            "The source's clamped tail cannot serve as the desired homogeneous continuation, but the source-visible "
            "geometry does not kill a one-sided extension. BasePhaseGeometry already works on (-L,2L), so [0,3L/2] "
            "is the cheapest theorem-sized candidate. Formalize the wider kinematics/continuity wrappers, construct the "
            "same-seed solution there, prove native-slot agreement by uniqueness, then recompute the full residual."
        ),
        "next_candidate": {
            "name": "one-sided enlarged homogeneous primary",
            "interval": "[0, 3L/2]",
            "construction": [
                "derive coefficient continuity on carrier x [0,3L/2] from source coefficient_jets on (-L,2L)",
                "generalize FrameData.Kinematics to [0,3L/2] using source normal_nonzero on (-L,2L)",
                "solve the homogeneous linear ODE on [0,3L/2] from the unchanged primarySeed at t=0",
                "prove agreement with the canonical primary on [0,L] using TangentODE.linear_solution_unique",
                "replace temporal slot cutoff by one on the enlarged interval",
                "recompute every non-principal residual and support condition before testing a second pulse",
            ],
            "kill_if": [
                "the wider coefficient/kinematics wrappers fail despite compact containment in (-L,2L)",
                "the enlarged solution cannot match the canonical primary on [0,L]",
                "new residual or interaction terms lose the all-order smallness/cancellation needed downstream",
            ],
        },
        "hard_nonclaims": {
            "generalized_kinematics_lean_checked": False,
            "enlarged_homogeneous_extension_constructed": False,
            "cutoff_can_be_removed_from_full_construction": False,
            "actual_forcing_reduced": False,
            "unforced_blowup_proved": False,
        },
    }
