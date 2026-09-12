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

    The modal continuation and ambient reconstruction are intentionally split.
    PrimaryODE.primary_hasDerivAt needs coefficient continuity, while FrameData
    kinematics is needed later to reconstruct the projected ambient equation.
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
            source_declaration="PrimaryODE.primary_hasDerivAt",
            consequence="Within the native interval, the modal primary follows the homogeneous coefficient ODE.",
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
            gate_id="one_sided_coefficient_continuity",
            question="Can source coefficient jets be restricted to carrier x [0,3L/2]?",
            status="READY_TO_FORMALIZE",
            evidence="SOURCE_PROOF_GENERALIZATION",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.coefficient_jets",
            consequence=(
                "This is sufficient to instantiate and differentiate the longer modal primary. Kinematics is not "
                "needed yet."
            ),
        ),
        ExtensionGate(
            gate_id="one_sided_modal_primary",
            question="Can PrimaryODE.primary be instantiated with the same t=0 seed on [0,3L/2]?",
            status="READY_AFTER_CONTINUITY",
            evidence="SOURCE_GENERIC_CONSTRUCTION",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.primary / PrimaryODE.primary_hasDerivAt",
            consequence=(
                "The generic primary construction accepts any ordered finite interval. Once coefficient continuity "
                "is available, primary_hasDerivAt certifies homogeneous modal dynamics on the enlarged interval."
            ),
        ),
        ExtensionGate(
            gate_id="agreement_with_native_primary",
            question="Does the enlarged modal primary equal the native primary on [0,L]?",
            status="READY_AFTER_MODAL_CONSTRUCTION",
            evidence="SOURCE_LIBRARY_THEOREM",
            source_file="NavierStokes/TangentODE.lean",
            source_declaration="TangentODE.linear_solution_unique",
            consequence="Both have the same t=0 seed and solve the same homogeneous modal ODE on [0,L].",
        ),
        ExtensionGate(
            gate_id="one_sided_kinematics_wrapper",
            question="Can FrameData.Kinematics be generalized from [0,L] to [0,3L/2]?",
            status="READY_TO_FORMALIZE",
            evidence="SOURCE_PROOF_GENERALIZATION",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="FamilyData.kinematics / normal_nonzero",
            consequence=(
                "This is required for ambient projected reconstruction, but no longer blocks construction of the "
                "modal homogeneous extension itself."
            ),
        ),
        ExtensionGate(
            gate_id="ambient_projected_equation",
            question="Does the enlarged modal primary reconstruct to the projected ambient equation on [0,3L/2]?",
            status="READY_AFTER_KINEMATICS",
            evidence="SOURCE_GENERIC_CONSTRUCTION",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.ambientSolution_hasDerivAt",
            consequence="A generalized kinematics wrapper upgrades the modal continuation into an ambient projected trajectory.",
        ),
        ExtensionGate(
            gate_id="uncut_principal_error_on_enlarged_interval",
            question="If psi=1 and the principal solve identity holds on the enlarged interval, does excludedSlotError vanish there?",
            status="READY_AFTER_AMBIENT_RECONSTRUCTION",
            evidence="ALGEBRAIC_PLUS_SOURCE_IDENTITY",
            source_file="NavierStokes/LinearWaveBounds.lean",
            source_declaration="LinearWaveBounds.excludedSlotError / principal_cutoff_of_solve",
            consequence="The principal localization error then vanishes on the enlarged interval, not just on the native slot.",
        ),
        ExtensionGate(
            gate_id="constructed_good_after_psi_one",
            question="What remains in constructedGood after the localization channel is erased?",
            status="OPEN",
            evidence="SOURCE_IDENTITY_KNOWN_VALUE_NOT_RECOMPUTED",
            source_file="NavierStokes/PrimaryResidualClass.lean",
            source_declaration="PrimaryResidualClass.Inputs.linear_identity",
            consequence=(
                "The exact residual identity leaves mode(constructedGood). Its curl-principal and corrected-remainder "
                "pieces must be recomputed for the uncut enlarged pulse."
            ),
        ),
        ExtensionGate(
            gate_id="uncut_full_pde_residual_after_extension",
            question="Do all remaining wave/PDE residual channels close after the longer pulse replaces the cutoff?",
            status="OPEN",
            evidence="NOT_YET_EVALUATED",
            source_file="",
            source_declaration="",
            consequence="Only after constructedGood and later nonlinear channels are resolved can two-pulse work begin.",
        ),
    ]

    active_statuses = {
        "READY_TO_FORMALIZE",
        "READY_AFTER_CONTINUITY",
        "READY_AFTER_MODAL_CONSTRUCTION",
        "READY_AFTER_KINEMATICS",
        "READY_AFTER_AMBIENT_RECONSTRUCTION",
        "OPEN",
    }
    unresolved = [g for g in gates if g.status in active_statuses]
    return {
        "schema": "one-pulse-extension-audit-v3",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "gates": [g.to_dict() for g in gates],
        "killed_lineages": [g.to_dict() for g in gates if g.status == "KILL"],
        "first_active_gate": unresolved[0].to_dict(),
        "enlarged_interval": enlarged,
        "scientific_result": (
            "The clamped-tail lineage is killed, but the source geometry supports a sharper continuation test. "
            "Coefficient continuity alone is enough to build a same-seed modal primary on [0,3L/2]; kinematics is "
            "a later ambient-reconstruction gate. This reduces the first formal task to a compact restriction of the "
            "already source-proved coefficient jets."
        ),
        "next_candidate": {
            "name": "one-sided enlarged homogeneous primary",
            "interval": "[0, 3L/2]",
            "construction": [
                "Lean-check coefficient continuity on carrier x [0,3L/2] from coefficient_jets on (-L,2L)",
                "instantiate PrimaryODE.primary on [0,3L/2] with the unchanged t=0 primarySeed",
                "certify homogeneous modal dynamics with PrimaryODE.primary_hasDerivAt",
                "prove equality with the native primary on [0,L] via TangentODE.linear_solution_unique",
                "Lean-check FrameData.Kinematics on [0,3L/2]",
                "reconstruct the ambient projected equation",
                "set temporal cutoff to one and recompute constructedGood",
                "only then inspect nonlinear and two-pulse channels",
            ],
            "kill_if": [
                "the coefficient-continuity restriction fails despite compact containment in (-L,2L)",
                "the same-seed enlarged modal primary cannot be certified on [0,3L/2]",
                "native-slot uniqueness fails because the two candidates do not actually solve the same modal ODE",
                "ambient kinematics or a later residual channel fails structurally beyond L",
            ],
        },
        "hard_nonclaims": {
            "enlarged_coefficient_continuity_lean_checked": False,
            "enlarged_modal_primary_lean_checked": False,
            "generalized_kinematics_lean_checked": False,
            "enlarged_homogeneous_extension_constructed": False,
            "cutoff_can_be_removed_from_full_construction": False,
            "actual_forcing_reduced": False,
            "unforced_blowup_proved": False,
        },
    }
