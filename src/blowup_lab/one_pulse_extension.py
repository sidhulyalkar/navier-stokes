from __future__ import annotations

from dataclasses import asdict, dataclass


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

    The key distinction is between an object being defined outside its native
    interval and the ODE identity being proved there. PrimaryODE.solution uses
    a differentiable extension of a finite-interval Volterra solution, while
    solution_hasDerivAt establishes the equation only on Icc a b.
    """
    gates = [
        ExtensionGate(
            gate_id="function_defined_on_R",
            question="Is the source primary represented by a function on all real slot times?",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.solution / PrimaryODE.extendedFamily",
            consequence="The differentiable extension is an R -> State object.",
        ),
        ExtensionGate(
            gate_id="agrees_with_volterra_on_native_interval",
            question="Does the extension equal the actual Volterra solution on [a,b]?",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.extendedFamily_eq_path",
            consequence="Inside Icc(a,b), the extended object is the constructed finite-interval solution.",
        ),
        ExtensionGate(
            gate_id="homogeneous_ode_on_native_interval",
            question="For the canonical primary with zero physical forcing, is the ODE identity proved on [a,b]?",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.solution_hasDerivAt + FrameData.forcing_zero",
            consequence="Within the native interval, the primary follows the homogeneous coefficient ODE.",
        ),
        ExtensionGate(
            gate_id="homogeneous_ode_outside_native_interval",
            question="Does the source prove that the differentiable extension satisfies the same ODE outside [a,b]?",
            status="OPEN",
            evidence="SOURCE_SCOPE_OBSTRUCTION",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.solution_hasDerivAt",
            consequence=(
                "The theorem carries hv : v in Icc(a,b). Merely deleting the cutoff and reusing solutionExtension "
                "does not source-justify homogeneous dynamics in neighboring time regions."
            ),
        ),
        ExtensionGate(
            gate_id="uncut_principal_error_on_native_interval",
            question="If psi=1 and the solve identity holds, does excludedSlotError vanish on the native interval?",
            status="PASS",
            evidence="ALGEBRAIC_PLUS_SOURCE_IDENTITY",
            source_file="NavierStokes/LinearWaveBounds.lean",
            source_declaration="LinearWaveBounds.excludedSlotError / principal_cutoff_of_solve",
            consequence="The principal localization error vanishes locally after removing the cutoff.",
        ),
        ExtensionGate(
            gate_id="uncut_full_pde_residual_global",
            question="Does the current source establish exact global Navier-Stokes residual closure for the uncut pulse?",
            status="FAIL_NOT_ESTABLISHED",
            evidence="OPEN",
            source_file="",
            source_declaration="",
            consequence="No. Global dynamics, other residual channels, geometry, pressure and interactions remain unresolved.",
        ),
    ]

    first_blocker = next(g for g in gates if g.status in {"OPEN", "FAIL_NOT_ESTABLISHED"})
    return {
        "schema": "one-pulse-extension-audit-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "gates": [g.to_dict() for g in gates],
        "first_blocker": first_blocker.to_dict(),
        "scientific_result": (
            "The existing differentiable extension is not itself a source-backed global homogeneous continuation. "
            "The first no-cutoff task is to extend the coefficient/frame dynamics and solve the ODE on an enlarged "
            "interval, not to estimate a backward propagator for a seed that already exists."
        ),
        "next_candidate": {
            "name": "enlarged-interval homogeneous primary",
            "construction": [
                "choose [a',b'] strictly containing the original pulse interval [a,b]",
                "prove FrameData coefficient and kinematic hypotheses on [a',b']",
                "solve the homogeneous ODE directly on [a',b'] from a compatible seed",
                "prove agreement with the canonical primary on [a,b] by uniqueness",
                "only then set the temporal slot cutoff to one on the enlarged interval",
                "recompute every non-principal residual channel and support condition",
            ],
            "kill_if": [
                "frame/coefficient hypotheses genuinely fail before reaching the neighboring slot",
                "the enlarged homogeneous solution cannot match the canonical pulse on the native interval",
                "new residual or interaction terms lose the all-order smallness needed by later correction machinery",
            ],
        },
        "hard_nonclaims": {
            "global_homogeneous_extension_exists": False,
            "cutoff_can_be_removed_from_full_construction": False,
            "actual_forcing_reduced": False,
            "unforced_blowup_proved": False,
        },
    }
