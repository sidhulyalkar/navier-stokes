from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


class Evidence(str, Enum):
    SOURCE_EXACT = "SOURCE_EXACT"
    ALGEBRAIC_DERIVED = "ALGEBRAIC_DERIVED"
    SOURCE_BOUND = "SOURCE_BOUND"
    OPEN = "OPEN"


@dataclass(frozen=True)
class ResidualAtom:
    atom_id: str
    expression: str
    mechanism: str
    support: str
    evidence: Evidence
    source_file: str
    source_declaration: str
    asymptotic_status: str
    disappears_if: tuple[str, ...]
    warning: str = ""

    def to_dict(self) -> dict:
        out = asdict(self)
        out["evidence"] = self.evidence.value
        return out


@dataclass(frozen=True)
class CutoffScenario:
    name: str
    source_zero: bool = False
    cutoff_identically_one: bool = False
    cutoff_identically_zero: bool = False
    product_cutoff: bool = False

    def __post_init__(self) -> None:
        if self.cutoff_identically_one and self.cutoff_identically_zero:
            raise ValueError("cutoff cannot be identically one and zero")
        if self.product_cutoff and (self.cutoff_identically_one or self.cutoff_identically_zero):
            raise ValueError("product decomposition is for a nonconstant cutoff")


def source_identity() -> dict:
    return {
        "source_file": "NavierStokes/LinearWaveBounds.lean",
        "source_declaration": "LinearWaveBounds.excludedSlotError",
        "identity": "excludedSlotError = Dfast(psi) * amplitude + (1-psi) * source",
        "solve_identity": (
            "If principal(amplitude,pressure) = -source, then principal(withCutoff(psi)) + source = excludedSlotError."
        ),
        "source_commit": SOURCE_COMMIT,
    }


def base_atoms(*, source_zero: bool) -> list[ResidualAtom]:
    atoms = [
        ResidualAtom(
            atom_id="cutoff.fast_derivative",
            expression="Dfast(psi) * amplitude",
            mechanism="temporal/fast cutoff commutator",
            support="where Dfast(psi) != 0",
            evidence=Evidence.SOURCE_EXACT,
            source_file="NavierStokes/LinearWaveBounds.lean",
            source_declaration="LinearWaveBounds.excludedSlotError",
            asymptotic_status=(
                "Gaussian-flat for the source slot cutoff after applying the GaussianTailFlat bounds"
            ),
            disappears_if=("psi is constant", "amplitude is zero"),
            warning="Smallness is not equality to zero.",
        )
    ]
    if not source_zero:
        atoms.append(
            ResidualAtom(
                atom_id="cutoff.uncovered_source",
                expression="(1-psi) * source",
                mechanism="source exposed where cutoff is not one",
                support="where psi != 1 and source != 0",
                evidence=Evidence.SOURCE_EXACT,
                source_file="NavierStokes/LinearWaveBounds.lean",
                source_declaration="LinearWaveBounds.excludedSlotError",
                asymptotic_status="depends on source support and source-tail estimates",
                disappears_if=("psi == 1", "source == 0"),
                warning="Present for source-driven particular solves; absent in the primary residual class where source=0.",
            )
        )
    return atoms


def product_cutoff_atoms(*, source_zero: bool) -> list[ResidualAtom]:
    """Expand psi = chi_clock * chi_slot using the exact product rule."""
    atoms = [
        ResidualAtom(
            atom_id="cutoff.clock_derivative",
            expression="Dfast(chi_clock) * chi_slot * amplitude",
            mechanism="padded native-clock localization commutator",
            support="transition region of chi_clock intersect support of chi_slot",
            evidence=Evidence.ALGEBRAIC_DERIVED,
            source_file="NavierStokes/ActualGaussianCoverage.lean",
            source_declaration="ActualGaussianCoverage.nativeCutoff",
            asymptotic_status="requires the actual clock-window tail/support bound",
            disappears_if=("chi_clock is constant", "amplitude is zero"),
        ),
        ResidualAtom(
            atom_id="cutoff.slot_derivative",
            expression="chi_clock * Dfast(chi_slot) * amplitude",
            mechanism="Gaussian slot localization commutator",
            support="L/5 <= |v-L/2| <= L/3, additionally inside chi_clock support",
            evidence=Evidence.SOURCE_BOUND,
            source_file="NavierStokes/GaussianTailFlat.lean",
            source_declaration="GaussianTailFlat.slotCutoff_deriv_support",
            asymptotic_status="Gaussian-small; source proves absorption by every fixed power of Q after stage scaling",
            disappears_if=("chi_slot is constant", "amplitude is zero"),
        ),
    ]
    if not source_zero:
        atoms.append(
            ResidualAtom(
                atom_id="cutoff.product_uncovered_source",
                expression="(1-chi_clock*chi_slot) * source",
                mechanism="source exposure under product localization",
                support="where native product cutoff is not one and source != 0",
                evidence=Evidence.ALGEBRAIC_DERIVED,
                source_file="NavierStokes/ActualGaussianCoverage.lean",
                source_declaration="ActualGaussianCoverage.nativeCutoff",
                asymptotic_status="must be controlled from actual source support; not erased by Gaussian rhetoric",
                disappears_if=("chi_clock*chi_slot == 1", "source == 0"),
            )
        )
    return atoms


def clamped_tail_residual() -> ResidualAtom:
    """Residual exposed by naively setting psi=1 while reusing the source clamp.

    PrimaryPulseBounds.canonicalPrimaryPulse uses ParametricODE.extend for its
    uncut components, so outside the native interval the reused tail is clamped
    to an endpoint value. A constant tail has derivative zero. If the target is
    the homogeneous ODE x'=A(v)x, its off-slot defect is therefore -A(v)x_end.
    """
    return ResidualAtom(
        atom_id="uncut.clamped_endpoint_dynamics",
        expression="-A(v) * x_endpoint",
        mechanism="naive reuse of the continuously clamped finite-interval primary after deleting temporal cutoff",
        support="off the native ODE interval wherever the clamped endpoint value is reused",
        evidence=Evidence.ALGEBRAIC_DERIVED,
        source_file="NavierStokes/PrimaryPulseBounds.lean",
        source_declaration="PrimaryPulseBounds.canonicalPrimaryPulse",
        asymptotic_status="no Gaussian-small conclusion follows from clamping alone",
        disappears_if=("A(v) * x_endpoint == 0", "replace clamp by a genuine homogeneous continuation"),
        warning=(
            "This atom is the defect relative to the desired homogeneous ODE, not a claim that the source asserts "
            "an off-slot ODE. The source deliberately uses clamping only for continuous extension."
        ),
    )


def evaluate_scenario(scenario: CutoffScenario) -> dict:
    if scenario.cutoff_identically_one:
        atoms: list[ResidualAtom] = []
        local_result = "excludedSlotError = 0"
        caveat = (
            "This is only the principal cutoff identity. It is valid where the uncut coefficient is defined and "
            "satisfies principal = -source. It does not establish global PDE residual closure."
        )
    elif scenario.cutoff_identically_zero:
        atoms = [] if scenario.source_zero else [
            ResidualAtom(
                atom_id="cutoff.full_source_exposure",
                expression="source",
                mechanism="zero cutoff exposes the entire source term",
                support="support(source)",
                evidence=Evidence.ALGEBRAIC_DERIVED,
                source_file="NavierStokes/LinearWaveBounds.lean",
                source_declaration="LinearWaveBounds.excludedSlotError",
                asymptotic_status="inherits source behavior",
                disappears_if=("source == 0",),
            )
        ]
        local_result = "excludedSlotError = 0" if scenario.source_zero else "excludedSlotError = source"
        caveat = "The amplitude itself is removed by the zero cutoff."
    elif scenario.product_cutoff:
        atoms = product_cutoff_atoms(source_zero=scenario.source_zero)
        local_result = "product-rule decomposition"
        caveat = "The product decomposition is algebraic; each support/asymptotic claim has its own evidence level."
    else:
        atoms = base_atoms(source_zero=scenario.source_zero)
        local_result = "source exact two-channel decomposition"
        caveat = "No global extension is implied."

    return {
        "scenario": asdict(scenario),
        "local_result": local_result,
        "atoms": [atom.to_dict() for atom in atoms],
        "atom_count": len(atoms),
        "caveat": caveat,
    }


def cutoff_residual_atlas() -> dict:
    scenarios = [
        CutoffScenario("general_source_driven"),
        CutoffScenario("primary_source_zero", source_zero=True),
        CutoffScenario("actual_product_cutoff", product_cutoff=True),
        CutoffScenario("actual_product_primary", source_zero=True, product_cutoff=True),
        CutoffScenario("uncut_general", cutoff_identically_one=True),
        CutoffScenario("uncut_primary", source_zero=True, cutoff_identically_one=True),
    ]
    evaluated = [evaluate_scenario(s) for s in scenarios]
    clamp_atom = clamped_tail_residual()
    return {
        "schema": "cutoff-residual-atlas-v2",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "source_identity": source_identity(),
        "scenarios": evaluated,
        "naive_uncut_clamped_reuse": {
            "status": "KILL_AS_GLOBAL_HOMOGENEOUS_CANDIDATE",
            "residual_atom": clamp_atom.to_dict(),
            "reason": (
                "Deleting psi removes excludedSlotError only where the uncut solve identity holds. Reusing the "
                "source's clamped off-slot components instead produces a constant endpoint tail; relative to a "
                "homogeneous continuation its defect is -A(v)x_endpoint unless that endpoint is an equilibrium."
            ),
            "replacement": "solve the homogeneous ODE on a genuinely enlarged finite interval",
        },
        "hard_findings": {
            "general_excluded_slot_error_has_two_channels": True,
            "primary_source_zero_removes_uncovered_source_channel": True,
            "source_native_cutoff_is_product_of_clock_and_slot_localizers": True,
            "uncut_principal_localization_error_is_zero_if_global_solve_holds": True,
            "naive_reuse_of_clamped_tail_is_global_homogeneous_solution": False,
            "naive_clamped_tail_exposes_endpoint_dynamics_defect": True,
            "global_solve_for_uncut_hierarchy_established": False,
            "full_unforced_navier_stokes_residual_closed": False,
        },
        "next_experiment": {
            "name": "one-sided enlarged homogeneous primary",
            "question": (
                "Construct the same-seed homogeneous primary on [0,3L/2], using the source's wider (-L,2L) "
                "coefficient/geometry domain, and recompute all residuals after removing temporal localization."
            ),
            "kill_conditions": [
                "the generalized coefficient-continuity or kinematics wrapper cannot be proved on [0,3L/2]",
                "the enlarged solution fails to agree with the canonical primary on [0,L]",
                "an exposed non-principal residual loses the smallness/cancellation required downstream",
            ],
            "promotion_conditions": [
                "one enlarged homogeneous pulse is source-backed on [0,3L/2]",
                "agreement with the canonical pulse on [0,L] follows by finite-interval uniqueness",
                "all newly exposed non-principal residual channels are explicitly bounded or cancelled",
            ],
        },
        "claim_boundary": (
            "The atlas proves only algebraic/source identities and source-backed support bounds. psi=1 erases the "
            "excludedSlotError term locally under the solve hypothesis; it does not make the source's clamped tail "
            "homogeneous, prove a longer solution exists in the published construction, or close the complete "
            "Navier-Stokes residual."
        ),
    }
