from __future__ import annotations

from dataclasses import asdict, dataclass


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class NormalizedInterval:
    """Interval measured in units of the native pulse length L."""

    left: float
    right: float

    def __post_init__(self) -> None:
        if self.left > self.right:
            raise ValueError("left must not exceed right")

    def inside_source_slot(self) -> bool:
        # BasePhaseGeometry.FamilyData.slot = Ioo(-L, 2L).
        return -1.0 < self.left and self.right < 2.0

    def contains_native(self) -> bool:
        return self.left <= 0.0 and 1.0 <= self.right

    def strict_slot_buffer(self) -> float:
        return min(self.left + 1.0, 2.0 - self.right)

    def to_dict(self) -> dict:
        out = asdict(self)
        out.update(
            inside_source_slot=self.inside_source_slot(),
            contains_native=self.contains_native(),
            strict_slot_buffer=self.strict_slot_buffer(),
        )
        return out


@dataclass(frozen=True)
class Obligation:
    obligation_id: str
    statement: str
    status: str
    evidence: str
    source_file: str
    source_declaration: str
    rationale: str

    def to_dict(self) -> dict:
        return asdict(self)


def candidate_interval() -> NormalizedInterval:
    """First one-sided no-cutoff experiment: [0, 3L/2]."""
    return NormalizedInterval(0.0, 1.5)


def one_sided_factor_interval(rho: float) -> NormalizedInterval:
    """Return the normalized one-sided interval [0,rho L]."""
    if rho < 0:
        raise ValueError("rho must be nonnegative")
    return NormalizedInterval(0.0, float(rho))


def extension_factor_frontier(factors: tuple[float, ...] = (1.0, 1.25, 1.5, 1.75, 1.9, 1.99, 2.0)) -> dict:
    """Audit the source-geometry frontier for one-sided extension factors.

    At the phase/frame-domain level, any compact [0,rho L] with rho<2 is
    contained in the open source slot (-L,2L). rho=2 is deliberately rejected
    because the source slot is open at 2L.
    """
    rows = []
    for rho in factors:
        I = one_sided_factor_interval(rho)
        rows.append(
            {
                "rho": rho,
                "interval": f"[0,{rho}L]",
                "inside_source_slot": I.inside_source_slot(),
                "contains_native": I.contains_native(),
                "right_buffer_in_L_units": 2.0 - rho,
                "source_geometry_status": "ADMISSIBLE_COMPACT_SUBINTERVAL" if I.inside_source_slot() else "OUTSIDE_OR_TOUCHES_OPEN_BOUNDARY",
            }
        )
    return {
        "schema": "one-sided-extension-factor-frontier-v1",
        "source_fact": "BasePhaseGeometry.FamilyData.slot = (-L,2L)",
        "derived_family": "For L>0 and 0<=rho<2, [0,rho L] is contained in (-L,2L).",
        "native_interval_factor": 1.0,
        "first_probe_factor": 1.5,
        "source_geometric_supremum_factor": 2.0,
        "supremum_attained": False,
        "rows": rows,
        "claim_boundary": (
            "This frontier concerns only containment in the source analysis slot. It does not prove coefficient "
            "continuity, modal dynamics, kinematics, residual control, or an unforced construction at every rho."
        ),
    }


def enlarged_interval_report(interval: NormalizedInterval | None = None) -> dict:
    I = interval or candidate_interval()

    obligations = [
        Obligation(
            obligation_id="source_open_slot",
            statement="The primitive phase/frame analysis is defined on V=(-L,2L).",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="BasePhaseGeometry.FamilyData.slot",
            rationale="The source defines slot(i) := Ioo(-length(i), 2*length(i)).",
        ),
        Obligation(
            obligation_id="candidate_strictly_inside_slot",
            statement="[0,3L/2] is compactly contained in (-L,2L) for L>0.",
            status="PASS" if I.inside_source_slot() and I.contains_native() else "FAIL",
            evidence="ALGEBRAIC_DERIVED",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="BasePhaseGeometry.FamilyData.slot",
            rationale=f"Normalized interval={I.left,I.right}; strict slot buffer={I.strict_slot_buffer()}*L.",
        ),
        Obligation(
            obligation_id="coefficient_smooth_on_source_slot",
            statement="The moving-frame coefficient has polynomial jets on the open source slot domain.",
            status="PASS",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="BasePhaseGeometry.FamilyData.coefficient_jets",
            rationale=(
                "coefficient_jets is proved on D.slot a.slot isOpen_Ioo; PrimaryTargetBounds later restricts this "
                "stronger statement to Icc(0,L)."
            ),
        ),
        Obligation(
            obligation_id="coefficient_continuous_on_enlarged_interval",
            statement="Continuity of coefficient 1 on carrier x [0,3L/2].",
            status="DERIVED_READY_TO_FORMALIZE" if I.inside_source_slot() else "FAIL",
            evidence="TOPOLOGICAL_RESTRICTION_OF_SOURCE_JETS",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="BasePhaseGeometry.FamilyData.coefficient_jets",
            rationale=(
                "Smoothness on the open slot restricts to continuity on any compact subinterval contained in it. "
                "The published wrapper coefficient_continuous chooses [0,L], but the source jet theorem is wider."
            ),
        ),
        Obligation(
            obligation_id="modal_primary_on_enlarged_interval",
            statement="The same-seed modal primary can be certified on [0,3L/2] once coefficient continuity is available.",
            status="READY_ON_CONTINUITY_GATE",
            evidence="SOURCE_GENERIC_CONSTRUCTION",
            source_file="NavierStokes/PrimaryODE.lean",
            source_declaration="PrimaryODE.primary / PrimaryODE.primary_hasDerivAt",
            rationale=(
                "The generic primary accepts any ordered finite interval; primary_hasDerivAt requires coefficient "
                "continuity but not FrameData.Kinematics."
            ),
        ),
        Obligation(
            obligation_id="agreement_with_native_primary",
            statement="The enlarged modal primary equals the canonical primary on [0,L].",
            status="READY_ON_MODAL_CONSTRUCTION_GATE",
            evidence="SOURCE_LIBRARY_THEOREM",
            source_file="NavierStokes/TangentODE.lean",
            source_declaration="TangentODE.linear_solution_unique",
            rationale=(
                "Both candidates start from the same t=0 seed and satisfy the same continuous-coefficient homogeneous "
                "modal ODE on [0,L]."
            ),
        ),
        Obligation(
            obligation_id="normal_nonzero_on_enlarged_interval",
            statement="The phase normal stays nonzero on [0,3L/2].",
            status="DERIVED_READY_TO_FORMALIZE" if I.inside_source_slot() else "FAIL",
            evidence="SOURCE_THEOREM_PLUS_SET_INCLUSION",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="BasePhaseGeometry.FamilyData.normal_nonzero",
            rationale="normal_nonzero is stated for every v in the larger source slot, not only v in [0,L].",
        ),
        Obligation(
            obligation_id="kinematics_on_enlarged_interval",
            statement="FrameData.Kinematics holds on [0,3L/2].",
            status="DERIVED_READY_TO_FORMALIZE" if I.inside_source_slot() else "FAIL",
            evidence="SOURCE_PROOF_GENERALIZATION",
            source_file="NavierStokes/BasePhaseGeometry.lean",
            source_declaration="BasePhaseGeometry.FamilyData.kinematics",
            rationale=(
                "The source proof uses interval_subset_slot only to feed normal_nonzero; its other derivative and "
                "eigenvector-nonzero steps are pointwise. This is an ambient-reconstruction gate, not the first modal gate."
            ),
        ),
        Obligation(
            obligation_id="full_wave_residual_after_extension",
            statement="All non-principal residual, geometry, pressure, support and interaction channels remain controlled.",
            status="OPEN",
            evidence="NOT_YET_EVALUATED",
            source_file="",
            source_declaration="",
            rationale="This is a later gate after the enlarged modal primary is constructed and ambient reconstruction is checked.",
        ),
    ]

    blocking = [o for o in obligations if o.status in {"FAIL", "OPEN"}]
    formalization = [o for o in obligations if "READY" in o.status]

    return {
        "schema": "enlarged-primary-interval-v2",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "candidate": I.to_dict(),
        "extension_factor_frontier": extension_factor_frontier(),
        "obligations": [o.to_dict() for o in obligations],
        "formalization_queue": [o.obligation_id for o in formalization],
        "first_unresolved_after_source_reuse": blocking[0].to_dict() if blocking else None,
        "scientific_update": (
            "The source geometry supports every compact one-sided factor rho<2 at the domain level; rho=3/2 is the "
            "first conservative probe. Coefficient continuity is the first formal gate for modal continuation. "
            "Kinematics is deferred until ambient reconstruction."
        ),
        "claim_boundary": (
            "This report identifies source coverage and a proof-generalization path. It does not claim that enlarged "
            "coefficient continuity, the longer modal primary, generalized kinematics, or any full Navier-Stokes "
            "forcing removal has been Lean-checked unless the separate formal audit says so."
        ),
    }
