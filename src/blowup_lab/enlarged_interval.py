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
    """First one-sided no-cutoff experiment: [0, 3L/2].

    This keeps the original t=0 seed and leaves an L/2 buffer to the right
    boundary of the source analysis slot (-L, 2L).
    """
    return NormalizedInterval(0.0, 1.5)


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
                "eigenvector-nonzero steps are pointwise. Replacing that inclusion by [0,3L/2] subset (-L,2L) "
                "should yield the generalized theorem without changing the frame formulas."
            ),
        ),
        Obligation(
            obligation_id="finite_interval_homogeneous_solution",
            statement="A homogeneous linear solution exists on [0,3L/2] from the same t=0 seed.",
            status="READY_ON_CONTINUITY_GATE",
            evidence="SOURCE_LIBRARY_THEOREM",
            source_file="NavierStokes/TangentODE.lean",
            source_declaration="TangentODE.exists_linear_solution",
            rationale=(
                "The source proves existence on any finite closed interval for a continuous linear coefficient, with "
                "no smallness restriction on interval length."
            ),
        ),
        Obligation(
            obligation_id="agreement_with_native_primary",
            statement="The enlarged solution equals the canonical primary on [0,L].",
            status="READY_ON_CONSTRUCTION_GATE",
            evidence="SOURCE_LIBRARY_THEOREM",
            source_file="NavierStokes/TangentODE.lean",
            source_declaration="TangentODE.linear_solution_unique",
            rationale=(
                "Both solutions have the same t=0 seed and satisfy the same continuous-coefficient homogeneous ODE "
                "on [0,L], so finite-interval uniqueness is the intended bridge."
            ),
        ),
        Obligation(
            obligation_id="full_wave_residual_after_extension",
            statement="All non-principal residual, geometry, pressure, support and interaction channels remain controlled.",
            status="OPEN",
            evidence="NOT_YET_EVALUATED",
            source_file="",
            source_declaration="",
            rationale="This is the first gate after the enlarged primary itself is constructed and matched.",
        ),
    ]

    blocking = [o for o in obligations if o.status in {"FAIL", "OPEN"}]
    formalization = [o for o in obligations if "READY" in o.status]

    return {
        "schema": "enlarged-primary-interval-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "candidate": I.to_dict(),
        "obligations": [o.to_dict() for o in obligations],
        "formalization_queue": [o.obligation_id for o in formalization],
        "first_unresolved_after_source_reuse": blocking[0].to_dict() if blocking else None,
        "scientific_update": (
            "The source-visible geometry does not presently kill a one-sided extension to [0,3L/2]. "
            "The stronger coefficient-jet and normal-nonzero results already live on (-L,2L). The immediate task "
            "is to formalize the generalized compact-interval wrappers, construct the longer homogeneous solution, "
            "and then recompute the complete wave residual."
        ),
        "claim_boundary": (
            "This report identifies source coverage and a proof-generalization path. It does not claim that the "
            "generalized kinematics wrapper has been Lean-checked, that the enlarged primary has been constructed "
            "inside the published development, or that any full Navier-Stokes forcing has been removed."
        ),
    }
