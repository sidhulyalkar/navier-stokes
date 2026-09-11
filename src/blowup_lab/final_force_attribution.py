from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
SOURCE_REPOSITORY = "openai/NavierStokesAndEuler"


class Evidence(str, Enum):
    SOURCE_EXACT = "SOURCE_EXACT"
    SOURCE_LOCAL_EQUALITY = "SOURCE_LOCAL_EQUALITY"
    SOURCE_STRUCTURAL = "SOURCE_STRUCTURAL"
    OPEN = "OPEN"


class ForceClass(str, Enum):
    STRUCTURAL_RESIDUAL = "STRUCTURAL_RESIDUAL"
    TIME_ACTIVATION = "TIME_ACTIVATION"
    SPATIAL_LOCALIZATION = "SPATIAL_LOCALIZATION"
    PERIODIZATION = "PERIODIZATION"
    EXTENSION_ONLY = "EXTENSION_ONLY"
    UNKNOWN = "UNKNOWN"


@dataclass(frozen=True)
class ForceNode:
    node_id: str
    expression: str
    force_class: ForceClass
    source_file: str
    source_declaration: str
    evidence: Evidence
    scope: str
    support: str
    norm_status: str = "UNKNOWN"
    warning: str = ""

    def to_dict(self) -> dict:
        out = asdict(self)
        out["force_class"] = self.force_class.value
        out["evidence"] = self.evidence.value
        return out


@dataclass(frozen=True)
class ForceEdge:
    parent: str
    child: str
    relation: str
    source_file: str
    source_declaration: str
    evidence: Evidence
    scope: str
    warning: str = ""

    def to_dict(self) -> dict:
        out = asdict(self)
        out["evidence"] = self.evidence.value
        return out


def source_lock() -> dict:
    return {"repository": SOURCE_REPOSITORY, "commit": SOURCE_COMMIT}


def final_force_nodes() -> list[ForceNode]:
    """Source-backed top-level force nodes.

    These nodes deliberately stop before inventing a mechanism-level split of
    the finite-stage residual. v5.7 should expand the DAG only when an exact
    source identity or a clearly scoped local equality has been extracted.
    """

    return [
        ForceNode(
            node_id="force.final",
            expression="CandidateFromLimits.force(u,p,hu,hp,L,hlim)",
            force_class=ForceClass.STRUCTURAL_RESIDUAL,
            source_file="NavierStokes/CandidateFromLimits.lean",
            source_declaration="CandidateFromLimits.force",
            evidence=Evidence.SOURCE_EXACT,
            scope="global smooth force; exact activated-residual equality on 0 <= t < 1",
            support="zero for t <= 0 and for t >= 2; compact future-time support",
            warning=(
                "The Taylor-Borel extension makes the force globally smooth but is not a separate pre-singular "
                "forcing mechanism: on 0 <= t < 1 the force equals the activated Navier-Stokes residual exactly."
            ),
        ),
        ForceNode(
            node_id="force.activated_residual",
            expression="R(activatedVelocity(u), activatedPressure(p))",
            force_class=ForceClass.STRUCTURAL_RESIDUAL,
            source_file="NavierStokes/CandidateFromLimits.lean",
            source_declaration="CandidateFromLimits.force_eq_activated_residual",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 <= t < 1",
            support="where the activated residual is nonzero",
        ),
        ForceNode(
            node_id="activation.scaled_incoming_residual",
            expression="chi(t) * R(u,p)",
            force_class=ForceClass.TIME_ACTIVATION,
            source_file="NavierStokes/TimeLocalization.lean",
            source_declaration="TimeLocalization.activated_residual_formula",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 < t < 1",
            support="where timeSwitch != 0 and incoming residual != 0",
        ),
        ForceNode(
            node_id="activation.switch_derivative",
            expression="chi'(t) * u",
            force_class=ForceClass.TIME_ACTIVATION,
            source_file="NavierStokes/TimeLocalization.lean",
            source_declaration="TimeLocalization.activated_residual_formula",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 < t < 1",
            support="time-switch transition; absent once chi is locally constant",
        ),
        ForceNode(
            node_id="activation.advection_defect",
            expression="(chi(t)^2-chi(t)) * (u dot grad)u",
            force_class=ForceClass.TIME_ACTIVATION,
            source_file="NavierStokes/TimeLocalization.lean",
            source_declaration="TimeLocalization.activated_residual_formula",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 < t < 1",
            support="where 0 < timeSwitch < 1",
        ),
        ForceNode(
            node_id="incoming.periodic_residual",
            expression=(
                "R(MixedPeriodicAssembly.periodicVelocity(A,v), "
                "SpatialLocalization.periodicPressure(p))"
            ),
            force_class=ForceClass.PERIODIZATION,
            source_file="NavierStokes/MixedPeriodicAssembly.lean",
            source_declaration="MixedPeriodicAssembly.periodicResidual",
            evidence=Evidence.SOURCE_EXACT,
            scope="incoming field before time activation",
            support="periodic spatial domain",
        ),
        ForceNode(
            node_id="incoming.cut_residual",
            expression="R(MixedPeriodicAssembly.cutVelocity(A,v), SpatialLocalization.cutPressure(p))",
            force_class=ForceClass.SPATIAL_LOCALIZATION,
            source_file="NavierStokes/MixedPeriodicAssembly.lean",
            source_declaration="MixedPeriodicAssembly.cutResidual",
            evidence=Evidence.SOURCE_EXACT,
            scope="nonperiodized spatially cut field",
            support="spatial-cutoff support",
        ),
        ForceNode(
            node_id="incoming.original_residual",
            expression="R(MixedPeriodicAssembly.velocity(A,v), p)",
            force_class=ForceClass.STRUCTURAL_RESIDUAL,
            source_file="NavierStokes/MixedPeriodicAssembly.lean",
            source_declaration="MixedPeriodicAssembly.originalResidual",
            evidence=Evidence.SOURCE_EXACT,
            scope="uncut/unperiodized mixed field",
            support="source construction domain",
        ),
        ForceNode(
            node_id="incoming.mixed_diagonal_residual",
            expression="MixedDiagonalResidual.residual(a,q,A,B,P)",
            force_class=ForceClass.STRUCTURAL_RESIDUAL,
            source_file="NavierStokes/MixedDiagonalResidual.lean",
            source_declaration="MixedDiagonalResidual.residual_eq_originalResidual",
            evidence=Evidence.SOURCE_EXACT,
            scope="actual diagonal sums used by the witness",
            support="positive-scale preterminal domain",
            warning="This is an exact rfl identity for the corresponding diagonal sums, not yet a mechanism-level term split.",
        ),
        ForceNode(
            node_id="extension.post_singular_borel",
            expression="SpacetimeGluing.smoothExtension of tracedResidual and endpoint jets",
            force_class=ForceClass.EXTENSION_ONLY,
            source_file="NavierStokes/CandidateFromLimits.lean",
            source_declaration="CandidateFromLimits.force",
            evidence=Evidence.SOURCE_STRUCTURAL,
            scope="global continuation, especially t >= 1",
            support="compact future-time support; zero from t >= 2",
            warning="Do not attribute the pre-singular force on 0 <= t < 1 to this extension layer.",
        ),
    ]


def final_force_edges() -> list[ForceEdge]:
    return [
        ForceEdge(
            parent="force.final",
            child="force.activated_residual",
            relation="exact equality",
            source_file="NavierStokes/CandidateFromLimits.lean",
            source_declaration="CandidateFromLimits.force_eq_activated_residual",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 <= t < 1",
        ),
        ForceEdge(
            parent="force.activated_residual",
            child="activation.scaled_incoming_residual",
            relation="exact additive decomposition term",
            source_file="NavierStokes/TimeLocalization.lean",
            source_declaration="TimeLocalization.activated_residual_formula",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 < t < 1",
        ),
        ForceEdge(
            parent="force.activated_residual",
            child="activation.switch_derivative",
            relation="exact additive decomposition term",
            source_file="NavierStokes/TimeLocalization.lean",
            source_declaration="TimeLocalization.activated_residual_formula",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 < t < 1",
        ),
        ForceEdge(
            parent="force.activated_residual",
            child="activation.advection_defect",
            relation="exact additive decomposition term",
            source_file="NavierStokes/TimeLocalization.lean",
            source_declaration="TimeLocalization.activated_residual_formula",
            evidence=Evidence.SOURCE_EXACT,
            scope="0 < t < 1",
        ),
        ForceEdge(
            parent="activation.scaled_incoming_residual",
            child="incoming.periodic_residual",
            relation="incoming residual instantiated with periodic velocity/pressure in the actual witness",
            source_file="NavierStokes/MixedCandidateWitness.lean",
            source_declaration="MixedCandidateWitness.exists_candidate_witness_of_finite_stages",
            evidence=Evidence.SOURCE_STRUCTURAL,
            scope="actual candidate assembly",
        ),
        ForceEdge(
            parent="incoming.periodic_residual",
            child="incoming.cut_residual",
            relation="local eventual equality after periodization",
            source_file="NavierStokes/MixedPeriodicAssembly.lean",
            source_declaration="MixedPeriodicAssembly.periodicResidual_eventuallyEq_cut",
            evidence=Evidence.SOURCE_LOCAL_EQUALITY,
            scope="near points whose spatial coordinate lies in PeriodicLocalization.innerCube(1/4)",
            warning="This is not a global equality and does not yet quantify periodization-region force cost.",
        ),
        ForceEdge(
            parent="incoming.cut_residual",
            child="incoming.original_residual",
            relation="local eventual equality on cutoff plateau",
            source_file="NavierStokes/MixedPeriodicAssembly.lean",
            source_declaration="MixedPeriodicAssembly.cutResidual_eventuallyEq_original",
            evidence=Evidence.SOURCE_LOCAL_EQUALITY,
            scope="near points with spatial coordinate in SpatialLocalization.plateau",
            warning="Outside the plateau, spatial cutoff derivatives remain part of the residual and require explicit attribution.",
        ),
        ForceEdge(
            parent="incoming.original_residual",
            child="incoming.mixed_diagonal_residual",
            relation="definitionally equal for the corresponding diagonal sums",
            source_file="NavierStokes/MixedDiagonalResidual.lean",
            source_declaration="MixedDiagonalResidual.residual_eq_originalResidual",
            evidence=Evidence.SOURCE_EXACT,
            scope="diagonal sums a,q,A,B,P",
        ),
    ]


def terminal_region_result() -> dict:
    """What is known exactly on the final quarter before the singular time."""

    return {
        "region": "3/4 < t < 1",
        "activated_velocity_equals_incoming": True,
        "activated_pressure_equals_incoming": True,
        "activated_residual_equals_incoming_residual": True,
        "activation_specific_force_atoms_present": False,
        "source": {
            "file": "NavierStokes/TimeLocalization.lean",
            "declaration": "TimeLocalization.activated_residual_eq_late",
            "evidence": Evidence.SOURCE_EXACT.value,
        },
        "consequence": (
            "Any attempt to reduce the force specifically in the terminal blowup region must act on the incoming "
            "periodic residual (and its localization/stage ancestry), not on the initial time-activation switch."
        ),
    }


def initial_priority_ranking() -> list[dict]:
    """Qualitative allocation ranking before norm attribution exists.

    The ranking is intentionally categorical: the repository does not yet have
    comparable source-backed norms for all channels, so numeric scores would be
    false precision.
    """

    return [
        {
            "rank": 1,
            "target": "incoming.original_residual -> incoming.mixed_diagonal_residual",
            "decision": "PROMOTE",
            "reason": (
                "This lineage survives unchanged in the terminal region t>3/4 and is definitionally tied to the "
                "diagonal residual used by the construction. Mechanism-level attribution here can change the force "
                "that remains arbitrarily close to blowup."
            ),
            "blocking_unknown": "exact mechanism-level additive decomposition of the finite-stage residual",
        },
        {
            "rank": 2,
            "target": "spatial localization / periodization residual cost",
            "decision": "PROMOTE_FOR_ATTRIBUTION",
            "reason": (
                "The source gives only local equality to cut/original residuals on interior regions. Global cutoff "
                "and periodization cost is therefore a real unresolved force channel rather than a proved dominant one."
            ),
            "blocking_unknown": "global quantitative residual difference outside plateau/inner cube",
        },
        {
            "rank": 3,
            "target": "time activation switch derivative and advection defect",
            "decision": "DEPRIORITIZE_FOR_TERMINAL_FORCE",
            "reason": "Both activation-specific channels disappear once t>3/4.",
            "blocking_unknown": "their total norm may still matter for global force minimization",
        },
        {
            "rank": 4,
            "target": "post-singular Taylor-Borel extension",
            "decision": "DEPRIORITIZE_FOR_PRESINGULAR_ABLATION",
            "reason": "On 0<=t<1 the final force already equals the activated residual exactly.",
            "blocking_unknown": "future-extension norm optimization is a separate problem",
        },
    ]


def final_force_attribution() -> dict:
    nodes = final_force_nodes()
    edges = final_force_edges()
    return {
        "schema": "final-force-attribution-v1",
        "source_lock": source_lock(),
        "nodes": [node.to_dict() for node in nodes],
        "edges": [edge.to_dict() for edge in edges],
        "terminal_region": terminal_region_result(),
        "priority_ranking": initial_priority_ranking(),
        "hard_findings": {
            "final_force_equals_activated_residual_before_blowup": True,
            "time_activation_exactly_three_additive_channels_on_0_lt_t_lt_1": True,
            "activation_specific_channels_survive_after_three_quarters": False,
            "periodic_to_cut_residual_is_only_local_equality": True,
            "cut_to_original_residual_is_only_local_equality": True,
            "mixed_diagonal_residual_equals_original_residual_for_diagonal_sums": True,
            "mechanism_level_final_force_decomposition_complete": False,
            "actual_force_norm_reduced": False,
            "unforced_navier_stokes_blowup_proved": False,
        },
        "next_extraction": {
            "target": "finite-stage residual mechanism decomposition",
            "question": (
                "Which actual stage-level base/wave/mean/particular/correction terms contribute additively to "
                "MixedDiagonalResidual.residual, with what source-backed scale and support?"
            ),
            "stop_rule": "Unknown stage terms remain UNKNOWN; do not backfill guessed categories.",
        },
    }
