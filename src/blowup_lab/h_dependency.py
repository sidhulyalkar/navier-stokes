from __future__ import annotations

from dataclasses import dataclass, asdict
from typing import Iterable


VALID_KINDS = {"ROOT", "NUMERIC", "DERIVED_WEAK", "INHERITED", "UNKNOWN"}


@dataclass(frozen=True)
class HConstraintNode:
    node_id: str
    file: str
    declaration: str
    kind: str
    statement: str
    source_anchor: str
    parents: tuple[str, ...] = ()
    candidate_upper_bound: float | None = None
    notes: str = ""

    def __post_init__(self) -> None:
        if self.kind not in VALID_KINDS:
            raise ValueError(f"invalid constraint kind: {self.kind}")

    def to_dict(self) -> dict:
        return asdict(self)


# v5.3 source-locked seed graph. These are intentionally only nodes whose use is
# visible in the pinned OpenAI Lean source. The graph is expected to grow as the
# crawler/source extraction advances.
def source_seed_nodes() -> tuple[HConstraintNode, ...]:
    return (
        HConstraintNode(
            node_id="small_h_root",
            file="NavierStokes/NaturalAxisData.lean",
            declaration="NaturalAxisData.SmallParameters.h_le",
            kind="ROOT",
            statement="h <= 1/1000",
            source_anchor="SmallParameters",
            candidate_upper_bound=1 / 1000,
            notes="Concrete formalization window; source comment describes it as a permitted quantitative choice, not sharpness.",
        ),
        HConstraintNode(
            node_id="D_bounds",
            file="NavierStokes/NaturalAxisData.lean",
            declaration="NaturalAxisData.D_bounds",
            kind="NUMERIC",
            statement="499/1000 <= D(h) < 1/2",
            source_anchor="D_bounds",
            parents=("small_h_root",),
            notes="Consumes h_le numerically to obtain explicit margins.",
        ),
        HConstraintNode(
            node_id="A_bounds",
            file="NavierStokes/NaturalAxisData.lean",
            declaration="NaturalAxisData.A_bounds",
            kind="NUMERIC",
            statement="1/2 < A(h) <= 501/1000",
            source_anchor="A_bounds",
            parents=("small_h_root",),
            notes="Consumes h_le numerically to obtain explicit margins.",
        ),
        HConstraintNode(
            node_id="L_lower",
            file="NavierStokes/NaturalAxisData.lean",
            declaration="NaturalAxisData.L_lower_bound",
            kind="NUMERIC",
            statement="499/500 <= L(h, eta) on |eta|<=1",
            source_anchor="L_lower_bound",
            parents=("small_h_root",),
            notes="Direct quantitative use of h_le.",
        ),
        HConstraintNode(
            node_id="neg_W_lower",
            file="NavierStokes/NaturalAxisData.lean",
            declaration="NaturalAxisData.neg_W_lower_bound",
            kind="NUMERIC",
            statement="2991/1000 <= -W(h,j,eta)",
            source_anchor="neg_W_lower_bound",
            parents=("small_h_root",),
            notes="Directly uses h_le and j_le; likely part of profile/cone margin budget.",
        ),
        HConstraintNode(
            node_id="natural_core_half",
            file="NavierStokes/NaturalCore.lean",
            declaration="NaturalCore core construction local h<1/2 fact",
            kind="DERIVED_WEAK",
            statement="h < 1/2",
            source_anchor="linarith [hsmall.h_le]",
            parents=("small_h_root",),
            candidate_upper_bound=1 / 2,
            notes="The consumer only needs h<1/2, far weaker than the root assumption.",
        ),
        HConstraintNode(
            node_id="constructed_base_half",
            file="NavierStokes/ConstructedSlowBase.lean",
            declaration="ConstructedSlowBase.height_lt_half",
            kind="DERIVED_WEAK",
            statement="h < 1/2",
            source_anchor="height_lt_half",
            parents=("small_h_root",),
            candidate_upper_bound=1 / 2,
            notes="Pure proof plumbing if this theorem is the only local consumer.",
        ),
        HConstraintNode(
            node_id="natural_entrance_numeric",
            file="NavierStokes/NaturalEntrance.lean",
            declaration="NaturalEntrance numeric entrance bound (source hit)",
            kind="NUMERIC",
            statement="uses h_le multiplied by 4501/500 in an entrance estimate",
            source_anchor="mul_le_mul_of_nonneg_right hsmall.h_le (4501/500)",
            parents=("small_h_root",),
            notes="Needs theorem-level extraction to solve for the largest admissible h.",
        ),
        HConstraintNode(
            node_id="matching_cone_numeric",
            file="NavierStokes/MatchingConeBounds.lean",
            declaration="MatchingConeBounds numeric cone estimate (source hit)",
            kind="NUMERIC",
            statement="uses h_le with factor 4501/500 inside matching-cone bounds",
            source_anchor="mul_le_mul_of_nonneg_right hs.h_le (4501/500)",
            parents=("small_h_root",),
            notes="High-priority candidate bottleneck because strict cone margin is structurally important.",
        ),
        HConstraintNode(
            node_id="activation_numeric",
            file="NavierStokes/ActivationContinuation.lean",
            declaration="ActivationContinuation hold-model bound (source hit)",
            kind="NUMERIC",
            statement="uses h_le with factor 4501/500 in activation continuation",
            source_anchor="mul_le_mul_of_nonneg_right hsmall.h_le (4501/500)",
            parents=("small_h_root",),
            notes="Potentially structural; exact target inequality still needs extraction.",
        ),
        HConstraintNode(
            node_id="transition_numeric",
            file="NavierStokes/TransitionRamp.lean",
            declaration="TransitionRamp quantitative ramp bound (source hit)",
            kind="NUMERIC",
            statement="uses h_le together with |eta|<=11/10",
            source_anchor="mul_le_mul hs.h_le hsquare ... (1/1000)",
            parents=("small_h_root",),
            notes="Exact admissible relaxation requires extracting the final target margin.",
        ),
    )


def validate_graph(nodes: Iterable[HConstraintNode]) -> None:
    nodes = tuple(nodes)
    ids = {n.node_id for n in nodes}
    if len(ids) != len(nodes):
        raise ValueError("duplicate node id")
    for node in nodes:
        missing = set(node.parents) - ids
        if missing:
            raise ValueError(f"{node.node_id}: missing parents {sorted(missing)}")


def descendants(nodes: Iterable[HConstraintNode], root: str) -> set[str]:
    nodes = tuple(nodes)
    validate_graph(nodes)
    out = {root}
    changed = True
    while changed:
        changed = False
        for node in nodes:
            if node.node_id not in out and any(parent in out for parent in node.parents):
                out.add(node.node_id)
                changed = True
    return out


def relaxation_priority(nodes: Iterable[HConstraintNode]) -> list[dict]:
    """Rank direct/indirect root consumers by how likely they are to bind h.

    NUMERIC consumers outrank UNKNOWN/INHERITED and DERIVED_WEAK consumers.
    This is a research prioritization, not a proof of which inequality is sharp.
    """
    nodes = tuple(nodes)
    validate_graph(nodes)
    weights = {"NUMERIC": 3, "UNKNOWN": 2, "INHERITED": 1, "DERIVED_WEAK": 0, "ROOT": -1}
    active = descendants(nodes, "small_h_root")
    ranked = [n for n in nodes if n.node_id in active and n.kind != "ROOT"]
    ranked.sort(key=lambda n: (-weights[n.kind], n.file, n.declaration))
    return [
        {
            "node_id": n.node_id,
            "kind": n.kind,
            "file": n.file,
            "declaration": n.declaration,
            "candidate_upper_bound": n.candidate_upper_bound,
            "notes": n.notes,
        }
        for n in ranked
    ]


def graph_report() -> dict:
    nodes = source_seed_nodes()
    validate_graph(nodes)
    counts = {kind: sum(n.kind == kind for n in nodes) for kind in sorted(VALID_KINDS)}
    return {
        "schema": "h-constraint-dependency-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538",
        },
        "nodes": [n.to_dict() for n in nodes],
        "counts": counts,
        "priority": relaxation_priority(nodes),
        "claim_boundary": (
            "This graph records source-visible consumers and classifications. It does not yet prove "
            "the maximal admissible h or that any listed numerical consumer is sharp."
        ),
    }
