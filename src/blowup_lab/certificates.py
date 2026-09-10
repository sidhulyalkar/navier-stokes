from __future__ import annotations

from dataclasses import asdict, dataclass

from .models import stable_hash


@dataclass(frozen=True)
class CertificateNode:
    id: str
    kind: str
    payload_hash: str
    dependencies: tuple[str, ...]


def build_certificate_dag(items: list[tuple[str, dict, tuple[str, ...]]]) -> dict:
    """Build a content-addressed DAG.

    Dependencies may be supplied either as an already-computed prior node id or
    as the unique `kind` of a prior item.  Kind references are resolved to node
    ids before hashing, so the resulting certificate remains content-addressed.
    Unknown and ambiguous-forward references still fail closed.
    """
    nodes: list[CertificateNode] = []
    known_ids: set[str] = set()
    kind_to_id: dict[str, str] = {}

    for kind, payload, deps in items:
        if kind in kind_to_id:
            raise ValueError(f"duplicate certificate kind {kind}")

        resolved: list[str] = []
        for dep in deps:
            if dep in known_ids:
                resolved.append(dep)
            elif dep in kind_to_id:
                resolved.append(kind_to_id[dep])
            else:
                raise ValueError(f"certificate dependency {dep} not yet known")

        resolved_deps = tuple(resolved)
        ph = stable_hash(payload)
        nid = stable_hash({"kind": kind, "payload_hash": ph, "dependencies": resolved_deps})
        node = CertificateNode(nid, kind, ph, resolved_deps)
        nodes.append(node)
        known_ids.add(nid)
        kind_to_id[kind] = nid

    return {
        "valid": True,
        "nodes": [asdict(n) for n in nodes],
        "root": nodes[-1].id if nodes else None,
        "kind_index": kind_to_id,
    }
