from __future__ import annotations

from dataclasses import dataclass, asdict
from .models import stable_hash


@dataclass(frozen=True)
class CertificateNode:
    id: str
    kind: str
    payload_hash: str
    dependencies: tuple[str, ...]


def build_certificate_dag(items: list[tuple[str, dict, tuple[str, ...]]]) -> dict:
    nodes: list[CertificateNode] = []
    known: set[str] = set()
    for kind, payload, deps in items:
        for dep in deps:
            if dep not in known:
                raise ValueError(f"certificate dependency {dep} not yet known")
        ph = stable_hash(payload)
        nid = stable_hash({"kind": kind, "payload_hash": ph, "dependencies": deps})
        nodes.append(CertificateNode(nid, kind, ph, deps))
        known.add(nid)
    return {
        "valid": True,
        "nodes": [asdict(n) for n in nodes],
        "root": nodes[-1].id if nodes else None,
    }
