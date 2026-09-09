from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import asdict
from .models import ResidualAtom, stable_hash
from .openai_reference import residual_atoms


class ResidualAtlas:
    def __init__(self, atoms: list[ResidualAtom] | None = None):
        self.atoms = atoms or residual_atoms()
        self.by_id = {a.id: a for a in self.atoms}
        if len(self.by_id) != len(self.atoms):
            raise ValueError("duplicate residual atom id")
        self._validate_dependencies()

    def _validate_dependencies(self) -> None:
        for atom in self.atoms:
            for dep in atom.dependencies:
                if dep not in self.by_id:
                    raise ValueError(f"{atom.id} has missing dependency {dep}")

    def topological_order(self) -> list[str]:
        indeg = {a.id: 0 for a in self.atoms}
        children: dict[str, list[str]] = defaultdict(list)
        for atom in self.atoms:
            for dep in atom.dependencies:
                indeg[atom.id] += 1
                children[dep].append(atom.id)
        q = deque(sorted(k for k, v in indeg.items() if v == 0))
        out: list[str] = []
        while q:
            n = q.popleft()
            out.append(n)
            for ch in sorted(children[n]):
                indeg[ch] -= 1
                if indeg[ch] == 0:
                    q.append(ch)
        if len(out) != len(self.atoms):
            raise ValueError("cycle in residual atlas")
        return out

    def downstream(self, atom_id: str) -> list[str]:
        children: dict[str, list[str]] = defaultdict(list)
        for atom in self.atoms:
            for dep in atom.dependencies:
                children[dep].append(atom.id)
        seen: set[str] = set()
        q = deque(children[atom_id])
        while q:
            x = q.popleft()
            if x in seen:
                continue
            seen.add(x)
            q.extend(children[x])
        return sorted(seen)

    def to_dict(self) -> dict:
        payload = {
            "schema": "residual-atlas-v1",
            "claim_level": "STRUCTURAL_SOURCE_ATLAS",
            "warning": "Structural decomposition of proof architecture; not an additive numerical decomposition of the final force.",
            "atoms": [asdict(a) for a in self.atoms],
            "topological_order": self.topological_order(),
        }
        payload["atlas_hash"] = stable_hash(payload)
        return payload
