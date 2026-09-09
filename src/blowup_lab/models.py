from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import Enum
from hashlib import sha256
import json
from typing import Any


class EvidenceLevel(str, Enum):
    SOURCE = "SOURCE"
    REPRODUCED = "REPRODUCED"
    EXPLORATORY = "EXPLORATORY"
    VALIDATED_BOUND = "VALIDATED_BOUND"
    FORMALIZED = "FORMALIZED"


class RouteStatus(str, Enum):
    PROMOTE = "PROMOTE"
    HOLD = "HOLD"
    KILL = "KILL"


@dataclass(frozen=True)
class SourceAnchor:
    section: str
    page: int
    statement: str
    lean_file: str | None = None
    lean_declaration: str | None = None


@dataclass(frozen=True)
class ResidualAtom:
    id: str
    stage: str
    region: str
    channel: str
    mechanism: str
    role: str
    source: SourceAnchor
    dependencies: tuple[str, ...] = ()
    cancellation_partner: tuple[str, ...] = ()
    forcing_exposure: str = "none"
    if_removed: str = "unknown"
    evidence: EvidenceLevel = EvidenceLevel.SOURCE
    notes: tuple[str, ...] = ()


@dataclass(frozen=True)
class Mechanism:
    id: str
    category: str
    current_role: str
    external_force_exposure: str
    required_by_atoms: tuple[str, ...]
    replaceable_in_principle: bool
    replacement_obligation: str


@dataclass
class AblationResult:
    route_id: str
    disabled: list[str]
    enabled_alternatives: list[str]
    hard_failures: list[str]
    open_obligations: list[str]
    benefits: list[str]
    status: RouteStatus
    score: float
    rationale: str


@dataclass
class ProofObligation:
    id: str
    statement: str
    category: str
    depends_on: list[str] = field(default_factory=list)
    status: str = "OPEN"
    evidence: list[str] = field(default_factory=list)


def stable_hash(obj: Any) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str).encode()
    return sha256(raw).hexdigest()


def dataclass_dict(x: Any) -> dict[str, Any]:
    return asdict(x)
