from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from typing import Iterable


@dataclass(frozen=True)
class Constraint:
    id: str
    parameter: str
    lower: Fraction | None = None
    lower_strict: bool = False
    upper: Fraction | None = None
    upper_strict: bool = False
    evidence: str = "SOURCE"
    source_kind: str = "unknown"
    source_ref: str = ""
    source_commit: str | None = None
    lean_file: str | None = None
    lean_declaration: str | None = None
    role: str = ""
    notes: tuple[str, ...] = ()

    def to_dict(self) -> dict:
        d = asdict(self)
        for key in ("lower", "upper"):
            value = d[key]
            d[key] = None if value is None else str(value)
        d["notes"] = list(self.notes)
        return d


@dataclass(frozen=True)
class IntervalSummary:
    parameter: str
    lower: Fraction | None
    lower_strict: bool
    upper: Fraction | None
    upper_strict: bool
    feasible: bool
    active_lower_ids: tuple[str, ...]
    active_upper_ids: tuple[str, ...]

    def to_dict(self) -> dict:
        return {
            "parameter": self.parameter,
            "lower": None if self.lower is None else str(self.lower),
            "lower_strict": self.lower_strict,
            "upper": None if self.upper is None else str(self.upper),
            "upper_strict": self.upper_strict,
            "feasible": self.feasible,
            "active_lower_ids": list(self.active_lower_ids),
            "active_upper_ids": list(self.active_upper_ids),
        }


def intersect_constraints(constraints: Iterable[Constraint], parameter: str) -> IntervalSummary:
    xs = [c for c in constraints if c.parameter == parameter]
    lowers = [c for c in xs if c.lower is not None]
    uppers = [c for c in xs if c.upper is not None]
    lower = max((c.lower for c in lowers), default=None)
    upper = min((c.upper for c in uppers), default=None)
    active_lower = tuple(c.id for c in lowers if c.lower == lower) if lower is not None else ()
    active_upper = tuple(c.id for c in uppers if c.upper == upper) if upper is not None else ()
    lower_strict = any(c.lower_strict for c in lowers if c.lower == lower) if lower is not None else False
    upper_strict = any(c.upper_strict for c in uppers if c.upper == upper) if upper is not None else False
    feasible = True
    if lower is not None and upper is not None:
        feasible = lower < upper or (lower == upper and not lower_strict and not upper_strict)
    return IntervalSummary(parameter, lower, lower_strict, upper, upper_strict, feasible, active_lower, active_upper)


def default_h_ledger() -> list[Constraint]:
    commit = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
    return [
        Constraint(id="H_POSITIVE", parameter="h", lower=Fraction(0), lower_strict=True,
                   evidence="FORMALIZED", source_kind="Lean",
                   source_ref="NaturalAxisData.SmallParameters.h_pos", source_commit=commit,
                   lean_file="NavierStokes/NaturalAxisData.lean",
                   lean_declaration="NaturalAxisData.SmallParameters.h_pos",
                   role="selects anisotropic axial expansion"),
        Constraint(id="H_POWER_COUNTING_ENERGY", parameter="h", upper=Fraction(1, 6), upper_strict=True,
                   evidence="EXPLORATORY_DERIVED", source_kind="local derivation",
                   source_ref="v5.1 leading balance family",
                   role="finite/decaying core energy plus subleading axial diffusion",
                   notes=("Cheap scaling condition only; not a proof-admissible range.",)),
        Constraint(id="H_MANUSCRIPT_SMALLNESS", parameter="h", upper=Fraction(1, 100), upper_strict=True,
                   evidence="SOURCE", source_kind="manuscript",
                   source_ref="Finite time blowup for Navier-Stokes, similarity-parameter smallness hypothesis",
                   role="published construction smallness regime",
                   notes=("Tracked as a manuscript-level source constraint, not claimed optimal.",)),
        Constraint(id="H_FORMALIZATION_SMALL_PARAMETERS", parameter="h", upper=Fraction(1, 1000),
                   evidence="FORMALIZED", source_kind="Lean",
                   source_ref="NaturalAxisData.SmallParameters.h_le", source_commit=commit,
                   lean_file="NavierStokes/NaturalAxisData.lean",
                   lean_declaration="NaturalAxisData.SmallParameters.h_le",
                   role="concrete quantitative range used by the formalized natural-axis construction",
                   notes=("The file comments that this is a concrete range permitted by the manuscript's smallness order.",
                          "Do not interpret 1/1000 as a demonstrated sharp threshold.")),
        Constraint(id="H_GEOMETRY_HALF", parameter="h", upper=Fraction(1, 2), upper_strict=True,
                   evidence="FORMALIZED_DERIVED", source_kind="Lean downstream",
                   source_ref="multiple geometry lemmas consume h_lt_half", source_commit=commit,
                   role="positivity/nondegeneracy of similarity geometry",
                   notes=("Weaker than the active small-parameter constraint.",)),
    ]


def tightening_chain(constraints: Iterable[Constraint], parameter: str = "h") -> list[dict]:
    xs = [c for c in constraints if c.parameter == parameter and c.upper is not None]
    xs.sort(key=lambda c: c.upper, reverse=True)
    out = []
    previous = None
    for c in xs:
        ratio = None
        if previous is not None and c.upper and c.upper != 0:
            ratio = str(previous / c.upper)
        out.append({"id": c.id, "upper": str(c.upper), "strict": c.upper_strict,
                    "evidence": c.evidence, "source_ref": c.source_ref,
                    "tightening_factor_from_previous": ratio})
        previous = c.upper
    return out


def ledger_report() -> dict:
    constraints = default_h_ledger()
    formal_or_source = [c for c in constraints if c.evidence in {"FORMALIZED", "SOURCE", "FORMALIZED_DERIVED"}]
    return {
        "parameter": "h",
        "constraints": [c.to_dict() for c in constraints],
        "all_constraints_intersection": intersect_constraints(constraints, "h").to_dict(),
        "source_and_formal_intersection": intersect_constraints(formal_or_source, "h").to_dict(),
        "tightening_chain": tightening_chain(constraints),
        "scientific_interpretation": {
            "cheap_scaling_ceiling": "1/6",
            "manuscript_ceiling": "1/100",
            "formalization_concrete_ceiling": "1/1000",
            "open_question": "Which proof obligations actually force each tightening, and how far can the constants be relaxed while preserving every downstream inequality?",
            "sharpness_claimed": False,
        },
    }
