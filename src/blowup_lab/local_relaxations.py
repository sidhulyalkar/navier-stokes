from __future__ import annotations

from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class LocalRelaxation:
    theorem: str
    parameter: str
    original_global_upper: float
    sufficient_local_upper: float
    assumptions: tuple[str, ...]
    derivation: tuple[str, ...]
    status: str
    claim_boundary: str

    @property
    def expansion_factor(self) -> float:
        return self.sufficient_local_upper / self.original_global_upper

    def to_dict(self) -> dict:
        out = asdict(self)
        out["expansion_factor"] = self.expansion_factor
        return out


def natural_entrance_base_source_h_upper(j_upper: float = 1e-3, target: float = 2.9) -> float:
    """A source-derived sufficient h upper bound for NaturalEntrance.base_source_lower.

    Uses only the explicit definitions/formulas visible in the pinned source:

      -W(h,j,eta) = 3 - 8 h eta^2 + 2 D(h) j eta,
      D(h)=1/2-h,
      U(j,eta)=4 eta+j.

    Under |eta|<=1, 0<j<=j_upper and 0<h<1/2:

      -W >= 3 - 8h - j_upper,
      1 - 2 eta U <= 1 + 2 |eta U| <= 9 + 2 j_upper.

    Hence

      -W - h(1 - 2 eta U)
        >= 3 - j_upper - h(17 + 2 j_upper).

    Requiring this lower bound to exceed `target` gives the returned strict
    sufficient upper bound. This is a local analytic certificate, not a proof
    that the rest of the OpenAI construction remains valid at that h.
    """
    if not (0 <= j_upper < 0.1):
        raise ValueError("j_upper must lie in [0, 0.1)")
    if not (target < 3 - j_upper):
        raise ValueError("target must be below the h=0 conservative lower bound")
    return (3.0 - j_upper - target) / (17.0 + 2.0 * j_upper)


def natural_entrance_relaxation() -> LocalRelaxation:
    j = 1e-3
    bound = natural_entrance_base_source_h_upper(j_upper=j, target=2.9)
    return LocalRelaxation(
        theorem="NavierStokes.NaturalEntrance.base_source_lower",
        parameter="h",
        original_global_upper=1e-3,
        sufficient_local_upper=bound,
        assumptions=(
            "0 < h < 1/2",
            "0 < j <= 1/1000",
            "|eta| <= 1",
            "NaturalAxisData definitions D,U,W as pinned at source commit 8937a8f...",
        ),
        derivation=(
            "-W = 3 - 8*h*eta^2 + 2*D(h)*j*eta >= 3 - 8*h - j",
            "|U| <= 4+j and |eta|<=1 imply 1-2*eta*U <= 9+2*j",
            "source >= 3-j-h*(17+2*j)",
            "source > 2.9 if h < (0.1-j)/(17+2*j)",
        ),
        status="DERIVED_SUFFICIENT_LOCAL_BOUND",
        claim_boundary=(
            "This removes base_source_lower as an explanation for the global h<=1/1000 choice up to this "
            "local sufficient window. It does not establish that NaturalProfile, cone, activation, correction, "
            "or final candidate theorems survive at the relaxed h."
        ),
    )


def relaxation_report() -> dict:
    r = natural_entrance_relaxation()
    return {
        "schema": "local-h-relaxation-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538",
        },
        "relaxations": [r.to_dict()],
        "next": [
            "formalize the generalized base_source_lower statement in Lean without SmallParameters.h_le",
            "extract and solve MatchingConeBounds quantitative inequalities",
            "intersect all locally sufficient h windows along the transitive proof path",
        ],
    }
