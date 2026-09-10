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
    """Source-derived sufficient h upper bound for NaturalEntrance.base_source_lower."""
    if not (0 <= j_upper < 0.1):
        raise ValueError("j_upper must lie in [0, 0.1)")
    if not (target < 3 - j_upper):
        raise ValueError("target must be below the h=0 conservative lower bound")
    return (3.0 - j_upper - target) / (17.0 + 2.0 * j_upper)


def matching_cone_shape_axis_h_upper(
    j_upper: float = 1e-3,
    ell_lower: float = 11 / 20,
    target: float = 8 / 5,
) -> float:
    """Sufficient local h bound for MatchingConeBounds.shape_axis_lower.

    From the pinned source and |eta|<=1, 0<j<=j_upper, 0<h<1/2:

      -W >= 3 - 8h - j_upper,
      1 - 2 eta U <= 9 + 2 j_upper,
      H * shapeGradient >= -2 j_upper.

    For theta in [0,1] and ell>=ell_lower, this yields

      shape expression >=
        ell_lower*(3-j_upper) - 2*j_upper
        - h*(8*ell_lower + 9 + 2*j_upper).

    Requiring this conservative lower bound to exceed `target` gives the
    returned strict sufficient h upper bound. This isolates this theorem only;
    it does not relax the complete matching-cone or final construction.
    """
    if not (0 <= j_upper < 0.1):
        raise ValueError("j_upper must lie in [0, 0.1)")
    if not (ell_lower > 0):
        raise ValueError("ell_lower must be positive")
    intercept = ell_lower * (3.0 - j_upper) - 2.0 * j_upper
    coefficient = 8.0 * ell_lower + 9.0 + 2.0 * j_upper
    if not (target < intercept):
        raise ValueError("target must be below the h=0 conservative lower bound")
    return (intercept - target) / coefficient


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


def matching_cone_relaxation() -> LocalRelaxation:
    j = 1e-3
    ell = 11 / 20
    bound = matching_cone_shape_axis_h_upper(j_upper=j, ell_lower=ell, target=8 / 5)
    return LocalRelaxation(
        theorem="NavierStokes.MatchingConeBounds.shape_axis_lower",
        parameter="h",
        original_global_upper=1e-3,
        sufficient_local_upper=bound,
        assumptions=(
            "0 < h < 1/2",
            "0 < j <= 1/1000",
            "|eta| <= 1",
            "ell >= 11/20",
            "theta in [0,1]",
            "shapeGradient source bounds as pinned at source commit 8937a8f...",
        ),
        derivation=(
            "-W >= 3-8*h-j",
            "-h*(1-2*eta*U) >= -h*(9+2*j)",
            "H*shapeGradient >= -2*j because the D+4d contribution is nonnegative and |shapeGradient|<=2",
            "theta in [0,1] preserves the lower bound -2*j",
            "shape expression >= ell*(3-j) - 2*j - h*(8*ell + 9 + 2*j)",
            "at ell=11/20 and j=1/1000, shape>8/5 for h below the reported threshold",
        ),
        status="DERIVED_SUFFICIENT_LOCAL_BOUND",
        claim_boundary=(
            "This locally relaxes only shape_axis_lower. It does not establish uniform shapeModel bounds, "
            "stress-cone interiority for the complete construction, or validity of later correction stages at the relaxed h."
        ),
    )


def relaxation_report() -> dict:
    entrance = natural_entrance_relaxation()
    cone = matching_cone_relaxation()
    active = min((entrance, cone), key=lambda r: r.sufficient_local_upper)
    return {
        "schema": "local-h-relaxation-v2",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538",
        },
        "relaxations": [entrance.to_dict(), cone.to_dict()],
        "current_local_bottleneck": {
            "theorem": active.theorem,
            "sufficient_local_upper": active.sufficient_local_upper,
            "expansion_factor_over_global": active.expansion_factor,
        },
        "next": [
            "formalize generalized local inequalities in Lean-compatible form without SmallParameters.h_le",
            "extract ActivationContinuation and TransitionRamp numerical target inequalities",
            "intersect all locally sufficient h windows along the transitive proof path",
            "distinguish shape-axis positivity from full stress-cone interior margin",
        ],
    }
