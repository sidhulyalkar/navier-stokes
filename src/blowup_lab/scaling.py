from __future__ import annotations

from dataclasses import dataclass, asdict
from fractions import Fraction
from typing import Mapping


@dataclass(frozen=True)
class SimilarityScaling:
    h: Fraction
    beta_r: Fraction
    beta_z: Fraction
    alpha_r: Fraction
    alpha_theta: Fraction
    alpha_z: Fraction

    @classmethod
    def openai_reference(cls, h: Fraction = Fraction(1, 200)) -> "SimilarityScaling":
        return cls(
            h=h,
            beta_r=Fraction(1, 2),
            beta_z=Fraction(1, 2) - h,
            alpha_r=Fraction(1, 2),
            alpha_theta=Fraction(1, 2) + h,
            alpha_z=Fraction(1, 2) + h,
        )

    @property
    def volume_exponent(self) -> Fraction:
        return 2 * self.beta_r + self.beta_z

    def energy_exponent(self, component: str) -> Fraction:
        alpha = self.component_alpha(component)
        return self.volume_exponent - 2 * alpha

    def component_alpha(self, component: str) -> Fraction:
        return {"r": self.alpha_r, "theta": self.alpha_theta, "z": self.alpha_z}[component]

    def beta(self, direction: str) -> Fraction:
        if direction in {"r", "theta"}:
            return self.beta_r
        if direction == "z":
            return self.beta_z
        raise KeyError(direction)

    def time_derivative(self, component: str) -> Fraction:
        return self.component_alpha(component) + 1

    def advection(self, advector: str, direction: str, target: str) -> Fraction:
        return self.component_alpha(advector) + self.beta(direction) + self.component_alpha(target)

    def diffusion(self, direction: str, target: str) -> Fraction:
        return self.component_alpha(target) + 2 * self.beta(direction)

    def balance_report(self) -> dict:
        report: dict[str, dict[str, str | bool]] = {}
        for target in ("r", "theta", "z"):
            t = self.time_derivative(target)
            radial_adv = self.advection("r", "r", target)
            radial_diff = self.diffusion("r", target)
            axial_adv = self.advection("z", "z", target)
            axial_diff = self.diffusion("z", target)
            report[target] = {
                "time": str(t),
                "radial_advection": str(radial_adv),
                "radial_diffusion": str(radial_diff),
                "axial_advection": str(axial_adv),
                "axial_diffusion": str(axial_diff),
                "radial_leading_balance": t == radial_adv == radial_diff,
                "axial_advection_leading": t == axial_adv,
                "axial_diffusion_gap": str(t - axial_diff),
            }
        return report

    def to_dict(self) -> dict:
        d = asdict(self)
        return {k: str(v) for k, v in d.items()} | {
            "volume_exponent": str(self.volume_exponent),
            "energy_exponent_r": str(self.energy_exponent("r")),
            "energy_exponent_theta": str(self.energy_exponent("theta")),
            "energy_exponent_z": str(self.energy_exponent("z")),
        }


def mixed_norm_tau_power(gamma: Fraction, volume_exp: Fraction, spatial_q: Fraction) -> Fraction:
    return volume_exp / spatial_q - gamma


def time_integrability(power: Fraction, time_p: Fraction) -> str:
    exponent = power * time_p
    if exponent > -1:
        return "integrable"
    if exponent == -1:
        return "borderline-log"
    return "divergent"


def leading_balance_family() -> dict:
    return {
        "constraints": [
            "2*beta_r = 1  (time vs radial diffusion)",
            "alpha_r + beta_r = 1  (time vs radial advection)",
            "alpha_t + beta_z = 1  (time vs axial advection)",
            "2*beta_z < 1  (axial diffusion subleading)",
            "2*beta_r + beta_z - 2*alpha_t > 0  (dominant-component core energy decays)",
        ],
        "solution": {
            "beta_r": "1/2",
            "alpha_r": "1/2",
            "alpha_t": "1-beta_z",
            "beta_z_interval": "1/3 < beta_z < 1/2",
            "equivalent_h_interval_if_beta_z=1/2-h": "0 < h < 1/6",
        },
        "paper_reference_range": "0 < h < 1/100",
        "interpretation": "Power counting alone permits a much wider h-window; the paper's h<1/100 restriction therefore comes from deeper profile/stress/correction inequalities, not the elementary balance identities alone.",
    }
