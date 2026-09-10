from __future__ import annotations

from dataclasses import asdict, dataclass


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class ResidualLayer:
    layer_id: str
    expression: str
    status_under_psi_one: str
    evidence: str
    source_file: str
    source_declaration: str
    role: str
    warning: str = ""

    def to_dict(self) -> dict:
        return asdict(self)


def primary_linear_residual_layers() -> dict:
    """Compile the exact source decomposition after the primary solve.

    PrimaryResidualClass.linear_identity writes the corrected harmonic residual
    as constructedGood plus excludedSlotError. Setting psi=1 kills the latter
    under the principal solve identity, but constructedGood remains an explicit
    obligation. This module deliberately does not infer that constructedGood is
    nonzero; it only records that it is not algebraically erased by psi=1.
    """
    layers = [
        ResidualLayer(
            layer_id="primary.excluded_slot",
            expression="mode(excludedSlotError)",
            status_under_psi_one="ERASED_UNDER_SOLVE_IDENTITY",
            evidence="SOURCE_EXACT_PLUS_ALGEBRA",
            source_file="NavierStokes/PrimaryResidualClass.lean",
            source_declaration="PrimaryResidualClass.Inputs.linear_identity",
            role="localization residual channel",
            warning="Erasing this channel does not erase constructedGood.",
        ),
        ResidualLayer(
            layer_id="primary.constructed_good",
            expression="mode(constructedGood)",
            status_under_psi_one="PERSISTS_AS_EXPLICIT_OBLIGATION",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/PrimaryResidualClass.lean",
            source_declaration="PrimaryResidualClass.Inputs.linear_identity",
            role="retained corrected linear-wave residual",
            warning=(
                "PERSISTS means it remains in the exact identity after psi=1; it is not a proof that the field is "
                "pointwise nonzero or cannot cancel against a later mechanism."
            ),
        ),
        ResidualLayer(
            layer_id="good.curl_principal",
            expression="principalVelocity(curlCorrection(withCutoff(psi)))",
            status_under_psi_one="PERSISTS_AS_FORMULA",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/LinearWaveBounds.lean",
            source_declaration="WaveCoefficients.goodCoefficient / constructedGood",
            role="principal contribution of the exact-curl amplitude correction",
        ),
        ResidualLayer(
            layer_id="good.corrected_remainder",
            expression="remainder(addAmplitude(withCutoff(psi), curlCorrection(withCutoff(psi))))",
            status_under_psi_one="PERSISTS_AS_FORMULA",
            evidence="SOURCE_EXACT",
            source_file="NavierStokes/LinearWaveBounds.lean",
            source_declaration="WaveCoefficients.goodCoefficient / constructedGood",
            role="lower-order linear-wave remainder after exact-curl correction",
        ),
    ]

    return {
        "schema": "primary-linear-residual-layers-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "exact_identity": (
            "harmonicResidual(corrected) = mode(constructedGood) + mode(excludedSlotError)"
        ),
        "psi_one_counterfactual": (
            "Under the principal solve identity and a valid uncut coefficient, excludedSlotError=0, leaving "
            "harmonicResidual(corrected_psi1) = mode(constructedGood_psi1)."
        ),
        "layers": [layer.to_dict() for layer in layers],
        "next_question": (
            "After the [0,3L/2] homogeneous primary is constructed, recompute constructedGood with psi=1 and decide "
            "whether its curl-principal and corrected-remainder pieces cancel, remain in the same weighted class, or "
            "expose a new non-Gaussian obstruction outside the native slot."
        ),
        "claim_boundary": (
            "The source identity shows that constructedGood remains as an explicit term after the localization channel "
            "is erased. This report does not claim constructedGood is pointwise nonzero, that it is forcing, or that it "
            "cannot be cancelled by later correction machinery."
        ),
    }
