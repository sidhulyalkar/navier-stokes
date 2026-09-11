from __future__ import annotations

from dataclasses import asdict, dataclass


SOURCE_COMMIT = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"


@dataclass(frozen=True)
class ProducerStep:
    step_id: str
    source_file: str
    source_declaration: str
    role: str
    exact_fact: str
    additive_decomposition_available: bool
    warning: str = ""

    def to_dict(self) -> dict:
        return asdict(self)


def finite_residual_producer_chain() -> list[ProducerStep]:
    """Trace where the terminal diagonal residual estimate is actually produced.

    The key purpose is to mark the exact boundary between source-backed
    attribution and a decomposition that still has to be extracted. The final
    candidate assembly consumes an aggregate `finite_residual` JetRate bound;
    it does not expose base/wave/mean/correction atoms itself.
    """

    return [
        ProducerStep(
            step_id="consumer.stage_estimates",
            source_file="NavierStokes/MixedCandidateAssembly.lean",
            source_declaration="MixedCandidateAssembly.StageEstimates.finite_residual",
            role="aggregate finite-prefix residual obligation consumed by diagonal assembly",
            exact_fact=(
                "For every finite prefix J and derivative order m, the Navier-Stokes residual of the uncut mixed "
                "velocity and pressure prefix has JetRate exponent gain(J)-residualLoss(m)."
            ),
            additive_decomposition_available=False,
            warning=(
                "This field is an aggregate estimate. Treating it as a term-by-term force decomposition would invent "
                "structure that StageEstimates does not contain."
            ),
        ),
        ProducerStep(
            step_id="adapter.actual_stage_estimates",
            source_file="NavierStokes/ActualStageEstimates.lean",
            source_declaration="ActualStageEstimates.stageEstimates_of_representations",
            role="fills the abstract StageEstimates record for the actual iteration",
            exact_fact=(
                "The finite_residual field is discharged directly by ActualCycleResidualBounds.finite_residual_rates, "
                "with residualLoss set to ActualCycleResidualBounds.fixedLoss."
            ),
            additive_decomposition_available=False,
            warning=(
                "The adapter proves that the actual iteration meets the aggregate obligation; it still does not expose "
                "an additive mechanism split."
            ),
        ),
        ProducerStep(
            step_id="producer.cycle_residual_bounds",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.finite_residual_rates",
            role="source-backed producer of the finite-prefix residual rate",
            exact_fact=(
                "The actual correction-cycle invariant supplies the finite residual rate with a derivative loss fixed "
                "before the number of completed correction cycles J is chosen."
            ),
            additive_decomposition_available=False,
            warning=(
                "This theorem is the current attribution frontier. Its proof dependencies and intermediate estimates "
                "must be unpacked before naming base, wave, mean, gauge, excluded, or correction terms as final-force atoms."
            ),
        ),
    ]


def current_attribution_frontier() -> dict:
    chain = finite_residual_producer_chain()
    return {
        "schema": "stage-residual-attribution-v1",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "producer_chain": [step.to_dict() for step in chain],
        "frontier": "ActualCycleResidualBounds.finite_residual_rates",
        "known_dependencies_from_pinned_source": [
            "PhysicalResidualJetBounds",
            "ActualInitialization",
            "ActualInitialExcluded",
            "GaugeExcludedBounds",
            "ActualIterationLedger",
            "GlobalBaseError",
            "ActualCarrierGeometry",
            "ActualPolarCoverage",
        ],
        "interpretation": (
            "The import/dependency list identifies proof ingredients only. It is not an additive residual decomposition. "
            "The next tranche must inspect the proof of finite_residual_rates and promote a mechanism atom only when an "
            "exact identity or separately bounded residual contribution is visible."
        ),
        "next_questions": [
            "Which intermediate residual identity feeds finite_residual_rates before JetRate aggregation?",
            "Where is the base residual separated from wave/covariance cancellation?",
            "Where do excluded-slot, gauge/mean, particular, and signed-wave errors enter?",
            "Which contributions have independent support and scale bounds suitable for norm attribution?",
            "Which contributions persist in the terminal region 3/4 < t < 1?",
        ],
        "hard_findings": {
            "final_assembly_contains_termwise_finite_residual_split": False,
            "actual_stage_adapter_contains_termwise_finite_residual_split": False,
            "finite_residual_rate_producer_located": True,
            "producer_termwise_decomposition_extracted": False,
            "force_priority_numerically_ranked": False,
        },
    }
