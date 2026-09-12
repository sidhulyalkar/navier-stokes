from __future__ import annotations

from dataclasses import asdict, dataclass

from .residual_force_ledger import exact_residual_attribution_report


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
    """Trace the aggregate finite residual bound to its exact residual ledger.

    The final candidate assembly and actual-stage adapter remain aggregate
    interfaces.  The proof of `finite_residual_rates`, however, descends into
    `ActualCycleResidualBounds.native_residual`, whose dependencies expose an
    exact harmonic reconstruction of the same normalized residual.
    """

    return [
        ProducerStep(
            step_id="consumer.stage_estimates",
            source_file="NavierStokes/MixedCandidateAssembly.lean",
            source_declaration="MixedCandidateAssembly.StageEstimates.finite_residual",
            role="aggregate finite-prefix residual obligation consumed by diagonal assembly",
            exact_fact=(
                "For every finite prefix J and derivative order m, the Navier-Stokes residual of the uncut mixed "
                "velocity and pressure prefix has the supplied JetRate exponent."
            ),
            additive_decomposition_available=False,
            warning="This record field is an aggregate estimate and does not expose force atoms.",
        ),
        ProducerStep(
            step_id="adapter.actual_stage_estimates",
            source_file="NavierStokes/ActualStageEstimates.lean",
            source_declaration="ActualStageEstimates.stageEstimates_of_representations",
            role="fills the abstract StageEstimates record for the actual iteration",
            exact_fact=(
                "The finite_residual field is discharged by ActualCycleResidualBounds.finite_residual_rates, "
                "with residualLoss fixed independently of the number of completed correction cycles."
            ),
            additive_decomposition_available=False,
            warning="The adapter preserves the aggregate interface; decomposition lives below it.",
        ),
        ProducerStep(
            step_id="producer.cycle_residual_bounds",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.finite_residual_rates",
            role="source-backed producer of the finite-prefix physical residual rate",
            exact_fact=(
                "The proof obtains a stronger physical-chart residual rate from `ResidualChartData.residual_jetRate` "
                "and then weakens it to the public iteration gain."
            ),
            additive_decomposition_available=True,
            warning=(
                "The exact decomposition is available in the proof dependencies, not in the theorem statement. "
                "Keep the definition-level physical split separate from harmonic extraction bookkeeping."
            ),
        ),
        ProducerStep(
            step_id="ledger.native_residual",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.Invariant.native_residual",
            role="combines independently bounded native residual channels before physical-chart conversion",
            exact_fact=(
                "The harmonic source sum has native gain h*(1/2+sigma), the selected mean has h*(1+sigma), "
                "and base/Gaussian/alias channels have stronger all-power or arbitrarily-flat inputs before weakening."
            ),
            additive_decomposition_available=True,
            warning="This identifies the harmonic sum as the native exponent bottleneck, not a final force-norm share.",
        ),
        ProducerStep(
            step_id="identity.harmonic_reconstruction",
            source_file="NavierStokes/ActualCycleResidualBounds.lean",
            source_declaration="ActualCycleResidualBounds.Invariant.fullResidual_decomposition",
            role="exact local reconstruction of the normalized residual",
            exact_fact=(
                "Full residual equals the finite harmonic residual-block sum plus meanGoodResidual plus errors.total. "
                "ExcludedErrors.total is base + Gaussian + alias."
            ),
            additive_decomposition_available=True,
            warning=(
                "Gaussian and alias are coupled extraction bookkeeping: they are subtracted inside residualBlock "
                "and restored in the reconstruction, so they are not independent physical forcing atoms."
            ),
        ),
    ]


def current_attribution_frontier() -> dict:
    chain = finite_residual_producer_chain()
    exact = exact_residual_attribution_report()
    return {
        "schema": "stage-residual-attribution-v2",
        "source_lock": {
            "repository": "openai/NavierStokesAndEuler",
            "commit": SOURCE_COMMIT,
        },
        "producer_chain": [step.to_dict() for step in chain],
        "frontier": (
            "bind each harmonic residualBlock to its concrete correction-stage mechanism and carry that split through "
            "spatial localization, time activation, and final force construction"
        ),
        "exact_residual_ledger": exact,
        "interpretation": (
            "The aggregate finite-residual theorem has now been unpacked far enough to expose exact residual identities "
            "and a native exponent bottleneck. The next frontier is mechanism attribution *inside* the harmonic sum; "
            "the current evidence does not assign force-norm fractions to individual mechanisms."
        ),
        "next_questions": [
            "Which exact stage constructors contribute to each per-label residualBlock?",
            "Can the harmonic bottleneck be split into primary, particular, signed, temporal, rank, and correction atoms without double counting?",
            "Which of those atoms survive spatial cutoff, periodization, and time activation?",
            "Does the source provide independent physical-chart rates for any harmonic sub-atom?",
            "If sigma is raised by 1/5 on the same literal state, does the h/5 native gain survive the final physical residual theorem?",
        ],
        "hard_findings": {
            "final_assembly_contains_termwise_finite_residual_split": False,
            "actual_stage_adapter_contains_termwise_finite_residual_split": False,
            "finite_residual_rate_producer_located": True,
            "producer_termwise_decomposition_extracted": True,
            "physical_definition_decomposition_extracted": True,
            "harmonic_reconstruction_extracted": True,
            "harmonic_native_bottleneck_identified": True,
            "force_priority_numerically_ranked": False,
            "force_norm_reduced": False,
        },
    }
