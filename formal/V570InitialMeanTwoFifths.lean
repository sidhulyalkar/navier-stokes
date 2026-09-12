import NavierStokes.ActualInitialMean

/-!
# v5.7 actual initialized mean at sigma = 2/5

The existing initializer exports `MeanResidualBounds ... (1/5)`, but its
rank-stage angular and axial estimates are already proved at exponent 149/100.
Since the `σ = 2/5` mean target is only `1 + σ = 7/5`, no new analytic
estimate is required for this gate.
-/

noncomputable section

namespace NavierStokes.V570InitialMeanTwoFifths

open Set Filter CorrectionState CorrectionInitialization WeightedClasses
open scoped ContDiff Topology BigOperators

open NavierStokes.ActualInitialMean

/-- The literal initialized mean residual satisfies the stronger `σ = 2/5`
class using the already-proved rank-stage estimates. -/
theorem initial_mean_bounds_two_fifths (B N0 : ℕ) :
    MeanResidualBounds strip (2 / 5) (ActualPrimary.commonContext B) (initialized B N0) := by
  have hr := rank_bounds B N0
  apply initialized_mean_bounds_of_rank B N0
  · exact hr.theta.mono_exponent
      (by norm_num : (1 : ℝ) + 2 / 5 ≤ 149 / 100)
  · exact hr.axial_residual.mono_exponent
      (by norm_num : (1 : ℝ) + 2 / 5 ≤ 149 / 100)

/-- The five-row defect theorem has arithmetic room for the same target when
fed the actual rank increment exponent `H = 1 - ChartScales.kappa`.  This is
only the exponent check; the literal debt theorem is audited separately. -/
theorem debt_two_fifths_margin :
    (1 : ℝ) + 2 / 5 ≤
      (1 - ChartScales.kappa) + 9 / 10 - 2 * ChartScales.kappa := by
  norm_num [ChartScales.kappa]

end NavierStokes.V570InitialMeanTwoFifths
