import NavierStokes.ActualInitialMean

/-!
# v5.7 actual initialized debt at sigma = 2/5

The source's `InitialRankBounds` record exports `DefectBounds ... (1/5)`, but
the underlying five-row cancellation theorem is parameterized by `σ` and only
requires

  1 + σ ≤ H + 9/10 - 2κ.

For the literal initial rank increment, `H = 1 - ChartScales.kappa` and
`ChartScales.kappa = 1/10`, giving an available exponent of `8/5`.  This file
replays the already-proved actual support/smoothness hypotheses and asks the
underlying theorem directly for `σ = 2/5`.
-/

noncomputable section

namespace NavierStokes.V570InitialDebtTwoFifths

open Set Filter CorrectionState CorrectionInitialization WeightedClasses
open VariableGaugeMean LocalSignedRequest
open scoped ContDiff Topology BigOperators

open NavierStokes.ActualInitialMean

/-- The literal initialized pressure/rank debt satisfies the stronger
`σ = 2/5` defect bound, provided solely by the already constructed rank
increment and the existing five-row cancellation theorem. -/
theorem initial_debt_bounds_two_fifths (B N0 : ℕ) :
    DefectBounds slowStrip (2 / 5) (ActualPrimary.commonContext B) (initialized B N0) := by
  let d := primary_mean_data B N0
  unfold PrimaryData at d
  let t := temporal_bounds B N0
  have hd := d.temporal_debt_bounds t
  have hg := ActualPrimary.rank_geometry ActualPrimary.standardRegion B (temporal B N0) hd.smooth
  have hslow := CommonBaseContext.context_isSlow ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion.carrier (CommonWindow.index ActualPrimary.h)
  let p := primary B N0
  let v := temporal B N0
  have hmean : v.mean = temporalIncrementState ActualPrimary.commonGauge ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B) p := by
    change MeanIncrementBounds.updated (seed B N0).mean _ = _
    rw [d.mean_zero]
    simp only [MeanIncrementBounds.updated, zero_add]
  have hmc : MeanIncrementBounds.SmoothTriple
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier) v.mean := by
    simpa only [hmean] using t.increment_smooth
  have hms : CorrectionStep.GaugeSupportedTriple ActualPrimary.commonGauge.radial.inner
      ActualPrimary.commonGauge.radial.outer (MovingMomentBounds.qLength (2 * ActualPrimary.h))
      ActualPrimary.standardRegion.carrier v.mean := by
    simpa only [hmean] using t.increment_support
  have hcov : v.covariance = (seed B N0).covariance := by
    change (temporalStageState ActualPrimary.commonGauge ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B) p).covariance = _
    simpa [p, primary] using CorrectionStep.gaugeTemporalStage_covariance
      ActualPrimary.commonGauge ActualPrimary.h (CommonWindow.index ActualPrimary.h) axial
      (ActualPrimary.commonContext B) p
  have hWc : ∀ i j, MeanIncrementBounds.SmoothOn
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier) (v.covariance i j) := by
    simpa only [hcov] using d.covariance_smooth
  have hWs : ∀ i j, CorrectionStep.GaugeSupported ActualPrimary.commonGauge.radial.inner
      ActualPrimary.commonGauge.radial.outer (MovingMomentBounds.qLength (2 * ActualPrimary.h))
      ActualPrimary.standardRegion.carrier (v.covariance i j) := by
    simpa only [hcov] using d.covariance_support
  have hr := rank_bounds B N0
  have hdef := MovingMomentBounds.rankStage_defectBounds
    ActualPrimary.standardRegion ActualPrimary.commonGauge ActualPrimary.rankData
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
    (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale d.gauge_length axial (ActualPrimary.commonContext B) v hg
    d.localOperators d.base_smooth hmc hms hWc hWs hslow.2.1 hslow.2.2
    d.operators d.base t.cumulative.velocity hr.increment
    (by norm_num [ChartScales.kappa] : (9 / 10 : ℝ) ≤ 1 - ChartScales.kappa)
    (by norm_num [ChartScales.kappa] :
      (1 : ℝ) + 2 / 5 ≤ (1 - ChartScales.kappa) + 9 / 10 - 2 * ChartScales.kappa)
  simpa [v, initialized, GaugeInitialization.initializedBands] using hdef

end NavierStokes.V570InitialDebtTwoFifths
