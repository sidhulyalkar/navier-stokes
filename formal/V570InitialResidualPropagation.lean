import NavierStokes.ActualInitialization

/-!
# v5.7 propagation of a 9/10 primary linear gain through initialization

This file isolates a downstream question from the improved linear-wave proof.
It assumes a `9/10` bound for the literal initialized linear-good block and
checks whether the already-formalized nonlinear self-transport and mean update
preserve that exponent.

The result is conditional on the supplied `hlinear : ... (9/10)`.  It does
not by itself establish that the actual primary has that stronger linear
bound; `V570ImprovedLinearRemainder.lean` tests that upstream claim separately.
-/

noncomputable section

namespace NavierStokes.V570InitialResidualPropagation

open Set Filter Function WeightedClasses CorrectionState
open HarmonicMeanInteraction HarmonicWaveInteraction UniformHarmonicInteraction
open scoped ContDiff Topology

open NavierStokes.ActualInitialization

/-- The source's zero-mean nonlinear residual theorem admits the full `9/10`
linear gain because, at the actual primary velocity exponent `1/2`, its
quadratic ceiling is `2*(1/2) - kappa = 9/10`. -/
theorem zeroMean_residual_nine_tenths
    {B N0 : ℕ}
    (hprimary : UniformVelocity strip envelope (1/2) (primaryBlock (B := B) (N0 := N0)))
    (hlinear : UniformVelocity strip envelope (9/10)
      (fun l : Index B N0 => linearGoodBlock
        (CorrectionInitialization.ActualPrimary.commonContext B)
        (primaryBlock l) (primaryBlock l) (gaussianBlock l).velocity))
    (hphase : ∀ (l : Index B N0) n, ContDiffOn ℝ ∞ (phase l n) strip.domain)
    (hdiv : ∀ l : Index B N0, ModeSolenoidal strip
      (CorrectionInitialization.ActualPrimary.commonContext B) (primaryBlock l)) :
    UniformVelocity strip envelope (9/10)
      (fun l : Index B N0 => HarmonicResidual.residualBlock
        (CorrectionInitialization.ActualPrimary.commonContext B) (sourceState B N0)
        (primaryBlock l) (gaussianBlock l).velocity 0) := by
  exact zeroMean_residual_uniform
    (CorrectionInitialization.ActualPrimary.commonContext B)
    (operators B) (radius_pos B) (sourceState B N0) (sourceState_mean B N0)
    primaryBlock (fun l => (gaussianBlock l).velocity) 0 hprimary primaryBlock_zeroMode
    primaryBlock_band hphase
    (fun l n => (CorrectionInitialization.ActualPrimary.chartCoefficients_frequency_pos l.2 l.1 n).ne')
    hdiv (fun l n x _ => envelope_nonneg l n x) (fun l n x _ => envelope_le_one l n x)
    (fun _ _ _ _ _ => rfl) hlinear (by norm_num [ChartScales.kappa])

/-- If the primary linear-good block is improved to `9/10`, then the same
source mean-stage theorem preserves `9/10` after the actual initialized mean.
The key mean increment is already proved at `9/10` by
`CorrectionStep.meanIncrement_of_cumulative`. -/
theorem initial_residual_uniform_of_primary_nine_tenths
    {B N0 : ℕ}
    (hprimary : UniformVelocity strip envelope (1/2) (primaryBlock (B := B) (N0 := N0)))
    (hlinear : UniformVelocity strip envelope (9/10)
      (fun l : Index B N0 => linearGoodBlock
        (CorrectionInitialization.ActualPrimary.commonContext B)
        (primaryBlock l) (primaryBlock l) (gaussianBlock l).velocity))
    (hphase : ∀ (l : Index B N0) n, ContDiffOn ℝ ∞ (phase l n) strip.domain)
    (hdiv : ∀ l : Index B N0, ModeSolenoidal strip
      (CorrectionInitialization.ActualPrimary.commonContext B) (primaryBlock l))
    {C : ℕ → Index B N0 → Set Point}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted strip C 0
      (fun n l x => slowNormal (CorrectionInitialization.ActualPrimary.commonContext B)
        (operators B) (radius_pos B) (phase l) n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted strip C (-(1/2))
      (fun n l _ => (primaryBlock l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted strip C (-(1/2))
      (fun n l _ => ((primaryBlock l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ strip.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (primaryBlock l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hmean : CorrectionState.CumulativeBounds strip (initialState B N0)) :
    UniformVelocity strip envelope (9/10) (initialResidualBlock (B := B) (N0 := N0)) := by
  have hzero : UniformVelocity strip envelope (9/10)
      (fun l : Index B N0 => HarmonicResidual.residualBlock
        (CorrectionInitialization.ActualPrimary.commonContext B) (sourceState B N0)
        (primaryBlock l) (gaussianBlock l).velocity 0) :=
    zeroMean_residual_nine_tenths hprimary hlinear hphase hdiv
  have he : (initialState B N0).mean =
      MeanIncrementBounds.updated (sourceState B N0).mean (initialState B N0).mean := by
    rw [sourceState_mean]
    simp only [MeanIncrementBounds.updated, zero_add]
  have hs : MeanIncrementBounds.SmoothTriple strip.domain (sourceState B N0).mean := by
    rw [sourceState_mean]
    exact ⟨fun _ => contDiffOn_const, fun _ => contDiffOn_const, fun _ => contDiffOn_const⟩
  exact CorrectionStep.meanStage_residual_uniform
    (CorrectionInitialization.ActualPrimary.commonContext B) (operators B)
    (by norm_num [ChartScales.kappa]) (radius_pos B) (sourceState B N0) (initialState B N0)
    (initialState B N0).mean he (base_bounds B).smooth hs
    (CorrectionStep.meanIncrement_of_cumulative hmean.velocity) primaryBlock hprimary
    hNormal hFreq hAng hz (fun l => (gaussianBlock l).velocity) 0 0
    (fun _ _ _ => by simpa using (HarmonicResidual.band_zero 0 (D := Point)))
    hzero (by norm_num)

/-- The two source ceilings that govern the propagation are exactly saturated
at the actual parameters. -/
theorem nonlinear_ceiling_nine_tenths :
    (9/10 : ℝ) = (1/2) + (1/2) - ChartScales.kappa := by
  norm_num [ChartScales.kappa]

theorem mean_stage_ceiling_nine_tenths :
    (9/10 : ℝ) = (1/2) + (9/10) - (1/2) := by
  norm_num

end NavierStokes.V570InitialResidualPropagation
