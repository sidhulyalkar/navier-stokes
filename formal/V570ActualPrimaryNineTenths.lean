import NavierStokes.ActualInitialization
import NavierStokes.V570ImprovedLocalizedGood

/-!
# v5.7 actual-primary 9/10 bridge

This file composes the source-locked localized sharpening with the literal
actual primary construction.  It does not change the primary field.  Instead,
it replays the source's control-cell cover and uniform slicing with the sharper
localized retained-good estimate.

The chain proved here is:

  localized retained-good at `1 - kappa`
    -> actual chart linear-good at `1 - kappa`
    -> sliced harmonic coefficients at `9/10`
    -> literal initialized linear-good block at `9/10`.

No cycle-invariant, stage-deletion, force-reduction, or unforced-blowup claim
is made here.
-/

noncomputable section

namespace NavierStokes.ActualPrimaryBounds

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryCopyBounds
open CorrectionInitialization
open scoped ContDiff Topology BigOperators

/-- The literal actual primary family satisfies the sharpened localized
retained-good estimate.  This is the source theorem `actual_local_good` with
only the generic retained-good estimate replaced by the v5.7 sharpening. -/
theorem actual_local_good_improved {B N0 : ℕ} :
    LocalizedWaveBounds.LocalWave fullStrip
      (controlCell (B := B) (N0 := N0))
      (fun n i => fullEnvelope i.1 n)
      (1 - ChartScales.kappa)
      ((actualFamily (B := B) (N0 := N0)).retainedGood fullStrip (directions B)) := by
  convert! NavierStokes.V570ImprovedLocalizedGood.retainedGood_class_improved
      (actual_local_inputs (B := B) (N0 := N0))
      (show ChartScales.kappa ≤ 1 / 2 by norm_num [ChartScales.kappa])
      (normalFloor_pos B N0)
      (fun _ _ _ hx hc => (actualFamily_normal_range hx hc).1)
      (fun _ _ _ hx hc => (actualFamily_normal_range hx hc).2)
      (inverse_carrier_local (B := B) (N0 := N0)) using 1
  norm_num

/-- Replay the source's local-to-uniform cover with the sharpened local
estimate.  The field and support cover are unchanged. -/
theorem chart_good_uniform_improved {B N0 : ℕ} :
    LabelSumBounds.UniformWaveClass fullStrip
      (fullEnvelope (B := B) (N0 := N0))
      (1 - ChartScales.kappa)
      (fun l => (ActualPrimary.piece region l.1 l.2).linearGood) := by
  have hg := actual_local_good_improved (B := B) (N0 := N0)
  rw [actualFamily_good_eq] at hg
  have hj : PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * fullEnvelope l n x)
      (1 - ChartScales.kappa)
      (fun (l : SignedLabel B N0) n k => controlCell n (l, k))
      (fun l n _k => (ActualPrimary.piece region l.1 l.2).linearGood n) :=
    hg.to_uniformLocalJets
  apply PeriodizedWaveBounds.uniformClass_of_local_germs
    (fun l n x _ => mul_nonneg (Real.sqrt_nonneg _) (fullEnvelope_nonneg l n x)) hj
  intro l n x hx
  rcases actual_input_cover l n hx with ⟨k, hk⟩ | ⟨ha, hp⟩
  · exact Or.inl ⟨k, hk, Filter.EventuallyEq.rfl⟩
  · have hz := ((actualFamily (B := B) (N0 := N0)).outputs_zero_germs
      fullStrip (directions B) (i := (l, 0)) ha hp).2.2
    rw [actualFamily_good_eq] at hz
    exact Or.inr hz

end NavierStokes.ActualPrimaryBounds

namespace NavierStokes.ActualInitialization

open Set Filter Function WeightedClasses CorrectionState
open HarmonicMeanInteraction HarmonicWaveInteraction UniformHarmonicInteraction
open scoped ContDiff Topology

/-- The source currently weakens these coefficients to `7/10`.  The improved
actual chart theorem leaves enough room to retain `9/10` after slicing and
harmonic pairing. -/
theorem good_coefficients_uniform_nine_tenths (B N0 : ℕ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass strip envelope (9 / 10)
      (fun l : Index B N0 => fun n x => (goodBlock l).velocity n i j x) := by
  have hg : LabelSumBounds.UniformWaveClass (productStrip strip)
      (fun l : Index B N0 => fun n x => envelope l n x.1)
      (1 - ChartScales.kappa)
      (fun l => (primaryPiece l).linearGood) :=
    (ActualPrimaryBounds.chart_good_uniform_improved (B := B) (N0 := N0)).reindex Prod.swap
  have hs := (UniformBlockBounds.uniform_slice (s := strip)
    (w := fun l n x => Real.sqrt (strip.zeta x) * envelope l n x) hg).map
      (ContinuousLinearMap.proj i)
  exact (UniformBlockBounds.pair_uniform hs 1 j).mono_exponent
    (show (9 / 10 : ℝ) ≤ 1 - ChartScales.kappa by norm_num [ChartScales.kappa])

/-- The literal initialized linear-good block therefore admits exponent
`9/10`; all identities, smoothness facts, Gaussian coefficients and primary
fields are the source's existing objects. -/
theorem linearGood_uniform_nine_tenths (B N0 : ℕ) :
    UniformVelocity strip envelope (9 / 10)
      (fun l : Index B N0 => linearGoodBlock (ActualPrimary.commonContext B)
        (primaryBlock l) (primaryBlock l) (gaussianBlock l).velocity) := by
  apply linearGood_uniform_of_identity B N0 (primary_uniform B N0) phase_smooth_full
    exact_amplitude_smooth_full exact_pressure_smooth_full
    (fun i j _ => good_coefficients_uniform_nine_tenths B N0 i j)
  intro l n x hx i
  exact ActualPrimaryDynamics.linearResidual_eq_on_strip l.2 l.1 n hx.1 i

end NavierStokes.ActualInitialization
