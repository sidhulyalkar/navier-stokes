import NavierStokes.ActualIterationLedger

/-!
# v5.8 common boosted gain sequence

The pinned source proves fixed positive margins above the printed stage gain.
The smallest visible positive-stage margin is the wave-potential margin

  h * (3/5 - kappa).

This file packages that margin into a candidate common gain sequence

  boostedGain(h,kappa,j) = gain(h,j) + h * (3/5 - kappa)

and checks the global gain properties required by `StageEstimates`. It also
proves that the finite residual has enough source-backed margin to support the
same boosted gain at every prefix index, including `J = 0`.

This does not yet prove the raw potential/direct/pressure stage bounds at the
boosted gain. Those are a separate physical-adapter obligation.
-/

noncomputable section

namespace NavierStokes.V580BoostedGainSequence

open Filter
open NavierStokes.ActualIterationLedger

noncomputable def boost (h κ : ℝ) : ℝ := h * (3 / 5 - κ)

noncomputable def boostedGain (h κ : ℝ) (j : ℕ) : ℝ :=
  gain h j + boost h κ

/-- The common boost is nonnegative throughout the source admissible kappa
range. -/
theorem boost_nonneg {h κ : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) :
    0 ≤ boost h κ := by
  unfold boost
  exact mul_nonneg hh (by linarith)

/-- `StageEstimates` only requires a nonnegative gain at index zero. -/
theorem boostedGain_zero_nonneg {h κ : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) :
    0 ≤ boostedGain h κ 0 := by
  simpa [boostedGain, gain_zero] using boost_nonneg hh hκ

/-- Positive stages retain strictly positive gain. -/
theorem boostedGain_pos {h κ : ℝ} (hh : 0 < h) (hκ : κ ≤ 1 / 100000)
    {j : ℕ} (hj : 1 ≤ j) : 0 < boostedGain h κ j := by
  have hg := gain_pos hh hj
  have hb := boost_nonneg hh.le hκ
  unfold boostedGain
  linarith

/-- Adding one fixed margin preserves stage monotonicity. -/
theorem boostedGain_monotone {h κ : ℝ} (hh : 0 ≤ h) :
    Monotone (boostedGain h κ) := by
  intro j k hjk
  unfold boostedGain
  have hg := (gain_monotone hh) hjk
  linarith

/-- Adding one fixed margin preserves divergence of the gain sequence. -/
theorem boostedGain_tendsto_atTop {h κ : ℝ} (hh : 0 < h) :
    Tendsto (boostedGain h κ) atTop atTop := by
  change Tendsto (fun j => gain h j + boost h κ) atTop atTop
  exact gain_add_tendsto_atTop hh (boost h κ)

/-- The source finite-residual exponent retains an exact positive margin after
spending the common stage boost. -/
theorem residual_boosted_gap (h κ : ℝ) (J : ℕ) :
    h * residualWave J - boostedGain h κ J = h * (1 / 10 + κ) := by
  rw [residual_physical_gap]
  unfold boostedGain boost
  ring

/-- For nonnegative kappa, the boosted gain still lies below the literal
finite-residual wave exponent at every prefix, including prefix zero. -/
theorem boostedGain_le_residualWave {h κ : ℝ} (hh : 0 ≤ h) (hκ0 : 0 ≤ κ)
    (J : ℕ) :
    boostedGain h κ J ≤ h * residualWave J := by
  have hgap : 0 ≤ h * residualWave J - boostedGain h κ J := by
    rw [residual_boosted_gap]
    exact mul_nonneg hh (by linarith)
  exact sub_nonneg.mp hgap

/-- Consequently the source's stronger residual rate may be weakened to the
same boosted common gain, with the existing residual derivative loss. -/
theorem boostedGain_le_residualRate {h κ : ℝ} (hh : 0 ≤ h) (hκ0 : 0 ≤ κ)
    (beta : ℝ) (J m : ℕ) :
    boostedGain h κ J - residualLoss h beta m ≤ residualRate h beta J m := by
  unfold residualRate
  have hres := boostedGain_le_residualWave hh hκ0 J
  linarith

/-- At the pinned source kappa, the candidate common boost is exactly
`59999/100000 * h`. -/
theorem pinned_boost_formula (h : ℝ) :
    boost h ActualIterationLedger.kappa = h * (59999 / 100000 : ℝ) := by
  norm_num [boost, ActualIterationLedger.kappa]

/-- The already-visible source margin is strictly larger than the candidate
`h/5` improvement from shifting sigma by `1/5`. -/
theorem pinned_boost_gt_sigma_shift {h : ℝ} (hh : 0 < h) :
    h / 5 < boost h ActualIterationLedger.kappa := by
  rw [pinned_boost_formula]
  nlinarith

end NavierStokes.V580BoostedGainSequence
