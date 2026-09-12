import NavierStokes.ActualIterationLedger

/-!
# v5.8 positive-stage physical gain slack

The source ledger proves native exponents with fixed positive margins above the
shared printed gain `gain h j = h*j/10`.  This file tests whether the *smallest*
of those visible margins can be retained simultaneously across all five
positive-stage metadata channels.

For positive stages define

  boostedGain(h,kappa,j) = gain(h,j) + h * (3/5 - kappa).

The wave-potential channel has exactly this native exponent.  The two mean
channels and both pressure channels have strictly larger fixed margins under
the source assumption `kappa <= 1/100000`.

This is an arithmetic/metadata promotion only.  It does not yet rebuild the
actual `StageEstimates` record, alter stage zero, change a diagonal schedule,
or reduce the final forcing norm.
-/

noncomputable section

namespace NavierStokes.V580PositiveStageGainSlack

open NavierStokes.ActualIterationLedger
open NavierStokes.PhysicalStageBounds NavierStokes.ProblemStatement

/-- The largest common fixed positive-stage boost immediately visible from the
source's conservative wave-potential exponent. -/
noncomputable def boostedGain (h κ : ℝ) (j : ℕ) : ℝ :=
  gain h j + h * (3 / 5 - κ)

theorem boostedGain_eq_waveNative (h κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    boostedGain h κ j = h * waveNative κ j := by
  exact (wave_physical_gap h κ hj).symm

theorem boostedGain_le_wavePressure {h κ : ℝ} (hh : 0 ≤ h)
    (hκ : κ ≤ 1 / 100000) {j : ℕ} (hj : 1 ≤ j) :
    boostedGain h κ j ≤ h * wavePressureNative κ j := by
  rw [pressure_physical_gap h κ hj]
  unfold boostedGain
  have hmargin : (3 / 5 : ℝ) - κ ≤ 11 / 10 - κ := by linarith
  have hm := mul_le_mul_of_nonneg_left hmargin hh
  linarith

theorem boostedGain_le_mean {h κ : ℝ} (hh : 0 ≤ h)
    (hκ : κ ≤ 1 / 100000) {j : ℕ} (hj : 1 ≤ j) :
    boostedGain h κ j ≤ h * meanNative κ j := by
  rw [mean_physical_gap h κ hj]
  unfold boostedGain
  have hkhalf : κ ≤ 1 / 2 := by linarith
  have hmargin : (3 / 5 : ℝ) - κ ≤ 11 / 10 - 2 * κ := by linarith
  have hm := mul_le_mul_of_nonneg_left hmargin hh
  linarith

section StageInputs

universe uDA uDP uIA uKA uIP uKP

variable {h κ qbig : ℝ}
  {DA : Type uDA} {DP : Type uDP}
  [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  {IA : Type uIA} {KA : Type uKA} {IP : Type uIP} {KP : Type uKP}

variable
  {WA : ℕ → WaveData h DA IA KA (Fin 3)}
  {MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2)}
  {MB : ℕ → MeanData h (CoordinateAlgebra.A h)}
  {WP : ℕ → WaveData h DP IP KP Unit}
  {MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h)}

/-- All five metadata channels support the same stronger positive-stage gain.
The potential channel is the bottleneck; the other four channels retain slack. -/
theorem StageMetadata.boosted_gain_inequalities
    (H : StageMetadata WA MA MB WP MP κ)
    (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) :
    (∀ j, 1 ≤ j → boostedGain h κ j ≤
      h * (WA j).alpha + (WA j).shift + (offsets h).wavePotential) ∧
    (∀ j, 1 ≤ j → boostedGain h κ j ≤
      h * (MA j).alpha + (offsets h).meanStream) ∧
    (∀ j, 1 ≤ j → boostedGain h κ j ≤
      h * (MB j).alpha + (offsets h).directAngular) ∧
    (∀ j, 1 ≤ j → boostedGain h κ j ≤
      h * (WP j).alpha + (WP j).shift + (offsets h).wavePressure) ∧
    (∀ j, 1 ≤ j → boostedGain h κ j ≤
      h * (MP j).alpha + (offsets h).meanPressure) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have ha := mul_le_mul_of_nonneg_left (H.wavePotential j hj) hh
    have hs := H.wavePotentialShift j hj
    have hg := boostedGain_eq_waveNative h κ hj
    dsimp only [offsets]
    rw [hg]
    linarith
  · intro j hj
    have ha := mul_le_mul_of_nonneg_left (H.meanStream j hj) hh
    have hg := boostedGain_le_mean hh hκ hj
    dsimp only [offsets]
    linarith
  · intro j hj
    have ha := mul_le_mul_of_nonneg_left (H.directAngular j hj) hh
    have hg := boostedGain_le_mean hh hκ hj
    dsimp only [offsets]
    linarith
  · intro j hj
    have ha := mul_le_mul_of_nonneg_left (H.wavePressure j hj) hh
    have hs := H.wavePressureShift j hj
    have hg := boostedGain_le_wavePressure hh hκ hj
    dsimp only [offsets]
    linarith
  · intro j hj
    have ha := mul_le_mul_of_nonneg_left (H.meanPressure j hj) hh
    have hg := boostedGain_le_mean hh hκ hj
    dsimp only [offsets]
    linarith

end StageInputs

/-- At the pinned source parameters the common positive-stage boost is almost
`3h/5`, substantially larger than the candidate `h/5` sigma shift. -/
theorem pinned_boost_formula (h : ℝ) :
    h * (3 / 5 - ActualIterationLedger.kappa) = h * (59999 / 100000 : ℝ) := by
  norm_num [ActualIterationLedger.kappa]

end NavierStokes.V580PositiveStageGainSlack
