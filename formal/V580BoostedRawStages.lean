import NavierStokes.ActualPhysicalStageBounds

/-!
# v5.8 boosted raw physical stage bounds

The source's low-level physical increment estimates are generic in the target
gain.  The published `ActualPhysicalStageBounds.CycleInputs` adapter chooses
`ActualIterationLedger.gain`, even though the native metadata leaves a fixed
positive margin above that choice.

This file spends the smallest common visible margin

  h * (3/5 - kappa)

and checks whether the *same literal positive correction fields* satisfy raw
potential, direct-angular, and pressure bounds at

  boostedGain(h,kappa,j) = gain(h,j) + h*(3/5-kappa).

The theorem is deliberately limited to raw physical stages.  It does not yet
construct a full `MixedCandidateAssembly.StageEstimates` record or claim any
final-force norm reduction.
-/

noncomputable section

namespace NavierStokes.V580BoostedRawStages

open Set
open NavierStokes.ActualPhysicalStageBounds
open NavierStokes.ActualIterationLedger

noncomputable def boost (h κ : ℝ) : ℝ := h * (3 / 5 - κ)

noncomputable def boostedGain (h κ : ℝ) (j : ℕ) : ℝ :=
  gain h j + boost h κ

private theorem boosted_eq_waveNative {h κ : ℝ} (j : ℕ) (hj : 1 ≤ j) :
    boostedGain h κ j = h * waveNative κ j := by
  unfold boostedGain boost
  exact (wave_physical_gap h κ hj).symm

private theorem boosted_le_wavePressure {h κ : ℝ} (hh : 0 ≤ h)
    {j : ℕ} (hj : 1 ≤ j) :
    boostedGain h κ j ≤ h * wavePressureNative κ j := by
  rw [pressure_physical_gap h κ hj]
  unfold boostedGain boost
  have hm : h * (3 / 5 - κ) ≤ h * (11 / 10 - κ) :=
    mul_le_mul_of_nonneg_left (by linarith) hh
  linarith

private theorem boosted_le_mean {h κ : ℝ} (hh : 0 ≤ h)
    (hκ : κ ≤ 1 / 100000) {j : ℕ} (hj : 1 ≤ j) :
    boostedGain h κ j ≤ h * meanNative κ j := by
  rw [mean_physical_gap h κ hj]
  unfold boostedGain boost
  have hm : h * (3 / 5 - κ) ≤ h * (11 / 10 - 2 * κ) := by
    apply mul_le_mul_of_nonneg_left _ hh
    linarith
  linarith

private theorem potential_gain_boosted {h κ α s : ℝ}
    (hh : 0 ≤ h) (k : ℕ)
    (hα : waveNative κ (k + 1) ≤ α) (hs : -h ≤ s) :
    boostedGain h κ (k + 1) ≤ h * α + s + h := by
  have hg := boosted_eq_waveNative (h := h) (κ := κ) (k + 1) (Nat.succ_pos k)
  have ha := mul_le_mul_of_nonneg_left hα hh
  rw [hg]
  linarith

private theorem pressure_gain_boosted {h κ α s : ℝ}
    (hh : 0 ≤ h) (k : ℕ)
    (hα : wavePressureNative κ (k + 1) ≤ α)
    (hs : -(2 * CoordinateAlgebra.A h) ≤ s) :
    boostedGain h κ (k + 1) ≤ h * α + s + 2 * CoordinateAlgebra.A h := by
  have hg := boosted_le_wavePressure (h := h) (κ := κ) hh (Nat.succ_pos k)
  have ha := mul_le_mul_of_nonneg_left hα hh
  linarith

private theorem mean_gain_boosted {h κ α : ℝ}
    (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) (k : ℕ)
    (hα : meanNative κ (k + 1) ≤ α) :
    boostedGain h κ (k + 1) ≤ h * α + 0 := by
  have hg := boosted_le_mean (h := h) (κ := κ) hh hκ (Nat.succ_pos k)
  have ha := mul_le_mul_of_nonneg_left hα hh
  linarith

universe uDP uDS uIP uKP uIS uKS

variable {h κ qbig : ℝ}
  {DP : Type uDP} {DS : Type uDS}
  [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS]
  {IP : Type uIP} {KP : Type uKP} {IS : Type uIS} {KS : Type uKS}

/-- The literal potential increment of cycle `k` supports the boosted common
gain at physical stage `k+1`. -/
theorem potential_bound_boosted
    (D : CycleInputs h DP IP KP DS IS KS)
    (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.potential k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (boostedGain h κ (k + 1) - PhysicalStageBounds.potentialLoss h h 0 m) :=
  potentialIncrement_bound
    (D.particularPotential k) (D.signedPotential k) (D.temporal k) (D.rank k)
    hh hh1 (Q.temporal k) (Q.rank k)
    (potential_gain_boosted hh.le k (H.particularPotential k) (H.particularPotentialShift k))
    (potential_gain_boosted hh.le k (H.signedPotential k) (H.signedPotentialShift k))
    (mean_gain_boosted hh.le hκ k (H.temporal k))
    (mean_gain_boosted hh.le hκ k (H.rank k)) m

/-- The literal direct-angular increment supports the same boosted gain. -/
theorem direct_bound_boosted
    (D : CycleInputs h DP IP KP DS IS KS)
    (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.direct k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (boostedGain h κ (k + 1) - PhysicalStageBounds.directLoss h 0 m) :=
  (D.angular k).angular_bound_with_gain hh hh1 (Q.angular k)
    (mean_gain_boosted hh.le hκ k (H.angular k)) m

/-- The literal pressure increment supports the same boosted gain. -/
theorem pressure_bound_boosted
    (D : CycleInputs h DP IP KP DS IS KS)
    (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.pressureField k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (boostedGain h κ (k + 1) -
          PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m) :=
  pressureIncrement_bound
    (D.particularPressure k) (D.signedPressure k) (D.pressure k)
    hh hh1 (Q.pressure k)
    (pressure_gain_boosted hh.le k
      (H.particularPressure k) (H.particularPressureShift k))
    (pressure_gain_boosted hh.le k
      (H.signedPressure k) (H.signedPressureShift k))
    (mean_gain_boosted hh.le hκ k (H.pressure k)) m

/-- Exact representation identities transfer the boosted positive-stage bounds
to the same literal candidate stage families.  Index zero is deliberately
absent exactly as in the source theorem `CycleInputs.represented_raw_bounds`. -/
theorem represented_raw_bounds_boosted
    (D : CycleInputs h DP IP KP DS IS KS)
    (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (A B : ℕ → VelocityField) (P : ℕ → PressureField)
    (hA : ∀ k, EqOn (D.potential k) (A (k + 1))
      (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ k, EqOn (D.direct k) (B (k + 1))
      (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ k, EqOn (D.pressureField k) (P (k + 1))
      (CutStageEstimates.physicalSublevel h qbig)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A (boostedGain h κ)
        (PhysicalStageBounds.potentialLoss h h 0) CA (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B (boostedGain h κ)
        (PhysicalStageBounds.directLoss h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P (boostedGain h κ)
        (PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0)
        CP (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  obtain ⟨CA, hCA, hrawA⟩ := raw_of_positive_bounds (fun k m =>
    bound_congr hh hh1 (hA k)
      (potential_bound_boosted D H Q hh hh1 hκ k m))
  obtain ⟨CB, hCB, hrawB⟩ := raw_of_positive_bounds (fun k m =>
    bound_congr hh hh1 (hB k)
      (direct_bound_boosted D H Q hh hh1 hκ k m))
  obtain ⟨CP, hCP, hrawP⟩ := raw_of_positive_bounds (fun k m =>
    bound_congr hh hh1 (hP k)
      (pressure_bound_boosted D H Q hh hh1 hκ k m))
  exact ⟨CA, CB, CP, fun j m => ⟨hCA j m, hCB j m, hCP j m⟩,
    hrawA, hrawB, hrawP⟩

end NavierStokes.V580BoostedRawStages
