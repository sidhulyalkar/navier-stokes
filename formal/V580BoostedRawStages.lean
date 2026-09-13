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

open Set ProblemStatement
open NavierStokes.ActualPhysicalStageBounds
open NavierStokes.ActualIterationLedger

noncomputable def boost (h κ : ℝ) : ℝ := h * (3 / 5 - κ)

noncomputable def boostedGain (h κ : ℝ) (j : ℕ) : ℝ :=
  ActualIterationLedger.gain h j + boost h κ

@[simp] theorem boostedGain_zero (h κ : ℝ) :
    boostedGain h κ 0 = boost h κ := by
  simp [boostedGain]

@[simp] theorem boostedGain_succ (h κ : ℝ) (j : ℕ) :
    boostedGain h κ (j + 1) = ActualIterationLedger.gain h (j + 1) + boost h κ := rfl

/-- The potential channel exactly supplies the common boost. -/
theorem potential_gain_boosted
    {h κ : ℝ} (hh : 0 ≤ h) {k : ℕ} {native shift : ℝ}
    (hnative : ActualIterationLedger.waveNative κ (k + 1) ≤ native)
    (hshift : -h ≤ shift) :
    boostedGain h κ (k + 1) ≤ h * native + shift + h := by
  unfold boostedGain boost
  have hbase := ActualIterationLedger.wave_physical_gap h κ (show 1 ≤ k + 1 by omega)
  have hnative_mul : h * ActualIterationLedger.waveNative κ (k + 1) ≤ h * native :=
    mul_le_mul_of_nonneg_left hnative hh
  rw [hbase] at hnative_mul
  linarith

/-- Direct mean-generated angular fields have much more margin than the common
potential-channel boost. -/
theorem mean_gain_boosted
    {h κ : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) {k : ℕ} {native : ℝ}
    (hnative : ActualIterationLedger.meanNative κ (k + 1) ≤ native) :
    boostedGain h κ (k + 1) ≤ h * native := by
  unfold boostedGain boost
  have hbase := ActualIterationLedger.mean_physical_gap h κ (show 1 ≤ k + 1 by omega)
  have hnative_mul : h * ActualIterationLedger.meanNative κ (k + 1) ≤ h * native :=
    mul_le_mul_of_nonneg_left hnative hh
  rw [hbase] at hnative_mul
  have hmargin : 3 / 5 - κ ≤ 11 / 10 - 2 * κ := by linarith
  have := mul_le_mul_of_nonneg_left hmargin hh
  linarith

/-- The wave-pressure channel also has more than the common potential margin. -/
theorem pressure_gain_boosted
    {h κ : ℝ} (hh : 0 ≤ h) {k : ℕ} {native shift : ℝ}
    (hnative : ActualIterationLedger.wavePressureNative κ (k + 1) ≤ native)
    (hshift : -(2 * CoordinateAlgebra.A h) ≤ shift) :
    boostedGain h κ (k + 1) ≤ h * native + shift + 2 * CoordinateAlgebra.A h := by
  unfold boostedGain boost
  have hbase := ActualIterationLedger.pressure_physical_gap h κ (show 1 ≤ k + 1 by omega)
  have hnative_mul : h * ActualIterationLedger.wavePressureNative κ (k + 1) ≤ h * native :=
    mul_le_mul_of_nonneg_left hnative hh
  rw [hbase] at hnative_mul
  have hmargin : (3 / 5 : ℝ) - κ ≤ 11 / 10 - κ := by norm_num
  have := mul_le_mul_of_nonneg_left hmargin hh
  linarith

section CycleInputs

variable {h κ qbig : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (D : CycleInputs h DP IP KP DS IS KS)

/-- Same literal potential increment, sharpened only by spending the visible
metadata slack. -/
theorem potential_bound_boosted (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.potential k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (boostedGain h κ (k + 1) - PhysicalStageBounds.potentialLoss h h 0 m) :=
  potentialIncrement_bound
    (D.particular k) (D.signed k) (D.temporal k) (D.rank k)
    hh hh1 (Q.temporal k) (Q.rank k)
    (potential_gain_boosted hh.le (H.particularPotential k) (H.particularPotentialShift k))
    (potential_gain_boosted hh.le (H.signedPotential k) (H.signedPotentialShift k))
    (mean_gain_boosted hh.le hκ (H.temporal k))
    (mean_gain_boosted hh.le hκ (H.rank k)) m

/-- Same literal direct angular increment at the boosted common gain. -/
theorem direct_bound_boosted (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.direct k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (boostedGain h κ (k + 1) - PhysicalStageBounds.directLoss h 0 m) :=
  (D.angular k).angular_bound_with_gain hh hh1 (Q.angular k)
    (mean_gain_boosted hh.le hκ (H.angular k)) m

/-- Same literal pressure increment at the boosted common gain. -/
theorem pressure_bound_boosted (H : D.Metadata κ) (Q : D.ValidScale qbig)
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

end CycleInputs

end NavierStokes.V580BoostedRawStages
