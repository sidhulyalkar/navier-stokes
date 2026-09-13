import NavierStokes.GluedStageEstimates

/-!
# v5.8: boosted signed-wave and mean bounds on the glued path

The literal actual candidate uses `GluedStageEstimates`: the current-band
particular field is handled separately, while the signed wave and all mean
increments retain their native source records.

This file spends the common source-visible margin

  h * (3/5 - kappa)

on the signed/mean side only.  No field, source class, derivative loss, or
analytic iterate is changed.
-/

noncomputable section

namespace NavierStokes.V580GluedSignedMeanSlack

open Set Function Filter ProblemStatement
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPhysicalStageBounds
open scoped ContDiff Topology BigOperators

noncomputable def boost : ℝ := h * (3 / 5 - ChartScales.kappa)

noncomputable def boostedGain (j : ℕ) : ℝ :=
  ActualIterationLedger.gain h j + boost

variable {B N0 N : ℕ}
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}
  (R : ActualStageEstimates.RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : GluedStageEstimates.SignedInputs D I K)

/-- The signed potential channel exactly reaches the v5.8 common boost when
its native exponent and shift saturate their current metadata bounds. -/
private theorem potential_gain_boosted (j : ℕ) :
    boostedGain (j + 1) ≤
      h * (W.potential j).alpha + (W.potential j).shift + h := by
  have hgap := ActualIterationLedger.wave_physical_gap h ChartScales.kappa
    (show 1 ≤ j + 1 by omega)
  rw [← ActualStageEstimates.nativePotential_eq_ledger j] at hgap
  have ha := mul_le_mul_of_nonneg_left (W.potential_exponent j) outgoing.data.h_pos.le
  rw [W.potential_shift]
  unfold boostedGain boost
  linarith

/-- The signed pressure channel has an extra half-power beyond the common
boost. -/
private theorem pressure_gain_boosted (j : ℕ) :
    boostedGain (j + 1) ≤
      h * (W.pressure j).alpha + (W.pressure j).shift + 2 * CoordinateAlgebra.A h := by
  have hgap := ActualIterationLedger.pressure_physical_gap h ChartScales.kappa
    (show 1 ≤ j + 1 by omega)
  rw [← ActualStageEstimates.nativePressure_eq_ledger j] at hgap
  have ha := mul_le_mul_of_nonneg_left (W.pressure_exponent j) outgoing.data.h_pos.le
  rw [W.pressure_shift]
  unfold boostedGain boost
  have hm : h * (3 / 5 - ChartScales.kappa) ≤
      h * (11 / 10 - ChartScales.kappa) := by
    nlinarith [outgoing.data.h_pos.le]
  linarith

/-- Every mean-generated channel has more room than the common signed-potential
margin. -/
private theorem mean_gain_boosted (j : ℕ) :
    boostedGain (j + 1) ≤
      h * (1 + ActualIterationLedger.sigma j - 2 * ChartScales.kappa) + 0 := by
  have hgap := ActualIterationLedger.mean_physical_gap h ChartScales.kappa
    (show 1 ≤ j + 1 by omega)
  rw [← ActualStageEstimates.nativeMean_eq_ledger j] at hgap
  unfold boostedGain boost
  norm_num [ChartScales.kappa] at hgap ⊢
  nlinarith [outgoing.data.h_pos.le]

/-- The literal signed potential plus temporal/rank mean streams supports the
common boosted gain. -/
theorem signedMeanPotential_bound_boosted {qbig : ℝ}
    (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    GluedStageEstimates.Bound qbig (GluedStageEstimates.signedMeanPotential R M hN W j) m
      (boostedGain (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m) := by
  have hs0 := (W.potential j).vector_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half (potential_gain_boosted R M hN W j) m
  have hs := weaken_bound (qbig := qbig)
    (s := boostedGain (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (sub_le_sub_left (le_max_left _ _) _) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have ht := weaken_bound
    (s := boostedGain (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.temporalInput R M hN j).angular_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain_boosted R M hN W j) m)
  have hr := weaken_bound
    (s := boostedGain (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.rankInput R M hN j).angular_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain_boosted R M hN W j) m)
  have ss : ContDiffOn ℝ ∞ (W.potential j).vector
      (CutStageEstimates.physicalSublevel h qbig) :=
    ((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
      inter_subset_left
  have st := (ActualStageEstimates.temporalInput R M hN j).angular_smooth
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  exact add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (ss.add st)
    ((ActualStageEstimates.rankInput R M hN j).angular_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq)
    (add_bounds outgoing.data.h_pos outgoing.data.h_lt_half ss st hs ht) hr

/-- The literal signed pressure plus pressure-mean increment supports the common
boosted gain. -/
theorem signedMeanPressure_bound_boosted {qbig : ℝ}
    (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    GluedStageEstimates.Bound qbig (GluedStageEstimates.signedMeanPressure R M hN W j) m
      (boostedGain (j + 1) -
        PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m) := by
  have hs0 := (W.pressure j).pressure_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half (pressure_gain_boosted R M hN W j) m
  have hs := weaken_bound (qbig := qbig)
    (s := boostedGain (j + 1) -
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (sub_le_sub_left (le_max_left _ _) _) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hm := weaken_bound
    (s := boostedGain (j + 1) -
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.pressureInput R M hN j).field_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain_boosted R M hN W j) m)
  exact add_bounds outgoing.data.h_pos outgoing.data.h_lt_half
    (((W.pressure j).pressure_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
      inter_subset_left)
    ((ActualStageEstimates.pressureInput R M hN j).field_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq) hs hm

/-- The direct angular mean increment is comfortably above the same target. -/
theorem direct_bound_boosted {qbig : ℝ}
    (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    GluedStageEstimates.Bound qbig (GluedStageEstimates.direct R M hN j) m
      (boostedGain (j + 1) - PhysicalStageBounds.directLoss h 0 m) :=
  (ActualStageEstimates.angularInput R M hN j).angular_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain_boosted R M hN W j) m

end NavierStokes.V580GluedSignedMeanSlack
