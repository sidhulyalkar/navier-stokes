import NavierStokes.GluedStageEstimates

/-!
# v5.8: boosted bounds for the literal glued current-particular fields

`ActualCandidateAssembly` does not represent the current-band particular wave
through the generic copy-family `WaveInputs` route.  It uses
`GluedStageEstimates.currentPotential/currentPressure`, built directly from the
actual current-band physical fields.

The source first proves these fields at the stronger exponent

  h * ((1/2 + sigma j) + 1/2) - currentLoss

and then weakens to the published physical gain.  This file checks that the
same literal fields can instead be weakened only to

  gain h (j+1) + h*(3/5-kappa) - stageLoss.

No field, source class, gluing argument, derivative loss, or PDE estimate is
changed.
-/

noncomputable section

namespace NavierStokes.V580GluedParticularSlack

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary (h outgoing)
open NavierStokes.GluedStageEstimates

noncomputable def boost : ℝ := h * (3 / 5 - ChartScales.kappa)

noncomputable def boostedGain (j : ℕ) : ℝ :=
  ActualIterationLedger.gain h j + boost

/-- The literal current-particular native exponent has strictly more room than
the v5.8 common boost. -/
theorem boostedGain_le_current_exponent (j : ℕ) :
    boostedGain (j + 1) ≤
      h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) := by
  unfold boostedGain boost ActualIterationLedger.gain
  rw [ActualIterationLedger.sigma_formula]
  norm_num [ChartScales.kappa]
  nlinarith [outgoing.data.h_pos.le]

section ActualRun

variable {B N0 N : ℕ}
  (R : ActualStageEstimates.RunData B N0)

/-- The exact glued current-particular potential field supports the common
v5.8 boost. -/
theorem current_potential_bound_boosted
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hN : 4 ≤ N) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    GluedStageEstimates.Bound qbig (GluedStageEstimates.currentPotential B N0 N j) m
      (boostedGain (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m) := by
  obtain ⟨K, hK, hb⟩ := GluedStageEstimates.localPotential_bound_of_modes
    (R.invariant j) hGeom m
    (fun k hk => ActualCurrentParticularBounds.current_potential_mode_bound
      (R.invariant j) hGeom k hk m)
  have hg : GluedStageEstimates.Bound qbig
      (GluedStageEstimates.currentPotential B N0 N j) m
      (h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) -
        ActualCurrentParticularBounds.currentLoss h (2 * h) m) :=
    GluedStageEstimates.glued_bound_of_local m
      (GluedStageEstimates.current_compatible R C hGeom j N).1 hq
      ⟨K, hK, fun n hn w hw _ hqw => hb n (hN.trans hn) w hw hqw⟩
  apply ActualPhysicalStageBounds.weaken_bound
    outgoing.data.h_pos outgoing.data.h_lt_half _ hg
  have hgain := boostedGain_le_current_exponent j
  have hloss := GluedStageEstimates.current_potential_loss_le m
  unfold ActualCurrentParticularBounds.currentLoss
  linarith

/-- The exact glued current-particular pressure field also supports the same
common boost. -/
theorem current_pressure_bound_boosted
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hN : 4 ≤ N) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    GluedStageEstimates.Bound qbig (GluedStageEstimates.currentPressure B N0 N j) m
      (boostedGain (j + 1) -
        PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m) := by
  obtain ⟨K, hK, hb⟩ := GluedStageEstimates.localPressure_bound_of_modes
    (R.invariant j) hGeom m
    (fun k hk => ActualCurrentParticularBounds.current_pressure_mode_bound
      (R.invariant j) hGeom k hk m)
  have hg : GluedStageEstimates.Bound qbig
      (GluedStageEstimates.currentPressure B N0 N j) m
      (h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) -
        ActualCurrentParticularBounds.currentLoss (2 * CoordinateAlgebra.A h) (2 * h) m) :=
    GluedStageEstimates.glued_bound_of_local m
      (GluedStageEstimates.current_compatible R C hGeom j N).2 hq
      ⟨K, hK, fun n hn w hw _ hqw => hb n (hN.trans hn) w hw hqw⟩
  apply ActualPhysicalStageBounds.weaken_bound
    outgoing.data.h_pos outgoing.data.h_lt_half _ hg
  have hgain := boostedGain_le_current_exponent j
  have hloss := GluedStageEstimates.current_pressure_loss_le m
  unfold ActualCurrentParticularBounds.currentLoss
  linarith

end ActualRun

end NavierStokes.V580GluedParticularSlack
