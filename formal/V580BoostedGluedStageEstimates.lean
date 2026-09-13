import NavierStokes.GluedStageEstimates
import NavierStokes.V580GluedParticularSlack
import NavierStokes.V580GluedSignedMeanSlack

/-!
# v5.8 boosted StageEstimates on the literal glued candidate path

`ActualCandidateAssembly` uses `GluedStageEstimates`, not the simpler pure
copy-family stage adapter.  This file rebuilds that exact glued interface with
one bookkeeping change only:

  gain(j) := ActualIterationLedger.gain h j + h*(3/5-kappa).

The literal current-band particular fields, signed waves, mean increments,
initial background, derivative losses, physical realizations and finite
Navier-Stokes residual are unchanged.

This is still a finite-stage certificate.  It does not assert a smaller final
force norm and does not alter the singular candidate fields.
-/

noncomputable section

namespace NavierStokes.V580BoostedGluedStageEstimates

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPhysicalStageBounds
open scoped ContDiff Topology BigOperators

noncomputable def boost : ℝ := h * (3 / 5 - ChartScales.kappa)

noncomputable def boostedGain (j : ℕ) : ℝ :=
  ActualIterationLedger.gain h j + boost

private theorem boost_nonneg : 0 ≤ boost := by
  unfold boost
  norm_num [ChartScales.kappa]
  exact outgoing.data.h_pos.le

private theorem boostedGain_nonneg (j : ℕ) : 0 ≤ boostedGain j := by
  unfold boostedGain
  exact add_nonneg (ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le j) boost_nonneg

private theorem boostedGain_pos {j : ℕ} (hj : 1 ≤ j) : 0 < boostedGain j := by
  unfold boostedGain
  have hg := ActualIterationLedger.gain_pos outgoing.data.h_pos hj
  linarith [boost_nonneg]

private theorem boostedGain_mono : Monotone boostedGain := by
  intro j k hjk
  unfold boostedGain
  exact add_le_add_right
    ((ActualIterationLedger.gain_monotone outgoing.data.h_pos.le) hjk) boost

private theorem boostedGain_top : Tendsto boostedGain atTop atTop := by
  change Tendsto (fun j => ActualIterationLedger.gain h j + boost) atTop atTop
  exact ActualIterationLedger.gain_add_tendsto_atTop outgoing.data.h_pos boost

private theorem boostedGain_le_residualWave (J : ℕ) :
    boostedGain J ≤ h * ActualIterationLedger.residualWave J := by
  rw [ActualIterationLedger.residual_physical_gap]
  unfold boostedGain boost
  norm_num [ChartScales.kappa]
  nlinarith [outgoing.data.h_pos.le]

section MixedSequence

variable {B N0 N : ℕ}
  {D DA0 DP0 : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0]
  [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {I K IA0 KA0 IP0 KP0 : Type*}
  (R : ActualStageEstimates.RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : GluedStageEstimates.SignedInputs D I K)
  (particularA : ℕ → VelocityField) (particularP : ℕ → PressureField)

variable {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)

/-- Combine a boosted particular-potential estimate with the independently
boosted signed/mean estimate. -/
theorem potential_bound_boosted {L : ℕ → ℝ}
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ j m, GluedStageEstimates.Bound qbig (particularA j) m
      (boostedGain (j + 1) - L m))
    (j m : ℕ) :
    GluedStageEstimates.Bound qbig
      (GluedStageEstimates.potential R M hN W particularA j) m
      (boostedGain (j + 1) - GluedStageEstimates.potentialLoss L m) := by
  rw [GluedStageEstimates.potential_eq]
  apply add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (hs j)
    (GluedStageEstimates.signedMeanPotential_smooth R M hN W hq j)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_left _ _) _) (hb j m)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_right _ _) _)
      (by
        simpa [boostedGain, boost,
          V580GluedSignedMeanSlack.boostedGain, V580GluedSignedMeanSlack.boost]
          using V580GluedSignedMeanSlack.signedMeanPotential_bound_boosted R M hN W hq j m)

/-- Pressure analogue of `potential_bound_boosted`. -/
theorem pressure_bound_boosted {L : ℕ → ℝ}
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ j m, GluedStageEstimates.Bound qbig (particularP j) m
      (boostedGain (j + 1) - L m))
    (j m : ℕ) :
    GluedStageEstimates.Bound qbig
      (GluedStageEstimates.pressure R M hN W particularP j) m
      (boostedGain (j + 1) - GluedStageEstimates.pressureLoss L m) := by
  rw [GluedStageEstimates.pressure_eq]
  apply add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (hs j)
    (GluedStageEstimates.signedMeanPressure_smooth R M hN W hq j)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_left _ _) _) (hb j m)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_right _ _) _)
      (by
        simpa [boostedGain, boost,
          V580GluedSignedMeanSlack.boostedGain, V580GluedSignedMeanSlack.boost]
          using V580GluedSignedMeanSlack.signedMeanPressure_bound_boosted R M hN W hq j m)

variable
  (WA : PhysicalStageBounds.WaveData h DA0 IA0 KA0 (Fin 3))
  (WP : PhysicalStageBounds.WaveData h DP0 IP0 KP0 Unit)
  (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)

variable {A Bdirect P}
  (e : GluedStageEstimates.Representations R M hN W particularA particularP
    WA WP A Bdirect P (qbig := qbig))

/-- Transfer all boosted positive-stage component estimates to the exact raw
candidate sequences. -/
theorem represented_raw_bounds_boosted {LA LP : ℕ → ℝ}
    (hsA : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hsP : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hbA : ∀ j m, GluedStageEstimates.Bound qbig (particularA j) m
      (boostedGain (j + 1) - LA m))
    (hbP : ∀ j m, GluedStageEstimates.Bound qbig (particularP j) m
      (boostedGain (j + 1) - LP m)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A boostedGain
        (GluedStageEstimates.potentialLoss LA) CA (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) Bdirect boostedGain
        (PhysicalStageBounds.directLoss h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P boostedGain
        (GluedStageEstimates.pressureLoss LP) CP (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  obtain ⟨CA, hCA, ha⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.potential_succ j)
      (potential_bound_boosted R M hN W particularA hq hsA hbA j m))
  obtain ⟨CB, hCB, hb⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.direct_succ j)
      (by
        simpa [boostedGain, boost,
          V580GluedSignedMeanSlack.boostedGain, V580GluedSignedMeanSlack.boost]
          using V580GluedSignedMeanSlack.direct_bound_boosted R M hN W hq j m))
  obtain ⟨CP, hCP, hp⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.pressure_succ j)
      (pressure_bound_boosted R M hN W particularP hq hsP hbP j m))
  exact ⟨CA, CB, CP, fun j m => ⟨hCA j m, hCB j m, hCP j m⟩, ha, hb, hp⟩

/-- The complete glued finite-stage record with unchanged fields and losses and
with only the common gain promoted. -/
noncomputable def stageEstimates_of_component_bounds_boosted {LA LP : ℕ → ℝ}
    (hsA : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hsP : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hbA : ∀ j m, GluedStageEstimates.Bound qbig (particularA j) m
      (boostedGain (j + 1) - LA m))
    (hbP : ∀ j m, GluedStageEstimates.Bound qbig (particularP j) m
      (boostedGain (j + 1) - LP m))
    (hqbig : 0 < qbig) (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let hr := represented_raw_bounds_boosted R M hN W particularA particularP hq WA WP e
    hsA hsP hbA hbP
  let CA := hr.choose
  let CB := hr.choose_spec.choose
  let CP := hr.choose_spec.choose_spec.choose
  have hc := hr.choose_spec.choose_spec.choose_spec
  have hsa := e.potential_smooth R M hN W particularA particularP hq WA WP hsA
  have hsb := e.direct_smooth R M hN W particularA particularP hq WA WP
  have hsp := e.pressure_smooth R M hN W particularA particularP hq WA WP hsP
  refine {
    potential_smooth := hsa
    direct_smooth := hsb
    pressure_smooth := hsp
    gain := boostedGain
    gain_zero := boostedGain_nonneg 0
    gain_pos := fun _ hj => boostedGain_pos hj
    gain_mono := boostedGain_mono
    gain_top := boostedGain_top
    potentialLoss := GluedStageEstimates.potentialLoss LA
    directLoss := PhysicalStageBounds.directLoss h 0
    pressureLoss := GluedStageEstimates.pressureLoss LP
    potentialConstant := CA
    directConstant := CB
    pressureConstant := CP
    potentialLog := fun _ _ => 0
    directLog := fun _ _ => 0
    pressureLog := fun _ _ => 0
    potential_bound := hc.2.1
    direct_bound := hc.2.2.1
    pressure_bound := hc.2.2.2
    backgroundLoss := GluedStageEstimates.backgroundLoss LA WA.alpha WA.shift
    residualLoss := ActualCycleResidualBounds.fixedLoss
    finite_background := ?_
    finite_residual := ?_ }
  · have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half qbig
    have hlU := InitializedPhysicalBackground.endpoint_sublevel
      outgoing.data.h_pos outgoing.data.h_lt_half hqbig
    apply MixedFiniteBackground.mixed_background_from_initial hU hlU
      (ActualBaseVelocityBounds.endpoint_past.and hlU)
      (ActualBaseVelocityBounds.endpoint_q_small outgoing.data.h_pos outgoing.data.h_lt_half)
      hsa hsb hc.2.1 hc.2.2.1 (fun j _ => boostedGain_nonneg j)
    intro m
    simpa only [actualInitialTemporalInput, actualInitialRankInput,
      actualInitialAngularInput, MeanInput.ofMoving, min_self] using
      GluedStageEstimates.represented_initial_rate certificate modulation upper B WA
        (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
        (actualInitialAngularInput B N0 N hN) hU hlU e.potential_zero e.direct_zero m
  · intro J m
    let HJ := ActualCyclePreservation.broad_invariant (R.invariant J)
    have he := HJ.residual_jetRate hGeom (by omega : 4 ≤ N + 1)
      (ActualCycleResidualBounds.actual_iterate_base_error
        (fun _ => ActualCycleParameters.fixedParameters B N0) J)
      (d J) m
    have hg := boostedGain_le_residualWave J
    have hg' : boostedGain J ≤ h * (1 / 2 + ActualIterationLedger.sigma J) := by
      simpa only [ActualIterationLedger.residualWave, ExponentLedger.waveExponent] using hg
    exact he.weaken ActualCycleResidualBounds.origin_positive_small
      (sub_le_sub_right hg' (ActualCycleResidualBounds.fixedLoss m))

end MixedSequence

section ActualRun

variable {B N0 N : ℕ}
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}
  (R : ActualStageEstimates.RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : GluedStageEstimates.SignedInputs D I K)

/-- Source-identical literal glued current-band fields packaged into the
boosted finite-stage record. -/
noncomputable def actualStageEstimates_boosted
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (hqbig : 0 < qbig)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)
    (e : GluedStageEstimates.ActualRepresentations R M hN W qbig A Bdirect P)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let E := stageEstimates_of_component_bounds_boosted R M hN W
    (GluedStageEstimates.currentPotential B N0 N)
    (GluedStageEstimates.currentPressure B N0 N) hq
    (InitialPhysicalData.potentialWaveData B N0)
    (InitialPhysicalData.pressureWaveData B N0) e
    (fun j => (GluedStageEstimates.current_fields_smooth R C hGeom hq j).1)
    (fun j => (GluedStageEstimates.current_fields_smooth R C hGeom hq j).2)
    (fun j m => by
      simpa [boostedGain, boost,
        V580GluedParticularSlack.boostedGain, V580GluedParticularSlack.boost]
        using V580GluedParticularSlack.current_potential_bound_boosted R C hGeom hN hq j m)
    (fun j m => by
      simpa [boostedGain, boost,
        V580GluedParticularSlack.boostedGain, V580GluedParticularSlack.boost]
        using V580GluedParticularSlack.current_pressure_bound_boosted R C hGeom hN hq j m)
    hqbig hGeom d
  have hA : E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 := by
    funext m
    exact max_self _
  have hP : E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 := by
    funext m
    exact max_self _
  have hBg : E.backgroundLoss = ActualStageEstimates.backgroundLoss 1 (-h) := by
    change GluedStageEstimates.backgroundLoss (PhysicalStageBounds.potentialLoss h h 0) 1 (-h) = _
    funext m
    simp only [GluedStageEstimates.backgroundLoss, ActualStageEstimates.backgroundLoss,
      MixedFiniteBackground.initialBackgroundLoss, GluedStageEstimates.potentialLoss, max_self]
  refine { E with
    potentialLoss := PhysicalStageBounds.potentialLoss h h 0
    pressureLoss := PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0
    backgroundLoss := ActualStageEstimates.backgroundLoss 1 (-h)
    potential_bound := ?_
    pressure_bound := ?_
    finite_background := ?_ }
  · rw [← hA]
    exact E.potential_bound
  · rw [← hP]
    exact E.pressure_bound
  · rw [← hBg]
    exact E.finite_background

/-- Ledger identity: the literal fields and all source losses are unchanged;
only the common gain is promoted. -/
theorem actualStageEstimates_boosted_ledger
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (hqbig : 0 < qbig)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)
    (e : GluedStageEstimates.ActualRepresentations R M hN W qbig A Bdirect P)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    let E := actualStageEstimates_boosted R M hN W C hq hqbig hGeom A Bdirect P e d
    E.gain = boostedGain ∧
      E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 ∧
      E.directLoss = PhysicalStageBounds.directLoss h 0 ∧
      E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 ∧
      E.backgroundLoss = ActualStageEstimates.backgroundLoss 1 (-h) ∧
      E.residualLoss = ActualCycleResidualBounds.fixedLoss :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ActualRun

end NavierStokes.V580BoostedGluedStageEstimates
