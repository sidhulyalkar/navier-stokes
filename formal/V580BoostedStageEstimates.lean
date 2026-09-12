import NavierStokes.ActualStageEstimates
import NavierStokes.V580BoostedRawStages

/-!
# v5.8 boosted StageEstimates for the unchanged actual fields

This file tests the construction-level consequence of the source-visible
positive-stage slack.  It keeps the literal actual potential, direct, and
pressure fields unchanged, but asks whether the mixed diagonal interface can
be certified with the stronger common gain

  gain(h,j) + h * (3/5 - kappa).

The raw positive-stage bounds are supplied by `V580BoostedRawStages`.  The
finite background is unchanged.  For the finite residual we intentionally use
`ActualCycleResidualBounds.Invariant.residual_jetRate` *before* the pinned
source weakens its exponent to the published gain.

A successful compile proves a stronger `StageEstimates` certificate for the
same physical fields.  It does not change the analytic iterate and does not by
itself imply a smaller forcing norm.
-/

noncomputable section

namespace NavierStokes.ActualStageEstimates

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPhysicalStageBounds
open scoped ContDiff Topology BigOperators

namespace V580BoostedStageEstimates

open NavierStokes.V580BoostedRawStages

variable {B N0 N : ℕ}

section StageEstimates

variable {DP DS DA0 DP0 : Type}
  [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0]
  [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {IP KP IS KS IA0 KA0 IP0 KP0 : Type*}
  (R : RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : WaveInputs DP IP KP DS IS KS)
  (qbig : ℝ)
  (WA : PhysicalStageBounds.WaveData h DA0 IA0 KA0 (Fin 3))
  (WP : PhysicalStageBounds.WaveData h DP0 IP0 KP0 Unit)
  (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)

variable {qbig A Bdirect P}
  (e : Representations R M hN W qbig WA WP A Bdirect P)
  (hq : qbig ≤ ChartScales.Q N)

include e hq

private theorem boost_nonneg :
    0 ≤ V580BoostedRawStages.boost h ChartScales.kappa := by
  unfold V580BoostedRawStages.boost
  norm_num [ChartScales.kappa]
  exact outgoing.data.h_pos.le

private theorem boostedGain_zero_nonneg :
    0 ≤ V580BoostedRawStages.boostedGain h ChartScales.kappa 0 := by
  unfold V580BoostedRawStages.boostedGain
  rw [ActualIterationLedger.gain_zero]
  simpa only [zero_add] using
    (boost_nonneg (R := R) (M := M) (hN := hN) (W := W) (WA := WA) (WP := WP)
      (e := e) (hq := hq))

private theorem boostedGain_pos {j : ℕ} (hj : 1 ≤ j) :
    0 < V580BoostedRawStages.boostedGain h ChartScales.kappa j := by
  have hg := ActualIterationLedger.gain_pos outgoing.data.h_pos hj
  have hb := boost_nonneg (R := R) (M := M) (hN := hN) (W := W) (WA := WA) (WP := WP)
    (e := e) (hq := hq)
  unfold V580BoostedRawStages.boostedGain
  linarith

private theorem boostedGain_mono :
    Monotone (V580BoostedRawStages.boostedGain h ChartScales.kappa) := by
  intro j k hjk
  unfold V580BoostedRawStages.boostedGain
  have hg := (ActualIterationLedger.gain_monotone outgoing.data.h_pos.le) hjk
  linarith

private theorem boostedGain_top :
    Tendsto (V580BoostedRawStages.boostedGain h ChartScales.kappa) atTop atTop := by
  change Tendsto
    (fun j => ActualIterationLedger.gain h j + V580BoostedRawStages.boost h ChartScales.kappa)
    atTop atTop
  exact ActualIterationLedger.gain_add_tendsto_atTop outgoing.data.h_pos
    (V580BoostedRawStages.boost h ChartScales.kappa)

/-- The boosted shared gain still lies strictly below the source's literal
finite-residual wave exponent.  This is the margin that lets us avoid a new
residual PDE estimate. -/
private theorem boostedGain_le_residualWave (J : ℕ) :
    V580BoostedRawStages.boostedGain h ChartScales.kappa J ≤
      h * ActualIterationLedger.residualWave J := by
  rw [ActualIterationLedger.residual_physical_gap]
  unfold V580BoostedRawStages.boostedGain V580BoostedRawStages.boost
  norm_num [ChartScales.kappa]
  nlinarith [outgoing.data.h_pos.le]

/-- The complete mixed-diagonal estimate record with unchanged literal fields
and the stronger source-visible common gain. -/
noncomputable def boostedStageEstimates_of_representations
    (hqbig : 0 < qbig) {Nres : ℕ} (hNres : 4 ≤ Nres)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B Nres
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let Cyc := cycleInputs R M hN W
  have hmeta := cycleInputs_metadata R M hN W
  have hscale := cycleInputs_validScale R M hN W hq
  have hraw := V580BoostedRawStages.represented_raw_bounds_boosted
    Cyc hmeta hscale outgoing.data.h_pos outgoing.data.h_lt_half
    ActualCyclePreservation.kappa_small A Bdirect P
    e.potential_succ e.direct_succ e.pressure_succ
  let CA := hraw.choose
  let CB := hraw.choose_spec.choose
  let CP := hraw.choose_spec.choose_spec.choose
  have hc := hraw.choose_spec.choose_spec.choose_spec
  refine {
    potential_smooth := e.potential_smooth R M hN W WA WP hq
    direct_smooth := e.direct_smooth R M hN W WA WP hq
    pressure_smooth := e.pressure_smooth R M hN W WA WP hq
    gain := V580BoostedRawStages.boostedGain h ChartScales.kappa
    gain_zero := boostedGain_zero_nonneg R M hN W WA WP e hq
    gain_pos := fun _ hj => boostedGain_pos R M hN W WA WP e hq hj
    gain_mono := boostedGain_mono R M hN W WA WP e hq
    gain_top := boostedGain_top R M hN W WA WP e hq
    potentialLoss := PhysicalStageBounds.potentialLoss h h 0
    directLoss := PhysicalStageBounds.directLoss h 0
    pressureLoss := PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0
    potentialConstant := CA
    directConstant := CB
    pressureConstant := CP
    potentialLog := fun _ _ => 0
    directLog := fun _ _ => 0
    pressureLog := fun _ _ => 0
    potential_bound := hc.2.1
    direct_bound := hc.2.2.1
    pressure_bound := hc.2.2.2
    backgroundLoss := backgroundLoss WA.alpha WA.shift
    residualLoss := ActualCycleResidualBounds.fixedLoss
    finite_background := ?_
    finite_residual := ?_ }
  · intro J m
    have hb := background_from_representations certificate modulation Cyc hmeta hscale
      ActualCyclePreservation.kappa_small hqbig upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
      (actualInitialAngularInput B N0 N hN) hq hq hq A Bdirect
      e.potential_zero e.direct_zero e.potential_succ e.direct_succ J m
    simp only [backgroundLoss, actualInitialTemporalInput, actualInitialRankInput,
      actualInitialAngularInput, MeanInput.ofMoving, min_self] at hb ⊢
    exact hb
  · intro J m
    let HJ := ActualCyclePreservation.broad_invariant (R.invariant J)
    have he := HJ.residual_jetRate hGeom hNres
      (ActualCycleResidualBounds.actual_iterate_base_error
        (fun _ => ActualCycleParameters.fixedParameters B N0) J)
      (d J) m
    have hg := boostedGain_le_residualWave R M hN W WA WP e hq J
    have hg' : V580BoostedRawStages.boostedGain h ChartScales.kappa J ≤
        h * (1 / 2 + ActualIterationLedger.sigma J) := by
      simpa only [ActualIterationLedger.residualWave, ExponentLedger.waveExponent] using hg
    exact he.weaken ActualCycleResidualBounds.origin_positive_small
      (sub_le_sub_right hg' (ActualCycleResidualBounds.fixedLoss m))

/-- Ledger identity for downstream audits: the fields/losses are unchanged and
only the common gain is promoted. -/
theorem boostedStageEstimates_ledger
    (hqbig : 0 < qbig) {Nres : ℕ} (hNres : 4 ≤ Nres)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B Nres
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    let E := boostedStageEstimates_of_representations R M hN W WA WP e hq hqbig hNres hGeom d
    E.gain = V580BoostedRawStages.boostedGain h ChartScales.kappa ∧
      E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 ∧
      E.directLoss = PhysicalStageBounds.directLoss h 0 ∧
      E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 ∧
      E.backgroundLoss = backgroundLoss WA.alpha WA.shift ∧
      E.residualLoss = ActualCycleResidualBounds.fixedLoss :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end StageEstimates

end V580BoostedStageEstimates

end NavierStokes.ActualStageEstimates
