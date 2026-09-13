import NavierStokes.ActualCandidateAssembly
import NavierStokes.V580BoostedGluedStageEstimates

/-!
# v5.8 boosted certificate for the literal actual candidate

This module does not construct new velocity or pressure fields.  It instantiates
the v5.8 boosted `GluedStageEstimates` adapter on exactly the literal data used
by `ActualCandidateAssembly.estimates`:

* the same correction run;
* the same mean cycle input;
* the same native signed-wave inputs;
* the same potential/direct/pressure stage sequences;
* the same exact representation equalities;
* the same physical finite-prefix realizations.

If this file compiles, the literal candidate stage families admit a stronger
finite-stage certificate with gain

  ActualIterationLedger.gain h j + h * (3/5 - ChartScales.kappa).

This alone does not assert that the source's existentially selected diagonal
schedule is strictly smaller, and it does not prove a smaller norm for the
final force.
-/

noncomputable section

namespace NavierStokes.V580ActualBoostedCandidate

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

/-- The exact literal stage families of the pinned actual candidate support the
boosted finite-stage estimate record. -/
noncomputable def estimates (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    MixedCandidateAssembly.StageEstimates h (ActualCandidateConstruction.qbig B N0)
      (ActualCandidateAssembly.potentialStages B N0 hN)
      (ActualCandidateAssembly.directStages B N0 hN)
      (ActualCandidateAssembly.pressureStages B N0 hN) :=
  V580BoostedGluedStageEstimates.actualStageEstimates_boosted
    (ActualCandidateAssembly.runData B N0 hN)
    (ActualCandidateAssembly.meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0)
    (ActualSignedWaveData.signedInputs B N0 hN)
    (ActualCyclePreservation.state_coherent B N0 hN)
    le_rfl
    (ActualCandidateConstruction.qbig_pos B N0)
    hN
    (ActualCandidateAssembly.potentialStages B N0 hN)
    (ActualCandidateAssembly.directStages B N0 hN)
    (ActualCandidateAssembly.pressureStages B N0 hN)
    (ActualCandidateAssembly.representations B N0 hN)
    (ActualCandidateAssembly.physicalData B N0 hN)

/-- The literal candidate has the same losses as the pinned source record while
its certified common gain is promoted by the v5.8 margin. -/
theorem estimates_ledger (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    let E := estimates B N0 hN
    E.gain = V580BoostedGluedStageEstimates.boostedGain ∧
      E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 ∧
      E.directLoss = PhysicalStageBounds.directLoss h 0 ∧
      E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 ∧
      E.backgroundLoss = ActualStageEstimates.backgroundLoss 1 (-h) ∧
      E.residualLoss = ActualCycleResidualBounds.fixedLoss := by
  exact V580BoostedGluedStageEstimates.actualStageEstimates_boosted_ledger
    (ActualCandidateAssembly.runData B N0 hN)
    (ActualCandidateAssembly.meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0)
    (ActualSignedWaveData.signedInputs B N0 hN)
    (ActualCyclePreservation.state_coherent B N0 hN)
    le_rfl
    (ActualCandidateConstruction.qbig_pos B N0)
    hN
    (ActualCandidateAssembly.potentialStages B N0 hN)
    (ActualCandidateAssembly.directStages B N0 hN)
    (ActualCandidateAssembly.pressureStages B N0 hN)
    (ActualCandidateAssembly.representations B N0 hN)
    (ActualCandidateAssembly.physicalData B N0 hN)

/-- The boost over the published stage gain is exactly `59999/100000 * h` at
the pinned iteration kappa. -/
theorem exact_gain_improvement (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    (estimates B N0 hN).gain j =
      ActualIterationLedger.gain h j + h * (59999 / 100000 : ℝ) := by
  rw [(estimates_ledger B N0 hN).1]
  unfold V580BoostedGluedStageEstimates.boostedGain
    V580BoostedGluedStageEstimates.boost
  norm_num [ChartScales.kappa]

end NavierStokes.V580ActualBoostedCandidate
