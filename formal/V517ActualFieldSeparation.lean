import NavierStokes.ActualCandidateAssembly
import NavierStokes.V516AxisFloorSeparation
import NavierStokes.V517FloorSeparatedStageEstimates

/-!
# v5.17: actual field separation for two selected schedules

Instantiate the floor-separated schedule pair on the literal
`ActualCandidateAssembly.estimates` record.

Both schedules are `MixedCandidateWitness.SelectedSchedule` witnesses for the
same actual potential/direct/pressure stage families.  At the explicit axis
point selected by the smaller zeroth scale, v5.16 then proves that their
assembled mixed velocities are different.  The nonvanishing input is discharged
by the exact pinned slow-base origin formula.
-/

noncomputable section

namespace NavierStokes.V517ActualFieldSeparation

open Set Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

theorem actual_stage_families_have_floor_separated_selected_pair
    (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (lower : ℕ) :
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      lower ≤ Bsmall ∧
      1 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) <
        ActualCandidateConstruction.qbig B N0 ∧
      MixedCandidateWitness.SelectedSchedule h
        (ActualCandidateConstruction.qbig B N0)
        (ActualCandidateAssembly.potentialStages B N0 hN)
        (ActualCandidateAssembly.directStages B N0 hN)
        (ActualCandidateAssembly.pressureStages B N0 hN) aSmall ∧
      MixedCandidateWitness.SelectedSchedule h
        (ActualCandidateConstruction.qbig B N0)
        (ActualCandidateAssembly.potentialStages B N0 hN)
        (ActualCandidateAssembly.directStages B N0 hN)
        (ActualCandidateAssembly.pressureStages B N0 hN) aLarge ∧
      let small : ℕ → ℝ := fun j => (aSmall j : ℝ)
      let large : ℕ → ℝ := fun j => (aLarge j : ℝ)
      let tStar : ℝ := 1 - (2 / 5 : ℝ) / small 0
      MixedPeriodicAssembly.velocity
          (SolenoidalDiagonal.potentialSum small
            (PhysicalWaveSum.physicalQ h)
            (ActualCandidateAssembly.potentialStages B N0 hN))
          (SolenoidalDiagonal.potentialSum small
            (PhysicalWaveSum.physicalQ h)
            (ActualCandidateAssembly.directStages B N0 hN))
          (tStar, 0) ≠
        MixedPeriodicAssembly.velocity
          (SolenoidalDiagonal.potentialSum large
            (PhysicalWaveSum.physicalQ h)
            (ActualCandidateAssembly.potentialStages B N0 hN))
          (SolenoidalDiagonal.potentialSum large
            (PhysicalWaveSum.physicalQ h)
            (ActualCandidateAssembly.directStages B N0 hN))
          (tStar, 0) := by
  obtain ⟨Bsmall, Blarge, aSmall, aLarge,
      hBLower, hBOne, hBLarge, hs0, hl0, hRatio, hqStar,
      hsSelected, hlSelected⟩ :=
    V517FloorSeparatedStageEstimates.stageEstimates_exists_floor_separated_selected
      (ActualCandidateAssembly.estimates B N0 hN)
      outgoing.data.h_pos outgoing.data.h_lt_half
      (ActualCandidateConstruction.qbig_pos B N0) lower

  have hsTop :
      Tendsto (fun j => (aSmall j : ℝ)) atTop atTop :=
    hsSelected.2.2.2.2.1
  have hlTop :
      Tendsto (fun j => (aLarge j : ℝ)) atTop atTop :=
    hlSelected.2.2.2.2.1
  have hsPosR : (0 : ℝ) < (aSmall 0 : ℝ) := by
    exact_mod_cast hsSelected.2.1 0
  have hRatioR :
      5 * (aSmall 0 : ℝ) < 2 * (aLarge 0 : ℝ) := by
    exact_mod_cast hRatio

  have hne :=
    V516AxisFloorSeparation.actualBase_physical_axis_velocity_ne
      certificate modulation upper B
      outgoing.data.h_pos outgoing.data.h_lt_half
      (ActualCandidateAssembly.directData B N0 hN)
      hsTop hlTop hsPosR hRatioR hqStar
      (ActualCandidateAssembly.initialPotential_axisZeroOn B N0)
      (ActualCandidateAssembly.positivePotential_axisZeroOn B N0 hN)

  refine ⟨Bsmall, Blarge, aSmall, aLarge,
    hBLower, hBOne, hBLarge, hs0, hl0, hRatio, hqStar,
    hsSelected, hlSelected, ?_⟩
  simpa only [
    ActualCandidateAssembly.potentialStages,
    ActualCandidateAssembly.directStages,
    GermCandidateAssembly.potentialStages
  ] using hne

end NavierStokes.V517ActualFieldSeparation
