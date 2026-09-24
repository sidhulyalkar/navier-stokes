import NavierStokes.ActualCandidateAssembly
import NavierStokes.V517ActualFieldSeparation
import NavierStokes.V517PrescribedGermCandidate

/-!
# v5.17: two distinct actual forced candidates from one finite-stage dataset

Specialize the floor-separated pair to lower = 2.  Then the explicit comparison
time lies in the final activation plateau:

  t★ = 1 - (2/5)/aSmall(0) >= 4/5 > 3/4.

At the spatial origin, pinned periodization is exactly the original mixed
velocity, and time activation is exactly the identity at t★.  Therefore the
v5.16 raw mixed-velocity separation survives into the final candidate velocity
fields.

Both candidates use the same literal actual finite-stage families, support
data, endpoint extensions, and base.  Only the admissible cutoff schedule
changes.
-/

noncomputable section

namespace NavierStokes.V517ActualCandidatePair

open Set Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

theorem exists_two_distinct_actual_candidates
    (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      2 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      let ASmall := SolenoidalDiagonal.potentialSum
        (fun j => (aSmall j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (ActualCandidateAssembly.potentialStages B N0 hN)
      let DSmall := SolenoidalDiagonal.potentialSum
        (fun j => (aSmall j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (ActualCandidateAssembly.directStages B N0 hN)
      let PSmall := SolenoidalDiagonal.potentialSum
        (fun j => (aSmall j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (ActualCandidateAssembly.pressureStages B N0 hN)
      let ALarge := SolenoidalDiagonal.potentialSum
        (fun j => (aLarge j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (ActualCandidateAssembly.potentialStages B N0 hN)
      let DLarge := SolenoidalDiagonal.potentialSum
        (fun j => (aLarge j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (ActualCandidateAssembly.directStages B N0 hN)
      let PLarge := SolenoidalDiagonal.potentialSum
        (fun j => (aLarge j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (ActualCandidateAssembly.pressureStages B N0 hN)
      let uSmall := TimeLocalization.activatedVelocity
        (MixedPeriodicAssembly.periodicVelocity ASmall DSmall)
      let pSmall := TimeLocalization.activatedPressure
        (SpatialLocalization.periodicPressure PSmall)
      let uLarge := TimeLocalization.activatedVelocity
        (MixedPeriodicAssembly.periodicVelocity ALarge DLarge)
      let pLarge := TimeLocalization.activatedPressure
        (SpatialLocalization.periodicPressure PLarge)
      let tStar : ℝ := 1 - (2 / 5 : ℝ) / (aSmall 0 : ℝ)
      ∃ fSmall fLarge : VelocityField,
        CandidateProperties uSmall pSmall fSmall ∧
        CandidateProperties uLarge pLarge fLarge ∧
        uSmall (tStar, 0) ≠ uLarge (tStar, 0) := by
  obtain ⟨Bsmall, Blarge, aSmall, aLarge,
      hBLower, _, hBLarge, hs0, hl0, hRatio, _,
      hsSelected, hlSelected, hRawNe⟩ :=
    V517ActualFieldSeparation.actual_stage_families_have_floor_separated_selected_pair
      B N0 hN 2

  have hBpos : 0 < Bsmall := lt_of_lt_of_le (by norm_num) hBLower
  have hs0pos : (0 : ℝ) < (aSmall 0 : ℝ) := by
    rw [hs0]
    exact_mod_cast hBpos

  have htLate :
      (3 / 4 : ℝ) ≤
        1 - (2 / 5 : ℝ) / (aSmall 0 : ℝ) := by
    have htwo : (2 : ℝ) ≤ (aSmall 0 : ℝ) := by
      rw [hs0]
      exact_mod_cast hBLower
    have hdiv :
        (2 / 5 : ℝ) / (aSmall 0 : ℝ) ≤ 1 / 5 := by
      apply (div_le_iff₀ hs0pos).2
      nlinarith
    linarith

  have hsSelected' :
      MixedCandidateWitness.SelectedSchedule h
        (ActualCandidateConstruction.qbig B N0)
        (GermCandidateAssembly.potentialStages certificate modulation upper B
          (ActualCandidateAssembly.initialPotential B N0)
          (ActualCandidateAssembly.positivePotential B N0 hN))
        (LocalAngularDiagonal.rawSeries (ActualCandidateAssembly.directData B N0 hN))
        (MixedCandidateAssembly.pressureStages certificate modulation upper B
          (ActualCandidateAssembly.initialPressure B N0)
          (ActualCandidateAssembly.positivePressure B N0 hN))
        aSmall := by
    simpa only [
      ActualCandidateAssembly.potentialStages,
      ActualCandidateAssembly.directStages,
      ActualCandidateAssembly.pressureStages
    ] using hsSelected

  have hlSelected' :
      MixedCandidateWitness.SelectedSchedule h
        (ActualCandidateConstruction.qbig B N0)
        (GermCandidateAssembly.potentialStages certificate modulation upper B
          (ActualCandidateAssembly.initialPotential B N0)
          (ActualCandidateAssembly.positivePotential B N0 hN))
        (LocalAngularDiagonal.rawSeries (ActualCandidateAssembly.directData B N0 hN))
        (MixedCandidateAssembly.pressureStages certificate modulation upper B
          (ActualCandidateAssembly.initialPressure B N0)
          (ActualCandidateAssembly.positivePressure B N0 hN))
        aLarge := by
    simpa only [
      ActualCandidateAssembly.potentialStages,
      ActualCandidateAssembly.directStages,
      ActualCandidateAssembly.pressureStages
    ] using hlSelected

  obtain ⟨fSmall, hcSmall⟩ :=
    V517PrescribedGermCandidate.exists_force_of_selected_schedule
      certificate modulation upper B
      (ActualCandidateConstruction.qbig_pos B N0)
      (ActualCandidateAssembly.initialPotential B N0)
      (ActualCandidateAssembly.positivePotential B N0 hN)
      (ActualCandidateAssembly.directData B N0 hN)
      (ActualCandidateAssembly.initialPressure B N0)
      (ActualCandidateAssembly.positivePressure B N0 hN)
      (ActualCandidateAssembly.initialPotential_support B N0)
      (ActualCandidateAssembly.positivePotential_support B N0 hN)
      (ActualCandidateAssembly.directStages_support B N0 hN)
      (ActualCandidateAssembly.initialPressure_support B N0)
      (ActualCandidateAssembly.positivePressure_support B N0 hN)
      (ActualCandidateAssembly.endpoints B N0 hN).potential
      (ActualCandidateAssembly.endpoints B N0 hN).direct
      (ActualCandidateAssembly.endpoints B N0 hN).pressure
      (ActualCandidateAssembly.initialPotential_axisZeroOn B N0)
      (ActualCandidateAssembly.positivePotential_axisZeroOn B N0 hN)
      aSmall hsSelected'

  obtain ⟨fLarge, hcLarge⟩ :=
    V517PrescribedGermCandidate.exists_force_of_selected_schedule
      certificate modulation upper B
      (ActualCandidateConstruction.qbig_pos B N0)
      (ActualCandidateAssembly.initialPotential B N0)
      (ActualCandidateAssembly.positivePotential B N0 hN)
      (ActualCandidateAssembly.directData B N0 hN)
      (ActualCandidateAssembly.initialPressure B N0)
      (ActualCandidateAssembly.positivePressure B N0 hN)
      (ActualCandidateAssembly.initialPotential_support B N0)
      (ActualCandidateAssembly.positivePotential_support B N0 hN)
      (ActualCandidateAssembly.directStages_support B N0 hN)
      (ActualCandidateAssembly.initialPressure_support B N0)
      (ActualCandidateAssembly.positivePressure_support B N0 hN)
      (ActualCandidateAssembly.endpoints B N0 hN).potential
      (ActualCandidateAssembly.endpoints B N0 hN).direct
      (ActualCandidateAssembly.endpoints B N0 hN).pressure
      (ActualCandidateAssembly.initialPotential_axisZeroOn B N0)
      (ActualCandidateAssembly.positivePotential_axisZeroOn B N0 hN)
      aLarge hlSelected'

  let ASmall := SolenoidalDiagonal.potentialSum
    (fun j => (aSmall j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.potentialStages B N0 hN)
  let DSmall := SolenoidalDiagonal.potentialSum
    (fun j => (aSmall j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.directStages B N0 hN)
  let PSmall := SolenoidalDiagonal.potentialSum
    (fun j => (aSmall j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.pressureStages B N0 hN)
  let ALarge := SolenoidalDiagonal.potentialSum
    (fun j => (aLarge j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.potentialStages B N0 hN)
  let DLarge := SolenoidalDiagonal.potentialSum
    (fun j => (aLarge j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.directStages B N0 hN)
  let PLarge := SolenoidalDiagonal.potentialSum
    (fun j => (aLarge j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.pressureStages B N0 hN)
  let uSmall := TimeLocalization.activatedVelocity
    (MixedPeriodicAssembly.periodicVelocity ASmall DSmall)
  let pSmall := TimeLocalization.activatedPressure
    (SpatialLocalization.periodicPressure PSmall)
  let uLarge := TimeLocalization.activatedVelocity
    (MixedPeriodicAssembly.periodicVelocity ALarge DLarge)
  let pLarge := TimeLocalization.activatedPressure
    (SpatialLocalization.periodicPressure PLarge)
  let tStar : ℝ := 1 - (2 / 5 : ℝ) / (aSmall 0 : ℝ)

  have hCandidateNe : uSmall (tStar, 0) ≠ uLarge (tStar, 0) := by
    intro he
    apply hRawNe
    have hsEq :
        uSmall (tStar, 0) =
          MixedPeriodicAssembly.velocity ASmall DSmall (tStar, 0) := by
      dsimp only [uSmall]
      exact TimeLocalization.activatedVelocity_eq_late
        (MixedPeriodicAssembly.periodicVelocity ASmall DSmall) htLate 0
    have hlEq :
        uLarge (tStar, 0) =
          MixedPeriodicAssembly.velocity ALarge DLarge (tStar, 0) := by
      dsimp only [uLarge]
      exact TimeLocalization.activatedVelocity_eq_late
        (MixedPeriodicAssembly.periodicVelocity ALarge DLarge) htLate 0
    rw [hsEq, hlEq,
      MixedPeriodicAssembly.periodicVelocity_origin,
      MixedPeriodicAssembly.periodicVelocity_origin] at he
    simpa only [ASmall, DSmall, ALarge, DLarge, tStar] using he

  refine ⟨Bsmall, Blarge, aSmall, aLarge,
    hBLower, hBLarge, hs0, hl0, hRatio, ?_⟩
  dsimp only
  exact ⟨fSmall, fLarge, hcSmall, hcLarge, hCandidateNe⟩

end NavierStokes.V517ActualCandidatePair
