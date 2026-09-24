import NavierStokes.MixedCandidateWitness
import NavierStokes.V517FloorSeparatedMixedSchedule
import NavierStokes.V517ResidualFromSelectedBounds

/-!
# v5.17: two floor-separated selected schedules from one finite-stage dataset

This module combines the floor-separated mixed cut/smooth bounds with the
schedule-generic residual-flatness bridge.  Both schedules therefore satisfy
the pinned `MixedCandidateWitness.SelectedSchedule` contract for the same
literal potential/direct/pressure families.

The schedules differ only through their initial floors B and 3B.  No second
raw-stage construction or independent constant selection is introduced.
-/

noncomputable section

namespace NavierStokes.V517FloorSeparatedMixedResidual

open ProblemStatement Set Filter
open DiagonalResidual (JetRate)
open scoped Topology ContDiff

theorem exists_floor_separated_selected_schedules
    {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hSopen : IsOpen S)
    (hS : S ⊆ PhysicalWaveSum.preterminal)
    (hlS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ S)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j)
      (CutStageEstimates.physicalSublevel h qbig))
    (g LA LB LP Lbg Lres : ℕ → ℝ)
    (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
    (rawA : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) A g LA CA pA
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawB : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) B g LB CB pB
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawP : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) P g LP CP pP
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (hg0 : 0 ≤ g 0) (hg : ∀ j, 1 ≤ j → 0 < g j)
    (hgmono : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hbg : ∀ J m,
      JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
        (PhysicalWaveSum.physicalQ h)
        (MixedDiagonalResidual.uncutVelocity A B J) m (-Lbg m))
    (hres : ∀ J m,
      JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
        (PhysicalWaveSum.physicalQ h)
        (fun z => navierStokesResidual
          (MixedDiagonalResidual.uncutVelocity A B J)
          (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2)
        m (g J - Lres m))
    (lower : ℕ) :
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      lower ≤ Bsmall ∧
      1 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) < qbig ∧
      MixedCandidateWitness.SelectedSchedule h qbig A B P aSmall ∧
      MixedCandidateWitness.SelectedSchedule h qbig A B P aLarge := by
  obtain ⟨Bsmall, Blarge, aSmall, aLarge,
      hBLower, hBOne, hBLarge,
      hsPos, hlPos, hsMono, hlMono,
      hsTop, hlTop, hsGrowth, hlGrowth,
      hsRecip, hlRecip, hs0, hl0, hRatio, hqStar,
      hsCut, hsSmooth, hlCut, hlSmooth⟩ :=
    V517FloorSeparatedMixedSchedule.exists_three_component_floor_separated_schedule
      hh hh1 hqbig hS hA hB hP
      g LA LB LP CA CB CP pA pB pP
      rawA rawB rawP hg lower

  have hsZero :=
    V517ResidualFromSelectedBounds.physical_vanishingJointJets_of_threeCutBounds
      hh hh1 hqbig hSopen hS hlS
      hA hB hP g LA LB LP Lbg Lres
      hg0 hgmono hgtop hbg hres hsTop hsCut
  have hlZero :=
    V517ResidualFromSelectedBounds.physical_vanishingJointJets_of_threeCutBounds
      hh hh1 hqbig hSopen hS hlS
      hA hB hP g LA LB LP Lbg Lres
      hg0 hgmono hgtop hbg hres hlTop hlCut

  have hsOne : 1 ≤ aSmall 0 := by
    rw [hs0]
    exact hBOne
  have hlOne : 1 ≤ aLarge 0 := by
    rw [hl0, hBLarge]
    omega

  have hsSelected :
      MixedCandidateWitness.SelectedSchedule h qbig A B P aSmall :=
    ⟨hsOne, hsPos, hsGrowth, hsMono, hsTop, hsRecip, hsSmooth, hsZero⟩
  have hlSelected :
      MixedCandidateWitness.SelectedSchedule h qbig A B P aLarge :=
    ⟨hlOne, hlPos, hlGrowth, hlMono, hlTop, hlRecip, hlSmooth, hlZero⟩

  exact ⟨Bsmall, Blarge, aSmall, aLarge,
    hBLower, hBOne, hBLarge, hs0, hl0, hRatio, hqStar,
    hsSelected, hlSelected⟩

end NavierStokes.V517FloorSeparatedMixedResidual
