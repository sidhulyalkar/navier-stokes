import NavierStokes.MixedDiagonalSchedule
import NavierStokes.V517FloorSeparatedPhysicalLocalCutBounds

/-!
# v5.17: floor-separated three-component mixed schedules

The same literal potential/direct/pressure families and the same raw analytic
data are assembled with two canonical schedules whose initial floors are B and
3B. Both satisfy the source-compatible cut bounds and smooth-sum conclusions.

This is the mixed-field counterpart of the v5.17 scalar schedule theorem.
-/

noncomputable section

namespace NavierStokes.V517FloorSeparatedMixedSchedule

open Set Function Filter ProblemStatement
open V517FloorSeparatedPhysicalLocalCutBounds
open scoped Topology ContDiff BigOperators

private theorem family_raw_bounds {h : ℝ} {S : Set SpaceTime}
    (hpos : ∀ x ∈ S, 0 < PhysicalWaveSum.physicalQ h x)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    {g LA LB LP : ℕ → ℝ} {CA CB CP pA pB pP : ℕ → ℕ → ℝ}
    (hA : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) A g LA CA pA S)
    (hB : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) B g LB CB pB S)
    (hP : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) P g LP CP pP S) :
    ∀ c, CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h)
      (MixedDiagonalSchedule.family A B P c) g
      (MixedDiagonalSchedule.commonRawLoss LA LB LP)
      (MixedDiagonalSchedule.scalarFamily
        (fun j m => |CA j m|) (fun j m => |CB j m|)
        (fun j m => |CP j m|) c)
      (MixedDiagonalSchedule.scalarFamily pA pB pP c) S := by
  intro c
  fin_cases c
  · exact MixedDiagonalSchedule.raw_bounds_mono_loss hpos
      (MixedDiagonalSchedule.potential_loss_le LA LB LP) hA
  · exact MixedDiagonalSchedule.raw_bounds_mono_loss hpos
      (MixedDiagonalSchedule.direct_loss_le LA LB LP) hB
  · exact MixedDiagonalSchedule.raw_bounds_mono_loss hpos
      (MixedDiagonalSchedule.pressure_loss_le LA LB LP) hP

theorem exists_three_component_floor_separated_schedule
    {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j)
      (CutStageEstimates.physicalSublevel h qbig))
    (g LA LB LP : ℕ → ℝ)
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
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      lower ≤ Bsmall ∧
      1 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      (∀ j, 0 < aSmall j) ∧
      (∀ j, 0 < aLarge j) ∧
      StrictMono aSmall ∧
      StrictMono aLarge ∧
      Tendsto (fun j => (aSmall j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aLarge j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aSmall j ≤ aSmall (j + 1)) ∧
      (∀ j, 2 * aLarge j ≤ aLarge (j + 1)) ∧
      (∀ j, 1 / (aSmall j : ℝ) < qbig) ∧
      (∀ j, 1 / (aLarge j : ℝ) < qbig) ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) < qbig ∧
      MixedDiagonalSchedule.ThreeCutBounds aSmall h A B P
        (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums aSmall h A B P ∧
      MixedDiagonalSchedule.ThreeCutBounds aLarge h A B P
        (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums aLarge h A B P := by
  have hs : ∀ c j, 1 ≤ j →
      ContDiffOn ℝ ∞ (MixedDiagonalSchedule.family A B P c j)
        (CutStageEstimates.physicalSublevel h qbig) := by
    intro c j _
    fin_cases c
    · exact hA j
    · exact hB j
    · exact hP j

  obtain ⟨Bsmall, Blarge, aSmall, aLarge,
      hBLower, hBOne, hBLarge,
      hsPos, hlPos, hsMono, hlMono,
      hsTop, hlTop, hsGrowth, hlGrowth,
      hsRecip, hlRecip, hs0, hl0, hRatio, hqStar, hb⟩ :=
    exists_floor_separated_physical_local_cut_bounds
      hh hh1 hqbig hS hs
      g (MixedDiagonalSchedule.commonRawLoss LA LB LP)
      (MixedDiagonalSchedule.scalarFamily
        (fun j m => |CA j m|) (fun j m => |CB j m|)
        (fun j m => |CP j m|))
      (MixedDiagonalSchedule.scalarFamily pA pB pP)
      (family_raw_bounds
        (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1)
        rawA rawB rawP)
      hg lower

  have hsCut : MixedDiagonalSchedule.ThreeCutBounds aSmall h A B P
      (fun j => g j / 2)
      (MixedDiagonalSchedule.commonLoss LA LB LP) S :=
    ⟨MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.potential).1.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.direct).1.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.pressure).1.1⟩

  have hlCut : MixedDiagonalSchedule.ThreeCutBounds aLarge h A B P
      (fun j => g j / 2)
      (MixedDiagonalSchedule.commonLoss LA LB LP) S :=
    ⟨MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.potential).2.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.direct).2.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.pressure).2.1⟩

  have hsSmooth : MixedDiagonalSchedule.ThreeSmoothSums aSmall h A B P :=
    ⟨MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hsMono (hsPos 0) (hsRecip 0)
        (hA 0) (hb MixedDiagonalSchedule.Component.potential).1.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hsMono (hsPos 0) (hsRecip 0)
        (hB 0) (hb MixedDiagonalSchedule.Component.direct).1.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hsMono (hsPos 0) (hsRecip 0)
        (hP 0) (hb MixedDiagonalSchedule.Component.pressure).1.2⟩

  have hlSmooth : MixedDiagonalSchedule.ThreeSmoothSums aLarge h A B P :=
    ⟨MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hlMono (hlPos 0) (hlRecip 0)
        (hA 0) (hb MixedDiagonalSchedule.Component.potential).2.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hlMono (hlPos 0) (hlRecip 0)
        (hB 0) (hb MixedDiagonalSchedule.Component.direct).2.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hlMono (hlPos 0) (hlRecip 0)
        (hP 0) (hb MixedDiagonalSchedule.Component.pressure).2.2⟩

  exact ⟨Bsmall, Blarge, aSmall, aLarge,
    hBLower, hBOne, hBLarge,
    hsPos, hlPos, hsMono, hlMono, hsTop, hlTop,
    hsGrowth, hlGrowth, hsRecip, hlRecip,
    hs0, hl0, hRatio, hqStar,
    hsCut, hsSmooth, hlCut, hlSmooth⟩

end NavierStokes.V517FloorSeparatedMixedSchedule
