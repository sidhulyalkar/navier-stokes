import NavierStokes.MixedDiagonalSchedule
import NavierStokes.V511PairedPhysicalLocalCutBounds

/-!
# v5.11: paired three-component mixed schedules

This lifts the paired strict-vs-doubling construction to the literal
potential/direct/pressure family used by the mixed diagonal assembly.

The raw fields, common derivative loss, finite-family aggregation, physical
support floor, and initial lower floor are shared.  The schedules fork only at
the recursive envelope and remain:

* equal at stage zero;
* strictly separated at stage one;
* pointwise ordered thereafter.

Both schedules satisfy `ThreeCutBounds` and `ThreeSmoothSums`.

No mixed-residual or force ordering is asserted here.
-/

noncomputable section

namespace NavierStokes.V511PairedMixedSchedule

open Set Function Filter ProblemStatement
open V511PairedPhysicalLocalCutBounds
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

/-- Paired mixed schedules for the same literal three-component field family. -/
theorem exists_three_component_local_paired_schedule {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j)
      (CutStageEstimates.physicalSublevel h qbig))
    (g LA LB LP : ℕ → ℝ) (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
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
    ∃ aStrict aDouble : ℕ → ℕ,
      lower ≤ aStrict 0 ∧
      lower ≤ aDouble 0 ∧
      (∀ j, 0 < aStrict j) ∧
      (∀ j, 0 < aDouble j) ∧
      StrictMono aStrict ∧
      StrictMono aDouble ∧
      Tendsto (fun j => (aStrict j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aDouble j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aDouble j ≤ aDouble (j + 1)) ∧
      (∀ j, 1 / (aStrict j : ℝ) < qbig) ∧
      (∀ j, 1 / (aDouble j : ℝ) < qbig) ∧
      aStrict 0 = aDouble 0 ∧
      aStrict 1 < aDouble 1 ∧
      (∀ j, aStrict j ≤ aDouble j) ∧
      MixedDiagonalSchedule.ThreeCutBounds aStrict h A B P
        (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums aStrict h A B P ∧
      MixedDiagonalSchedule.ThreeCutBounds aDouble h A B P
        (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums aDouble h A B P := by
  have hs : ∀ c j, 1 ≤ j →
      ContDiffOn ℝ ∞ (MixedDiagonalSchedule.family A B P c j)
        (CutStageEstimates.physicalSublevel h qbig) := by
    intro c j _
    fin_cases c
    · exact hA j
    · exact hB j
    · exact hP j

  obtain ⟨aStrict, aDouble,
      hsLower, hdLower,
      hsPos, hdPos,
      hsMono, hdMono,
      hsTop, hdTop,
      hdGrowth,
      hsRecip, hdRecip,
      hEq0, hLt1, hOrder,
      hb⟩ :=
    exists_paired_physical_local_cut_bounds hh hh1 hqbig hS hs
      g (MixedDiagonalSchedule.commonRawLoss LA LB LP)
      (MixedDiagonalSchedule.scalarFamily
        (fun j m => |CA j m|) (fun j m => |CB j m|)
        (fun j m => |CP j m|))
      (MixedDiagonalSchedule.scalarFamily pA pB pP)
      (family_raw_bounds
        (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1)
        rawA rawB rawP)
      hg lower

  have hsCut : MixedDiagonalSchedule.ThreeCutBounds aStrict h A B P
      (fun j => g j / 2)
      (MixedDiagonalSchedule.commonLoss LA LB LP) S :=
    ⟨MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.potential).1.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.direct).1.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.pressure).1.1⟩

  have hdCut : MixedDiagonalSchedule.ThreeCutBounds aDouble h A B P
      (fun j => g j / 2)
      (MixedDiagonalSchedule.commonLoss LA LB LP) S :=
    ⟨MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.potential).2.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.direct).2.1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.pressure).2.1⟩

  have hsSmooth : MixedDiagonalSchedule.ThreeSmoothSums aStrict h A B P :=
    ⟨MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hsMono (hsPos 0) (hsRecip 0)
        (hA 0) (hb MixedDiagonalSchedule.Component.potential).1.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hsMono (hsPos 0) (hsRecip 0)
        (hB 0) (hb MixedDiagonalSchedule.Component.direct).1.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hsMono (hsPos 0) (hsRecip 0)
        (hP 0) (hb MixedDiagonalSchedule.Component.pressure).1.2⟩

  have hdSmooth : MixedDiagonalSchedule.ThreeSmoothSums aDouble h A B P :=
    ⟨MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hdMono (hdPos 0) (hdRecip 0)
        (hA 0) (hb MixedDiagonalSchedule.Component.potential).2.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hdMono (hdPos 0) (hdRecip 0)
        (hB 0) (hb MixedDiagonalSchedule.Component.direct).2.2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial
        hh hh1 hdMono (hdPos 0) (hdRecip 0)
        (hP 0) (hb MixedDiagonalSchedule.Component.pressure).2.2⟩

  exact ⟨aStrict, aDouble,
    hsLower, hdLower, hsPos, hdPos, hsMono, hdMono,
    hsTop, hdTop, hdGrowth, hsRecip, hdRecip,
    hEq0, hLt1, hOrder,
    hsCut, hsSmooth, hdCut, hdSmooth⟩

end NavierStokes.V511PairedMixedSchedule
