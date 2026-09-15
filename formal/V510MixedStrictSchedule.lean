import NavierStokes.MixedDiagonalSchedule
import NavierStokes.V510PhysicalLocalStrictCutBounds

/-!
# v5.10: mixed three-component schedule without factor-two growth

This mirrors `MixedDiagonalSchedule.exists_three_component_local_schedule` for
the same potential, direct-velocity, and pressure families, but selects the
common physical cutoff schedule through the v5.10 minimal strict envelope.

The raw field estimates, common derivative loss, finite-family aggregation,
local-q support condition, and smooth full sums are unchanged.  The returned
schedule is positive, strictly monotone, tends to infinity, and obeys the same
support gap, but intentionally carries no `2 * a j ≤ a (j+1)` field.

No final-candidate or force-norm claim is made here.
-/

noncomputable section

namespace NavierStokes.V510MixedStrictSchedule

open Set Function Filter ProblemStatement
open V510PhysicalLocalStrictCutBounds
open scoped Topology ContDiff BigOperators

private theorem family_raw_bounds {h : ℝ} {S : Set SpaceTime}
    (hpos : ∀ x ∈ S, 0 < PhysicalWaveSum.physicalQ h x)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    {g LA LB LP : ℕ → ℝ} {CA CB CP pA pB pP : ℕ → ℕ → ℝ}
    (hA : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g LA CA pA S)
    (hB : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B g LB CB pB S)
    (hP : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P g LP CP pP S) :
    ∀ c, CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) (MixedDiagonalSchedule.family A B P c) g
      (MixedDiagonalSchedule.commonRawLoss LA LB LP)
      (MixedDiagonalSchedule.scalarFamily
        (fun j m => |CA j m|) (fun j m => |CB j m|) (fun j m => |CP j m|) c)
      (MixedDiagonalSchedule.scalarFamily pA pB pP c) S := by
  intro c
  fin_cases c
  · exact MixedDiagonalSchedule.raw_bounds_mono_loss hpos
      (MixedDiagonalSchedule.potential_loss_le LA LB LP) hA
  · exact MixedDiagonalSchedule.raw_bounds_mono_loss hpos
      (MixedDiagonalSchedule.direct_loss_le LA LB LP) hB
  · exact MixedDiagonalSchedule.raw_bounds_mono_loss hpos
      (MixedDiagonalSchedule.pressure_loss_le LA LB LP) hP

/-- Exact mixed local schedule interface with factor-two growth removed. -/
theorem exists_three_component_local_strict_schedule {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig))
    (g LA LB LP : ℕ → ℝ) (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
    (rawA : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g LA CA pA
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawB : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B g LB CB pB
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawP : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P g LP CP pP
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ,
      lower ≤ a 0 ∧
      (∀ j, 0 < a j) ∧
      StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      MixedDiagonalSchedule.ThreeCutBounds a h A B P (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums a h A B P := by
  have hs : ∀ c j, 1 ≤ j →
      ContDiffOn ℝ ∞ (MixedDiagonalSchedule.family A B P c j)
        (CutStageEstimates.physicalSublevel h qbig) := by
    intro c j _
    fin_cases c
    · exact hA j
    · exact hB j
    · exact hP j
  obtain ⟨a, hal, hap, ham, hat, hrecip, hb⟩ :=
    exists_physical_local_strict_cut_bounds hh hh1 hqbig hS hs
      g (MixedDiagonalSchedule.commonRawLoss LA LB LP)
      (MixedDiagonalSchedule.scalarFamily
        (fun j m => |CA j m|) (fun j m => |CB j m|) (fun j m => |CP j m|))
      (MixedDiagonalSchedule.scalarFamily pA pB pP)
      (family_raw_bounds
        (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1)
        rawA rawB rawP) hg lower
  refine ⟨a, hal, hap, ham, hat, hrecip,
    ⟨MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.potential).1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.direct).1,
      MixedDiagonalSchedule.cut_bounds_of_positiveStages
        (hb MixedDiagonalSchedule.Component.pressure).1⟩, ?_⟩
  exact
    ⟨MixedDiagonalSchedule.full_sum_smooth_of_initial hh hh1 ham (hap 0) (hrecip 0)
        (hA 0) (hb MixedDiagonalSchedule.Component.potential).2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial hh hh1 ham (hap 0) (hrecip 0)
        (hB 0) (hb MixedDiagonalSchedule.Component.direct).2,
      MixedDiagonalSchedule.full_sum_smooth_of_initial hh hh1 ham (hap 0) (hrecip 0)
        (hP 0) (hb MixedDiagonalSchedule.Component.pressure).2⟩

end NavierStokes.V510MixedStrictSchedule
