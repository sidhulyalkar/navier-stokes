import NavierStokes.V510MinimalStrictSchedule

/-!
# v5.10: force a genuine strict-vs-doubling schedule separation

Removing the factor-two rule from the final candidate is now source-locked, but
that does not imply the two recursive selectors choose different integers for
the source theorem's default lower floor.

This module isolates a stronger existence statement that requires no numerical
values for the hidden cutoff constants.  Positive-stage local admissibility is
independent of the stage-zero floor.  Therefore we may choose a common floor
just above the least admissible stage-one scale.  For that same local-scale
family, the minimal +1 envelope and the source doubling envelope agree at stage
zero but are strictly separated at stage one.

This proves existence of a genuinely different admissible localization geometry.
It does not prove that the default lower=1 schedules differ, and it does not
compare either resulting force in any norm.
-/

noncomputable section

namespace NavierStokes.V510StrictScheduleSeparation

open V590CanonicalDiagonalScale V510MinimalStrictSchedule

/-- At a positive stage, the stage-zero floor is logically irrelevant to the
local admissibility predicate. -/
theorem stageAdmissible_floor_irrelevant_of_pos
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    {B B' j b : ℕ} (hj : 1 ≤ j) :
    StageAdmissible C p g B j b ↔
      StageAdmissible C p g B' j b := by
  constructor
  · rintro ⟨hb, _, hbound⟩
    refine ⟨hb, ?_, hbound⟩
    intro hj0
    omega
  · rintro ⟨hb, _, hbound⟩
    refine ⟨hb, ?_, hbound⟩
    intro hj0
    omega

/-- Consequently, the deterministic least positive-stage scale is independent
of the stage-zero floor. -/
theorem leastLocalScale_floor_independent_of_pos
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j)
    {B B' j : ℕ} (hj : 1 ≤ j) :
    leastLocalScale C p g hg B j =
      leastLocalScale C p g hg B' j := by
  apply Nat.le_antisymm
  · classical
    unfold leastLocalScale
    apply Nat.find_min'
    exact (stageAdmissible_floor_irrelevant_of_pos
      C p g (B := B) (B' := B') hj).2
      (Nat.find_spec (exists_stageAdmissible C p g hg B' j))
  · classical
    unfold leastLocalScale
    apply Nat.find_min'
    exact (stageAdmissible_floor_irrelevant_of_pos
      C p g (B := B) (B' := B') hj).1
      (Nat.find_spec (exists_stageAdmissible C p g hg B j))

/-- At stage zero the least admissible local scale is exactly max(1,B). -/
theorem leastLocalScale_zero_eq_max_one
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ) :
    leastLocalScale C p g hg B 0 = max 1 B := by
  apply Nat.le_antisymm
  · classical
    unfold leastLocalScale
    apply Nat.find_min'
    refine ⟨?_, ?_, ?_⟩
    · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    · intro _
      exact le_max_right _ _
    · intro hpos
      omega
  · have hs := leastLocalScale_spec C p g hg B 0
    apply max_le
    · exact hs.1
    · exact hs.2.1 rfl

/-- For every source-compatible local admissibility problem, there is a common
initial floor for which the minimal strict selector and the source doubling
selector are already strictly different at stage one. -/
theorem exists_floor_strict_schedule_separation
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) :
    ∃ B : ℕ,
      minimalStrictSchedule C p g hg B 0 =
        canonicalSchedule C p g hg B 0 ∧
      minimalStrictSchedule C p g hg B 1 <
        canonicalSchedule C p g hg B 1 := by
  let l := leastLocalScale C p g hg 0 1
  have hlpos : 0 < l := by
    exact (leastLocalScale_spec C p g hg 0 1).1
  let B := l + 1
  have hB1 : 1 ≤ B := by
    dsimp [B]
    omega
  have hBgt : 1 < B := by
    dsimp [B]
    omega
  have hzero : leastLocalScale C p g hg B 0 = B := by
    rw [leastLocalScale_zero_eq_max_one C p g hg B]
    exact max_eq_right hB1
  have hone : leastLocalScale C p g hg B 1 = l := by
    exact leastLocalScale_floor_independent_of_pos
      C p g hg (B := B) (B' := 0) (j := 1) (by omega)
  refine ⟨B, ?_, ?_⟩
  · unfold minimalStrictSchedule canonicalSchedule
    simp [strictEnvelope, DiagonalScale.doublingEnvelope, hzero, max_eq_right hB1]
  · unfold minimalStrictSchedule canonicalSchedule
    change
      max (leastLocalScale C p g hg B 1)
          (max 1 (leastLocalScale C p g hg B 0) + 1) <
        max (leastLocalScale C p g hg B 1)
          (2 * max 1 (leastLocalScale C p g hg B 0))
    rw [hzero, hone, max_eq_right hB1]
    have hl_left : l ≤ B + 1 := by
      dsimp [B]
      omega
    have hl_right : l ≤ 2 * B := by
      dsimp [B]
      omega
    rw [max_eq_right hl_left, max_eq_right hl_right]
    omega


/-- Any floor strictly above the positive-stage-one least local scale forces
stage-one separation between the two canonical recursive selectors. -/
theorem strict_schedule_separation_of_floor_gt_stage_one
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ)
    (hB : leastLocalScale C p g hg 0 1 < B) :
    minimalStrictSchedule C p g hg B 0 =
        canonicalSchedule C p g hg B 0 ∧
      minimalStrictSchedule C p g hg B 1 <
        canonicalSchedule C p g hg B 1 := by
  let l := leastLocalScale C p g hg 0 1
  have hlpos : 0 < l := by
    exact (leastLocalScale_spec C p g hg 0 1).1
  have hB1 : 1 ≤ B := by
    dsimp [l] at hB
    omega
  have hzero : leastLocalScale C p g hg B 0 = B := by
    rw [leastLocalScale_zero_eq_max_one C p g hg B]
    exact max_eq_right hB1
  have hone : leastLocalScale C p g hg B 1 = l := by
    exact leastLocalScale_floor_independent_of_pos
      C p g hg (B := B) (B' := 0) (j := 1) (by omega)
  constructor
  · unfold minimalStrictSchedule canonicalSchedule
    simp [strictEnvelope, DiagonalScale.doublingEnvelope, hzero, max_eq_right hB1]
  · unfold minimalStrictSchedule canonicalSchedule
    change
      max (leastLocalScale C p g hg B 1)
          (max 1 (leastLocalScale C p g hg B 0) + 1) <
        max (leastLocalScale C p g hg B 1)
          (2 * max 1 (leastLocalScale C p g hg B 0))
    rw [hzero, hone, max_eq_right hB1]
    have hlB : l < B := by
      simpa only [l] using hB
    have hl_left : l ≤ B + 1 := by omega
    have hl_right : l ≤ 2 * B := by omega
    rw [max_eq_right hl_left, max_eq_right hl_right]
    omega

/-- The support/localization layer may demand an arbitrary initial floor.
Whatever that requested floor is, one can raise it further and still force a
strict-vs-doubling separation at stage one without knowing any hidden cutoff
constant numerically. -/
theorem exists_floor_ge_strict_schedule_separation
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ B : ℕ,
      lower ≤ B ∧
      minimalStrictSchedule C p g hg B 0 =
        canonicalSchedule C p g hg B 0 ∧
      minimalStrictSchedule C p g hg B 1 <
        canonicalSchedule C p g hg B 1 := by
  let l := leastLocalScale C p g hg 0 1
  let B := max lower (l + 1)
  have hlB : l < B := by
    have hle : l + 1 ≤ B := le_max_right lower (l + 1)
    omega
  refine ⟨B, le_max_left lower (l + 1), ?_⟩
  exact strict_schedule_separation_of_floor_gt_stage_one
    C p g hg B (by simpa only [l] using hlB)

end NavierStokes.V510StrictScheduleSeparation
