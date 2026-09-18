import NavierStokes.V510MinimalStrictSchedule

/-!
# v5.10: strict separation from the source doubling envelope

Removing factor-two growth as a proof obligation does not automatically imply
that the selected numerical schedule changes.  The local admissibility scales
may themselves already grow fast enough that the minimal strict and doubling
envelopes coincide.

This module isolates a sufficient condition for an actual strict change.  If
the previous source doubling scale is larger than one and the next local scale
does not itself reach the doubled previous scale, then the minimal +1 envelope
is strictly smaller at the next stage.

This is a numerical construction statement only.  It proves no force-norm
ordering.
-/

noncomputable section

namespace NavierStokes.V510StrictSeparation

open V590CanonicalDiagonalScale V510MinimalStrictSchedule

/-- Sufficient condition for strict separation of the two envelopes on the
same local-scale sequence. -/
theorem strictEnvelope_lt_doublingEnvelope_of_local_below_double
    (b : ℕ → ℕ) (n : ℕ)
    (hprev : 1 < DiagonalScale.doublingEnvelope b n)
    (hlocal :
      b (n + 1) < 2 * DiagonalScale.doublingEnvelope b n) :
    strictEnvelope b (n + 1) <
      DiagonalScale.doublingEnvelope b (n + 1) := by
  have henv :
      strictEnvelope b n ≤ DiagonalScale.doublingEnvelope b n :=
    strictEnvelope_le_doublingEnvelope b n
  have hstep :
      strictEnvelope b n + 1 <
        2 * DiagonalScale.doublingEnvelope b n := by
    omega
  change
    max (b (n + 1)) (strictEnvelope b n + 1) <
      max (b (n + 1)) (2 * DiagonalScale.doublingEnvelope b n)
  rw [max_eq_right (Nat.le_of_lt hlocal)]
  exact max_lt hlocal hstep

/-- Instantiation for the canonical least-admissible local scales used by the
v5.9/v5.10 comparison framework. -/
theorem minimalStrictSchedule_lt_canonicalSchedule_of_local_below_double
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B n : ℕ)
    (hprev : 1 < canonicalSchedule C p g hg B n)
    (hlocal :
      leastLocalScale C p g hg B (n + 1) <
        2 * canonicalSchedule C p g hg B n) :
    minimalStrictSchedule C p g hg B (n + 1) <
      canonicalSchedule C p g hg B (n + 1) := by
  exact strictEnvelope_lt_doublingEnvelope_of_local_below_double
    (leastLocalScale C p g hg B) n hprev hlocal

/-- Equivalent failure mode for this sufficient criterion: if the next local
least scale already reaches the source doubled floor, the max recursion may be
controlled by the same local requirement and the envelope deletion need not
change the selected integer at that stage. -/
theorem doublingEnvelope_eq_local_of_double_le_local
    (b : ℕ → ℕ) (n : ℕ)
    (hlocal :
      2 * DiagonalScale.doublingEnvelope b n ≤ b (n + 1)) :
    DiagonalScale.doublingEnvelope b (n + 1) = b (n + 1) := by
  change max (b (n + 1)) (2 * DiagonalScale.doublingEnvelope b n) =
    b (n + 1)
  exact max_eq_left hlocal

/-- At a positive stage the initial-floor parameter is logically irrelevant to
`StageAdmissible`; it appears only in the impossible `j = 0` branch. -/
theorem stageAdmissible_change_floor_of_pos
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    {B₁ B₂ j b : ℕ} (hj : 1 ≤ j)
    (h : StageAdmissible C p g B₁ j b) :
    StageAdmissible C p g B₂ j b := by
  rcases h with ⟨hb, _, hbound⟩
  refine ⟨hb, ?_, hbound⟩
  intro hj0
  omega

/-- For every fixed local admissibility problem there is an initial floor that
forces the minimal strict and canonical doubling schedules to differ already
at stage one.  No numerical value of the hidden source constants is required.

This is an existence statement for a deliberately chosen floor; it does not
claim that the default floor used by a particular source witness separates. -/
theorem exists_floor_strict_separation_at_one
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) :
    ∃ B : ℕ,
      minimalStrictSchedule C p g hg B 1 <
        canonicalSchedule C p g hg B 1 := by
  classical
  let r := leastLocalScale C p g hg 0 1
  let B := r + 2
  have hr0 : StageAdmissible C p g 0 1 r := by
    dsimp only [r]
    exact leastLocalScale_spec C p g hg 0 1
  have hrB : StageAdmissible C p g B 1 r :=
    stageAdmissible_change_floor_of_pos C p g (j := 1)
      (B₁ := 0) (B₂ := B) (by omega) hr0
  have hlocal_le :
      leastLocalScale C p g hg B 1 ≤ r := by
    unfold leastLocalScale
    apply Nat.find_min'
    exact hrB
  have hB0 : B ≤ canonicalSchedule C p g hg B 0 :=
    (canonicalSchedule_spec C p g hg B).1
  have hprev : 1 < canonicalSchedule C p g hg B 0 := by
    dsimp only [B] at hB0 ⊢
    omega
  have hlocal :
      leastLocalScale C p g hg B 1 <
        2 * canonicalSchedule C p g hg B 0 := by
    dsimp only [B] at hB0
    omega
  exact ⟨B,
    minimalStrictSchedule_lt_canonicalSchedule_of_local_below_double
      C p g hg B 0 hprev hlocal⟩

end NavierStokes.V510StrictSeparation
