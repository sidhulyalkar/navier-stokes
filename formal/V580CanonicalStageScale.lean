import NavierStokes.DiagonalScale

/-!
# v5.8 canonical least admissible stage scale

The pinned source proves existence of sufficiently large integer cutoff scales,
but does not choose a canonical witness.  This file introduces the least
integer scale satisfying the exact finite family of logarithmic smallness tests
at one correction stage.

The key comparison is antitonicity in the gain: if `g'` is pointwise stronger
than `g`, then the least admissible scale for `g'` is no larger than the least
admissible scale for `g`.

This gives a quantitative comparison object for v5.8.  It does not prove that
the inequality is strict at any actual stage, and it does not alter the source
construction.
-/

noncomputable section

namespace NavierStokes.V580CanonicalStageScale

open NavierStokes.DiagonalScale

/-- Exact per-stage numerical predicate used by the source diagonal schedule.
Stage zero is exempt from logarithmic smallness, matching
`DiagonalScale.exists_diagonal_scales`; it retains only positivity of the
integer scale. -/
def StageAdmissible (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ) (j a : ℕ) : Prop :=
  1 ≤ a ∧
    (j = 0 ∨
      ∀ m, m ≤ j + 2 → ∀ q : ℝ,
        0 < q → q ≤ 1 / (a : ℝ) →
          |logPowerWeight (C j m) (p j m) (g j / 2) q| ≤ (1 / 2 : ℝ) ^ j)

/-- Every stage has at least one admissible integer scale whenever the positive
stages have positive gain. -/
theorem exists_stageAdmissible
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (j : ℕ) :
    ∃ a : ℕ, StageAdmissible C p g j a := by
  by_cases hj : j = 0
  · refine ⟨1, le_rfl, Or.inl hj⟩
  · have hjpos : 1 ≤ j := by omega
    obtain ⟨a, ha, hbound⟩ := exists_integer_scale (Finset.range (j + 3))
      (C j) (p j) (g j / 2) ((1 / 2 : ℝ) ^ j)
      (by linarith [hg j hjpos]) (by positivity)
    refine ⟨a, ?_, Or.inr ?_⟩
    · omega
    · intro m hm q hq hqa
      exact hbound m (Finset.mem_range.mpr (by omega)) q hq hqa

/-- The least positive integer satisfying all numerical cutoff tests at stage
`j`.  Proof arguments only certify existence; proof irrelevance ensures the
selected natural number is canonical for the underlying predicate. -/
noncomputable def leastStageScale
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (j : ℕ) : ℕ :=
  Nat.find (exists_stageAdmissible C p g hg j)

/-- The canonical least scale really is admissible. -/
theorem leastStageScale_spec
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (j : ℕ) :
    StageAdmissible C p g j (leastStageScale C p g hg j) := by
  unfold leastStageScale
  exact Nat.find_spec (exists_stageAdmissible C p g hg j)

/-- Raising the gain preserves admissibility of any fixed integer scale. -/
theorem StageAdmissible.mono_gain
    {C p : ℕ → ℕ → ℝ} {g g' : ℕ → ℝ} {j a : ℕ}
    (hgain : ∀ k, 1 ≤ k → g k ≤ g' k)
    (h : StageAdmissible C p g j a) :
    StageAdmissible C p g' j a := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hj | hold
  · exact Or.inl hj
  · refine Or.inr ?_
    intro m hm q hq hqa
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h.1
    have haPos : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le zero_lt_one haR
    have hrecip : (1 : ℝ) / (a : ℝ) ≤ 1 := by
      rw [one_div, inv_le_one₀ haPos]
      exact haR
    have hq1 : q ≤ 1 := hqa.trans hrecip
    have hjpos : 1 ≤ j := by
      by_contra hj0
      have : j = 0 := Nat.eq_zero_of_not_pos hj0
      subst j
      simp at hold
    have hhalf : g j / 2 ≤ g' j / 2 := by
      exact div_le_div_of_nonneg_right (hgain j hjpos) (by norm_num)
    have hmono :
        |logPowerWeight (C j m) (p j m) (g' j / 2) q| ≤
          |logPowerWeight (C j m) (p j m) (g j / 2) q| := by
      unfold logPowerWeight
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hq.le (g' j / 2)),
        abs_of_nonneg (Real.rpow_nonneg hq.le (g j / 2))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hq hq1 hhalf)
        (mul_nonneg (abs_nonneg (C j m))
          (abs_nonneg ((1 + |Real.log q|) ^ (p j m))))
    exact hmono.trans (hold m hm q hq hqa)

/-- Canonical stage scales are antitone in the gain.  A stronger gain can only
lower, or leave unchanged, the least integer cutoff needed at that stage. -/
theorem leastStageScale_antitone_gain
    {C p : ℕ → ℕ → ℝ} {g g' : ℕ → ℝ}
    (hg : ∀ j, 1 ≤ j → 0 < g j)
    (hg' : ∀ j, 1 ≤ j → 0 < g' j)
    (hgain : ∀ j, 1 ≤ j → g j ≤ g' j) (j : ℕ) :
    leastStageScale C p g' hg' j ≤ leastStageScale C p g hg j := by
  unfold leastStageScale
  apply Nat.find_min'
  exact StageAdmissible.mono_gain hgain
    (Nat.find_spec (exists_stageAdmissible C p g hg j))

/-- Pointwise comparison of the full canonical local-scale families. -/
theorem leastStageScale_family_antitone_gain
    {C p : ℕ → ℕ → ℝ} {g g' : ℕ → ℝ}
    (hg : ∀ j, 1 ≤ j → 0 < g j)
    (hg' : ∀ j, 1 ≤ j → 0 < g' j)
    (hgain : ∀ j, 1 ≤ j → g j ≤ g' j) :
    ∀ j,
      leastStageScale C p g' hg' j ≤ leastStageScale C p g hg j :=
  leastStageScale_antitone_gain hg hg' hgain

end NavierStokes.V580CanonicalStageScale
