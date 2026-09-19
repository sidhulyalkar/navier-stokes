import NavierStokes.SolenoidalDiagonal
import NavierStokes.SmoothCutoffs

/-!
# v5.11: paired cutoff-collar geometry

These source-locked geometric lemmas isolate what can change when the paired
construction replaces a larger cutoff scale by a smaller positive scale.

For the pinned cutoff `χ(a q)`, positive-order derivatives live in

  1/2 ≤ a q ≤ 1,

hence on the physical nonnegative q-axis in the reciprocal collar

  1/(2a) ≤ q ≤ 1/a.

If `b ≤ a`, the relaxed scale `b` moves both collar endpoints outward.  The
two cutoffs agree deep inside the tighter plateau and beyond the relaxed outer
support, so any actual cut-stage difference is confined to one explicit
comparison annulus.

The final theorem specializes this directly to Nat-valued strict/doubling
schedules.  It is support geometry only and proves no residual-norm ordering.
-/

noncomputable section

namespace NavierStokes.V511PairedCollarGeometry

open Set

theorem scaledCutoff_derivative_collar_nonneg
    (n : ℕ) {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q)
    (hs : iteratedDeriv (n + 1) (SmoothCutoffs.scaledCutoff a) q ≠ 0) :
    1 / (2 * a) ≤ q ∧ q ≤ 1 / a := by
  have hsupport :=
    SmoothCutoffs.scaledCutoff_iteratedDeriv_support a n hs
  change (1 / 2 : ℝ) ≤ |a * q| ∧ |a * q| ≤ 1 at hsupport
  have habs : |a * q| = a * q :=
    abs_of_nonneg (mul_nonneg ha.le hq)
  rw [habs] at hsupport
  have hl : (1 / 2 : ℝ) / a ≤ q := by
    apply (div_le_iff₀ ha).2
    simpa [mul_comm] using hsupport.1
  have heq : (1 / 2 : ℝ) / a = 1 / (2 * a) := by
    field_simp [ne_of_gt ha]
  rw [heq] at hl
  have hu : q ≤ 1 / a := by
    apply (le_div_iff₀ ha).2
    simpa [mul_comm] using hsupport.2
  exact ⟨hl, hu⟩

theorem collar_endpoints_monotone
    {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    1 / (2 * a) ≤ 1 / (2 * b) ∧ 1 / a ≤ 1 / b := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  constructor
  · exact one_div_le_one_div_of_le
      (mul_pos (by norm_num) hb)
      (mul_le_mul_of_nonneg_left hba (by norm_num))
  · exact one_div_le_one_div_of_le hb hba

theorem cutoffs_both_one_inside_old_plateau
    {a b q : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hq : 0 ≤ q) (hinner : q ≤ 1 / (2 * a)) :
    SmoothCutoffs.scaledCutoff a q = 1 ∧
      SmoothCutoffs.scaledCutoff b q = 1 := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have heq : (1 / (2 * a) : ℝ) = (1 / 2 : ℝ) / a := by
    field_simp [ne_of_gt ha]
  have hqa : q ≤ (1 / 2 : ℝ) / a := by
    simpa [heq] using hinner
  have haqa : q * a ≤ (1 / 2 : ℝ) := (le_div_iff₀ ha).1 hqa
  have haqp : a * q ≤ (1 / 2 : ℝ) := by
    simpa [mul_comm] using haqa
  have hbqp : b * q ≤ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_right hba hq).trans haqp
  have hAabs : |a * q| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonneg (mul_nonneg ha.le hq)]
    exact haqp
  have hBabs : |b * q| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonneg (mul_nonneg hb.le hq)]
    exact hbqp
  exact ⟨SmoothCutoffs.scaledCutoff_one_of_abs_le hAabs,
    SmoothCutoffs.scaledCutoff_one_of_abs_le hBabs⟩

theorem cutoffs_both_zero_outside_relaxed_support
    {a b q : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (houter : 1 / b ≤ q) :
    SmoothCutoffs.scaledCutoff a q = 0 ∧
      SmoothCutoffs.scaledCutoff b q = 0 := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hrecip : 1 / a ≤ 1 / b :=
    one_div_le_one_div_of_le hb hba
  exact
    ⟨SmoothCutoffs.scaledCutoff_zero_of_inv_le ha
        (hrecip.trans houter),
      SmoothCutoffs.scaledCutoff_zero_of_inv_le hb houter⟩

theorem cutoff_difference_localized
    {a b q : ℝ} (hb : 0 < b) (hba : b ≤ a) (hq : 0 ≤ q)
    (hne :
      SmoothCutoffs.scaledCutoff a q ≠
        SmoothCutoffs.scaledCutoff b q) :
    1 / (2 * a) < q ∧ q < 1 / b := by
  constructor
  · by_contra h
    have hle : q ≤ 1 / (2 * a) := le_of_not_gt h
    obtain ⟨ha1, hb1⟩ :=
      cutoffs_both_one_inside_old_plateau hb hba hq hle
    exact hne (ha1.trans hb1.symm)
  · by_contra h
    have hle : 1 / b ≤ q := le_of_not_gt h
    obtain ⟨ha0, hb0⟩ :=
      cutoffs_both_zero_outside_relaxed_support hb hba hle
    exact hne (ha0.trans hb0.symm)

theorem cutStage_difference_localized
    {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℕ → ℝ} {q : X → ℝ} {A : ℕ → X → V}
    {j : ℕ} {x : X}
    (hb : 0 < b j) (hba : b j ≤ a j) (hq : 0 ≤ q x)
    (hne :
      SolenoidalDiagonal.cutStage a q A j x ≠
        SolenoidalDiagonal.cutStage b q A j x) :
    1 / (2 * a j) < q x ∧ q x < 1 / (b j) := by
  have hcut :
      SmoothCutoffs.scaledCutoff (a j) (q x) ≠
        SmoothCutoffs.scaledCutoff (b j) (q x) := by
    intro heq
    apply hne
    simp only [SolenoidalDiagonal.cutStage]
    rw [heq]
  exact cutoff_difference_localized hb hba hq hcut

/-- Direct paired-schedule form.  If the strict and doubling cut stages differ
at a point and the strict scale is no larger, the difference lies between the
inner edge of the doubling collar and the outer edge of the strict support. -/
theorem natPairedCutStage_difference_localized
    {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {aStrict aDouble : ℕ → ℕ} {q : X → ℝ} {A : ℕ → X → V}
    {j : ℕ} {x : X}
    (hsPos : 0 < aStrict j)
    (horder : aStrict j ≤ aDouble j)
    (hq : 0 ≤ q x)
    (hne :
      SolenoidalDiagonal.cutStage (fun k => (aDouble k : ℝ)) q A j x ≠
        SolenoidalDiagonal.cutStage (fun k => (aStrict k : ℝ)) q A j x) :
    1 / (2 * (aDouble j : ℝ)) < q x ∧
      q x < 1 / (aStrict j : ℝ) := by
  apply cutStage_difference_localized
  · exact_mod_cast hsPos
  · exact_mod_cast horder
  · exact hq
  · exact hne

end NavierStokes.V511PairedCollarGeometry
