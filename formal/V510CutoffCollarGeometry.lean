import NavierStokes.SmoothCutoffs

/-!
# v5.10: cutoff-collar geometry under scale relaxation

These lemmas isolate the exact geometric effect of replacing a cutoff scale
`a` by a smaller positive scale `b ≤ a`.

For the pinned cutoff `χ(a q)`, positive derivatives live in the normalized
collar `1/2 ≤ a q ≤ 1`, hence on the physical positive q-axis in

  1/(2a) ≤ q ≤ 1/a.

A smaller scale moves both collar endpoints outward.  The cutoff fields agree
deep inside the old plateau and beyond the new outer support, so any actual
field difference is confined to an explicit annulus.

This is geometry only.  It proves no ordering of the Navier--Stokes residual
or force norm.
-/

noncomputable section

namespace NavierStokes.V510CutoffCollarGeometry

open Set

/-- On the physical half-line, any nonzero positive-order derivative of the
scaled cutoff lies in the exact reciprocal collar. -/
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

/-- If `0 < b ≤ a`, both reciprocal collar endpoints move outward when the
scale is relaxed from `a` to `b`. -/
theorem collar_endpoints_monotone
    {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    1 / (2 * a) ≤ 1 / (2 * b) ∧ 1 / a ≤ 1 / b := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  constructor
  · exact one_div_le_one_div_of_le
      (mul_pos (by norm_num) hb)
      (mul_le_mul_of_nonneg_left hba (by norm_num))
  · exact one_div_le_one_div_of_le hb hba

/-- Deep inside the old, tighter plateau, both the old and relaxed cutoffs are
identically one. -/
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

/-- Beyond the relaxed cutoff's outer support, both old and relaxed cutoffs are
zero. -/
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

/-- Any point where the old and relaxed cutoff fields differ lies in one
explicit comparison annulus.  This is the first support-level localization of
the v5.10 geometry change. -/
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

end NavierStokes.V510CutoffCollarGeometry
