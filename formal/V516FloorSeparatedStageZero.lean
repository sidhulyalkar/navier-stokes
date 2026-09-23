import NavierStokes.SolenoidalDiagonal
import NavierStokes.SmoothCutoffs

/-!
# v5.16: floor-separated stage-zero isolation

A second comparison lane avoids the stage-two nonvanishing bottleneck.

Take a factor-two schedule `aSmall` and inspect the explicit scale

  q★ = 1 / (2 * aSmall 0).

At this point the stage-zero cutoff of the small schedule is exactly one.
Because every later scale is at least `2 * aSmall 0`, all later cutoffs are
exactly zero. Hence the full infinite diagonal sum is literally the raw
stage-zero field.

For a second monotone schedule whose initial scale is already at least
`2 * aSmall 0`, every cutoff is zero at the same point, so its full sum
vanishes.

This is an exact pointwise identity, not a bound and not an asymptotic claim.
It gives a route to compare two admissible schedules using the initialized
field, where the pinned construction has substantially stronger explicit
structure than at a later correction cycle.
-/

noncomputable section

namespace NavierStokes.V516FloorSeparatedStageZero

open Set Filter
open scoped Topology BigOperators

/-- At the half-scale of a positive cutoff, that cutoff equals one, while any
cutoff whose scale is at least twice as large equals zero. -/
theorem scaledCutoffs_half_scale
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b) :
    SmoothCutoffs.scaledCutoff a (1 / (2 * a)) = 1 ∧
      SmoothCutoffs.scaledCutoff b (1 / (2 * a)) = 0 := by
  have h2a : 0 < 2 * a := mul_pos (by norm_num) ha
  have hb : 0 < b := h2a.trans_le hab
  have hprod : a * (1 / (2 * a)) = 1 / 2 := by
    field_simp [ne_of_gt ha]
  constructor
  · apply SmoothCutoffs.scaledCutoff_one_of_abs_le
    rw [hprod, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · apply SmoothCutoffs.scaledCutoff_zero_of_inv_le hb
    exact one_div_le_one_div_of_le h2a hab

/-- A factor-two monotone schedule isolates its raw stage zero at the explicit
half-scale point. No summability hypothesis is needed: every other summand is
proved to vanish exactly. -/
theorem potentialSum_eq_stageZero_at_half_scale
    {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : ℕ → ℝ} {q : X → ℝ} {A : ℕ → X → V} {x : X}
    (ha0 : 0 < a 0)
    (hgrowth0 : 2 * a 0 ≤ a 1)
    (hamono : Monotone a)
    (hq : q x = 1 / (2 * a 0)) :
    SolenoidalDiagonal.potentialSum a q A x = A 0 x := by
  have hcut0 :
      SmoothCutoffs.scaledCutoff (a 0) (1 / (2 * a 0)) = 1 :=
    (scaledCutoffs_half_scale ha0 hgrowth0).1
  have hsum :
      SolenoidalDiagonal.potentialSum a q A x =
        SolenoidalDiagonal.cutStage a q A 0 x := by
    apply tsum_eq_single 0
    intro j hj
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hratio : 2 * a 0 ≤ a j :=
      hgrowth0.trans (hamono hj1)
    have hzero :
        SmoothCutoffs.scaledCutoff (a j) (1 / (2 * a 0)) = 0 :=
      (scaledCutoffs_half_scale ha0 hratio).2
    simp only [SolenoidalDiagonal.cutStage, hq, hzero, zero_smul]
  rw [hsum]
  simp only [SolenoidalDiagonal.cutStage, hq, hcut0, one_smul]

/-- If a second monotone schedule starts at least twice as far out as the
reference scale, then its entire diagonal sum is zero at the reference
half-scale point. -/
theorem potentialSum_eq_zero_at_half_scale_of_floor
    {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a0 : ℝ} {b : ℕ → ℝ} {q : X → ℝ} {A : ℕ → X → V} {x : X}
    (ha0 : 0 < a0)
    (hfloor : 2 * a0 ≤ b 0)
    (hbmono : Monotone b)
    (hq : q x = 1 / (2 * a0)) :
    SolenoidalDiagonal.potentialSum b q A x = 0 := by
  unfold SolenoidalDiagonal.potentialSum
  apply tsum_zero
  intro j
  have hratio : 2 * a0 ≤ b j :=
    hfloor.trans (hbmono (Nat.zero_le j))
  have hzero :
      SmoothCutoffs.scaledCutoff (b j) (1 / (2 * a0)) = 0 :=
    (scaledCutoffs_half_scale ha0 hratio).2
  simp only [SolenoidalDiagonal.cutStage, hq, hzero, zero_smul]

/-- Exact two-schedule witness: the small factor-two schedule retains precisely
stage zero, while the larger-floor schedule retains nothing at the same point. -/
theorem floorSeparated_potentialSums
    {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {aSmall aLarge : ℕ → ℝ} {q : X → ℝ}
    {A : ℕ → X → V} {x : X}
    (hsmall0 : 0 < aSmall 0)
    (hsmallGrowth0 : 2 * aSmall 0 ≤ aSmall 1)
    (hsmallMono : Monotone aSmall)
    (hlargeFloor : 2 * aSmall 0 ≤ aLarge 0)
    (hlargeMono : Monotone aLarge)
    (hq : q x = 1 / (2 * aSmall 0)) :
    SolenoidalDiagonal.potentialSum aSmall q A x = A 0 x ∧
      SolenoidalDiagonal.potentialSum aLarge q A x = 0 := by
  exact ⟨
    potentialSum_eq_stageZero_at_half_scale
      hsmall0 hsmallGrowth0 hsmallMono hq,
    potentialSum_eq_zero_at_half_scale_of_floor
      hsmall0 hlargeFloor hlargeMono hq⟩

/-- If the raw stage-zero field is nonzero, the two full diagonal sums are
strictly different at the explicit floor-separated point. -/
theorem floorSeparated_potentialSums_ne
    {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {aSmall aLarge : ℕ → ℝ} {q : X → ℝ}
    {A : ℕ → X → V} {x : X}
    (hsmall0 : 0 < aSmall 0)
    (hsmallGrowth0 : 2 * aSmall 0 ≤ aSmall 1)
    (hsmallMono : Monotone aSmall)
    (hlargeFloor : 2 * aSmall 0 ≤ aLarge 0)
    (hlargeMono : Monotone aLarge)
    (hq : q x = 1 / (2 * aSmall 0))
    (hA0 : A 0 x ≠ 0) :
    SolenoidalDiagonal.potentialSum aSmall q A x ≠
      SolenoidalDiagonal.potentialSum aLarge q A x := by
  obtain ⟨hs, hl⟩ :=
    floorSeparated_potentialSums
      hsmall0 hsmallGrowth0 hsmallMono hlargeFloor hlargeMono hq
  rw [hs, hl]
  exact hA0

end NavierStokes.V516FloorSeparatedStageZero
