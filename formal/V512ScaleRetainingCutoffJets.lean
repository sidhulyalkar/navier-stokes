import NavierStokes.CutStageEstimates
import NavierStokes.SmoothCutoffs

/-!
# v5.12: scale-retaining cutoff jets on the active collar

The pinned diagonal proof deliberately replaces powers of the cutoff scale by
powers of the inverse coordinate. That is ideal for scale-uniform existence
estimates, but it erases the quantity needed to compare two schedules.

This module keeps the scale explicit.

The exact scalar identity is already source-native:

  D^m[scaledCutoff a](q) = a^m * cutoff^(m)(a*q).

For a physical coordinate Q whose k-jets obey

  ||D^k Q|| <= B_k * Q^(1-k),

and on the active reciprocal collar

  1/(2a) <= Q <= 1/a,

the jets of the scaled coordinate a*Q are O(a^k). Feeding that bound into the
source composition theorem yields

  ||D^m[cutoff(a*Q)]|| <= C_m * a^m.

No force-norm ordering is claimed here. This is the schedule-sensitive cutoff
input needed before a paired collar residual comparison can be meaningful.
-/

noncomputable section

namespace NavierStokes.V512ScaleRetainingCutoffJets

open Set Function
open scoped Topology ContDiff BigOperators

/-- Exact scale-retaining scalar derivative bound. -/
theorem scaledCutoff_iteratedDeriv_scale_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a q : ℝ, 0 ≤ a →
      |iteratedDeriv m (SmoothCutoffs.scaledCutoff a) q| ≤ C * a ^ m := by
  obtain ⟨C, hC, hb⟩ := SmoothCutoffs.cutoff_iteratedDeriv_bounded m
  refine ⟨C, hC, ?_⟩
  intro a q ha
  rw [SmoothCutoffs.scaledCutoff_iteratedDeriv, abs_mul,
    abs_of_nonneg (pow_nonneg ha m)]
  calc
    a ^ m * |iteratedDeriv m SmoothCutoffs.cutoff (a * q)|
        ≤ a ^ m * C :=
      mul_le_mul_of_nonneg_left (hb (a * q)) (pow_nonneg ha m)
    _ = C * a ^ m := by ring

/-- A single constant controls all scalar cutoff jets up to order m while
retaining the top scale power a^m, for a >= 1. -/
theorem scaledCutoff_finite_jets_scale_bound (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a q : ℝ, 1 ≤ a → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (SmoothCutoffs.scaledCutoff a) q‖ ≤
        C * a ^ m := by
  choose C hC hb using scaledCutoff_iteratedDeriv_scale_bound
  let M := CutStageEstimates.finiteBound C m
  have hM : 1 ≤ M := CutStageEstimates.finiteBound_one_le C m
  refine ⟨M, hM, ?_⟩
  intro a q ha k hk
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hk0 := hb k a q ha0
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  calc
    |iteratedDeriv k (SmoothCutoffs.scaledCutoff a) q|
        ≤ C k * a ^ k := hk0
    _ ≤ M * a ^ k :=
      mul_le_mul_of_nonneg_right
        (CutStageEstimates.le_finiteBound C hk) (pow_nonneg ha0 k)
    _ ≤ M * a ^ m := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_right₀ ha hk
      · linarith

section CollarComposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a reciprocal collar, coordinate power loss converts into explicit
powers of the cutoff scale. -/
theorem scaledCoordinate_jet_bound_on_collar
    {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hpos : ∀ x ∈ S, 0 < q x)
    (B : ℕ → ℝ)
    (hB : ∀ k x, x ∈ S →
      ‖iteratedFDeriv ℝ k q x‖ ≤ B k * q x ^ (1 - (k : ℝ)))
    (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ a : ℝ, 1 ≤ a → ∀ x ∈ S,
      1 / (2 * a) ≤ q x → q x ≤ 1 / a →
      ∀ k, 1 ≤ k → k ≤ m →
        ‖iteratedFDeriv ℝ k (fun y => a * q y) x‖ ≤ (D * a) ^ k := by
  let FB := CutStageEstimates.finiteBound B m
  let D : ℝ := 2 * FB
  have hFB : 1 ≤ FB := CutStageEstimates.finiteBound_one_le B m
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro a ha x hx hlow hhigh k hk hkm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hqx : 0 < q x := hpos x hx
  have hrecip : 1 / q x ≤ 2 * a := by
    apply (div_le_iff₀ hqx).2
    have hp := (div_le_iff₀ (mul_pos (by norm_num) ha0)).1 hlow
    nlinarith
  have hpowq :
      q x ^ (1 - ((n + 1 : ℕ) : ℝ)) = (1 / q x) ^ n := by
    have hexp : 1 - ((n + 1 : ℕ) : ℝ) = -(n : ℝ) := by
      push_cast
      ring
    rw [hexp, Real.rpow_neg hqx.le, Real.rpow_natCast]
    simp only [one_div, inv_pow]
  have hpowrecip : (1 / q x) ^ n ≤ (2 * a) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hrecip n
  have hBk : B (n + 1) ≤ FB ^ (n + 1) := by
    exact (CutStageEstimates.le_finiteBound B hkm).trans
      (by simpa only [pow_one] using
        pow_le_pow_right₀ hFB (Nat.succ_pos n))
  have hqraw :
      B (n + 1) * q x ^ (1 - ((n + 1 : ℕ) : ℝ)) ≤
        FB ^ (n + 1) * (2 * a) ^ n := by
    rw [hpowq]
    exact mul_le_mul hBk hpowrecip (by positivity) (by positivity)
  have hscaled :
      ‖iteratedFDeriv ℝ (n + 1) (fun y => a * q y) x‖ ≤
        a * (B (n + 1) * q x ^ (1 - ((n + 1 : ℕ) : ℝ))) := by
    change ‖iteratedFDeriv ℝ (n + 1) (fun y => a • q y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply'
      ((hq.contDiffAt (hU.mem_nhds (hSU hx))).of_le
        (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))),
      norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
    exact mul_le_mul_of_nonneg_left (hB (n + 1) x hx) ha0.le
  apply hscaled.trans
  calc
    a * (B (n + 1) * q x ^ (1 - ((n + 1 : ℕ) : ℝ)))
        ≤ a * (FB ^ (n + 1) * (2 * a) ^ n) :=
      mul_le_mul_of_nonneg_left hqraw ha0.le
    _ = FB ^ (n + 1) * ((2 * a) ^ n * a) := by ring
    _ ≤ FB ^ (n + 1) * ((2 * a) ^ n * (2 * a)) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · linarith
        · positivity
      · positivity
    _ = (D * a) ^ (n + 1) := by
      dsimp only [D]
      rw [pow_succ]
      ring

/-- Scale-retaining composed cutoff jet bound on the active collar. -/
theorem composedCutoff_jet_scale_bound_on_collar
    {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hpos : ∀ x ∈ S, 0 < q x)
    (B : ℕ → ℝ)
    (hB : ∀ k x, x ∈ S →
      ‖iteratedFDeriv ℝ k q x‖ ≤ B k * q x ^ (1 - (k : ℝ)))
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 1 ≤ a → ∀ x ∈ S,
      1 / (2 * a) ≤ q x → q x ≤ 1 / a →
      ‖iteratedFDeriv ℝ m
        (fun y => SmoothCutoffs.cutoff (a * q y)) x‖ ≤ C * a ^ m := by
  obtain ⟨D, hD, hscaled⟩ :=
    scaledCoordinate_jet_bound_on_collar hU hSU hq hpos B hB m
  choose C hC hb using SmoothCutoffs.cutoff_iteratedDeriv_bounded
  let CF := CutStageEstimates.finiteBound C m
  let K : ℝ := m.factorial * CF * D ^ m
  have hCF : 1 ≤ CF := CutStageEstimates.finiteBound_one_le C m
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro a ha x hx hlow hhigh
  let F : E → ℝ := fun y => a * q y
  have hF : ContDiffOn ℝ ∞ F U := contDiffOn_const.mul hq
  have hCB : ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k SmoothCutoffs.cutoff (F x)‖ ≤ CF := by
    intro k hk
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact (hb k (F x)).trans (CutStageEstimates.le_finiteBound C hk)
  have hcomp := CutStageEstimates.composition_jet_bound
    hU hF SmoothCutoffs.cutoff_contDiff (hSU hx) m
    (C := CF) (D := D * a)
    hCB (hscaled a ha x hx hlow hhigh)
  change ‖iteratedFDeriv ℝ m
      (fun y => SmoothCutoffs.cutoff (a * q y)) x‖ ≤ _ at hcomp
  apply hcomp.trans_eq
  dsimp only [K]
  rw [mul_pow]
  ring

end CollarComposition

end NavierStokes.V512ScaleRetainingCutoffJets
