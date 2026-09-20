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
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hqx : 0 < q x := hpos x hx
  have hq1 : q x ≤ 1 := hhigh.trans (by
    simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one ha)
  have hrecip : 1 / q x ≤ 2 * a := by
    apply (div_le_iff₀ hqx).2
    have hp := (div_le_iff₀ (mul_pos (by norm_num) ha0)).1 hlow
    nlinarith
  have hpowq :
      q x ^ (1 - (k : ℝ)) ≤ (1 / q x) ^ k := by
    calc
      q x ^ (1 - (k : ℝ)) ≤ q x ^ (-(k : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_ge hqx hq1
        linarith
      _ = (1 / q x) ^ k := by
        rw [Real.rpow_neg hqx.le, Real.rpow_natCast]
        simp only [one_div]
  have hpowrecip : (1 / q x) ^ k ≤ (2 * a) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hrecip k
  have hBk : B k ≤ FB ^ k := by
    exact (CutStageEstimates.le_finiteBound B hkm).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hFB hk)
  have hqraw :
      B k * q x ^ (1 - (k : ℝ)) ≤ FB ^ k * (2 * a) ^ k := by
    exact (mul_le_mul hBk (hpowq.trans hpowrecip)
      (Real.rpow_nonneg hqx.le _) (by positivity))
  have hscaled :
      ‖iteratedFDeriv ℝ k (fun y => a * q y) x‖ ≤
        a * (B k * q x ^ (1 - (k : ℝ))) := by
    have hs := iteratedFDeriv_const_mul_apply
      (hq.contDiffAt (hU.mem_nhds (hSU hx))).of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
      a q x
    rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
    exact mul_le_mul_of_nonneg_left (hB k x hx) ha0.le
  apply hscaled.trans
  calc
    a * (B k * q x ^ (1 - (k : ℝ)))
        ≤ a * (FB ^ k * (2 * a) ^ k) :=
      mul_le_mul_of_nonneg_left hqraw ha0.le
    _ ≤ (D * a) ^ k := by
      dsimp only [D]
      rw [mul_pow, mul_pow]
      have ha_le_pow : a ≤ a ^ k := by
        simpa only [pow_one] using pow_le_pow_right₀ ha hk
      calc
        a * (FB ^ k * (2 ^ k * a ^ k))
            = FB ^ k * 2 ^ k * (a * a ^ k) := by ring
        _ ≤ FB ^ k * 2 ^ k * (a ^ k * a ^ k) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right ha_le_pow (pow_nonneg ha0.le k)
          · positivity
        _ = (2 * FB) ^ k * a ^ k * a ^ k := by ring
        _ ≥ (2 * FB) ^ k * a ^ k := by
          have hak : 1 ≤ a ^ k := one_le_pow₀ ha
          nlinarith [show 0 ≤ (2 * FB) ^ k * a ^ k by positivity]

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
  obtain ⟨C0, hC0, hcut⟩ :=
    SmoothCutoffs.cutoff_iteratedDeriv_bounded m
  let C : ℝ := m.factorial * CutStageEstimates.finiteBound
    (fun k => Classical.choose (SmoothCutoffs.cutoff_iteratedDeriv_bounded k)) m * D ^ m
  have hCF : 1 ≤ CutStageEstimates.finiteBound
      (fun k => Classical.choose (SmoothCutoffs.cutoff_iteratedDeriv_bounded k)) m :=
    CutStageEstimates.finiteBound_one_le _ _
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a ha x hx hlow hhigh
  let F : E → ℝ := fun y => a * q y
  have hF : ContDiffOn ℝ ∞ F U := contDiffOn_const.mul hq
  let CB : ℕ → ℝ := fun k =>
    Classical.choose (SmoothCutoffs.cutoff_iteratedDeriv_bounded k)
  have hCB : ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k SmoothCutoffs.cutoff (F x)‖ ≤
        CutStageEstimates.finiteBound CB m := by
    intro k hk
    have hs := Classical.choose_spec
      (SmoothCutoffs.cutoff_iteratedDeriv_bounded k)
    have hkbound := hs.2 (F x)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hkbound.trans (CutStageEstimates.le_finiteBound CB hk)
  have hcomp := CutStageEstimates.composition_jet_bound
    hU hF SmoothCutoffs.cutoff_contDiff (hSU hx) m
    (C := CutStageEstimates.finiteBound CB m) (D := D * a)
    hCB (hscaled a ha x hx hlow hhigh)
  change ‖iteratedFDeriv ℝ m (SmoothCutoffs.cutoff ∘ F) x‖ ≤ _ at hcomp
  have heq : SmoothCutoffs.cutoff ∘ F =
      fun y => SmoothCutoffs.cutoff (a * q y) := rfl
  rw [heq] at hcomp
  apply hcomp.trans_eq
  dsimp only [C]
  rw [mul_pow]
  ring

end CollarComposition

end NavierStokes.V512ScaleRetainingCutoffJets
