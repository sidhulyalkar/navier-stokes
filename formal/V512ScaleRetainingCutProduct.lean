import NavierStokes.CutStageEstimates
import NavierStokes.V512ScaleRetainingCutoffJets

/-!
# v5.12: scale-retaining cut-stage product jets

The pinned source's scale-uniform cut-stage estimates intentionally erase the
cutoff parameter. For paired schedule comparison we instead keep the explicit
scale dependence all the way through the Leibniz product

  cutoff(a * q) • A.

On the active reciprocal collar, if the coordinate has the source-style jet
bounds and the raw stage has bounded jets up to order m, then every m-jet of
the cut product is bounded by

  K_m * a^m.

This is a schedule-sensitive field estimate. It is not yet a residual or force
ordering theorem.
-/

noncomputable section

namespace NavierStokes.V512ScaleRetainingCutProduct

open Set Function
open scoped Topology ContDiff BigOperators

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem sum_choose_real (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
  exact_mod_cast Nat.sum_range_choose m

/-- Scale-retaining Leibniz bound for one raw stage on an active collar. -/
theorem cut_product_jet_scale_bound_on_collar
    {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hpos : ∀ x ∈ S, 0 < q x)
    (B : ℕ → ℝ)
    (hB : ∀ k x, x ∈ S →
      ‖iteratedFDeriv ℝ k q x‖ ≤ B k * q x ^ (1 - (k : ℝ)))
    {A : E → V} (hA : ContDiffOn ℝ ∞ A U)
    (R : ℕ → ℝ)
    (hR : ∀ k x, x ∈ S →
      ‖iteratedFDeriv ℝ k A x‖ ≤ R k)
    (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, 1 ≤ a → ∀ x ∈ S,
      1 / (2 * a) ≤ q x → q x ≤ 1 / a →
      ‖iteratedFDeriv ℝ m
        (fun y => SmoothCutoffs.scaledCutoff a (q y) • A y) x‖ ≤
          K * a ^ m := by
  choose C hC hcut using fun k =>
    V512ScaleRetainingCutoffJets.composedCutoff_jet_scale_bound_on_collar
      hU hSU hq hpos B hB k
  let CF := CutStageEstimates.finiteBound C m
  let RF := CutStageEstimates.finiteBound R m
  have hCF : 1 ≤ CF := CutStageEstimates.finiteBound_one_le C m
  have hRF : 1 ≤ RF := CutStageEstimates.finiteBound_one_le R m
  let K : ℝ := 2 ^ m * CF * RF
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro a ha x hx hlow hhigh
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hcut' : ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i
        (fun y => SmoothCutoffs.scaledCutoff a (q y)) x‖ ≤
          CF * a ^ m := by
    intro i him
    have hi := hcut i a ha x hx hlow hhigh
    simp only [SmoothCutoffs.scaledCutoff] at hi
    calc
      ‖iteratedFDeriv ℝ i
          (fun y => SmoothCutoffs.scaledCutoff a (q y)) x‖
          ≤ C i * a ^ i := hi
      _ ≤ CF * a ^ i :=
        mul_le_mul_of_nonneg_right
          (CutStageEstimates.le_finiteBound C him)
          (pow_nonneg ha0 i)
      _ ≤ CF * a ^ m :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ ha him)
          (zero_le_one.trans hCF)
  have hraw' : ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k A x‖ ≤ RF := by
    intro k hkm
    exact (hR k x hx).trans (CutStageEstimates.le_finiteBound R hkm)
  have hb := CutStageEstimates.smul_jet_bound hU
    ((SmoothCutoffs.scaledCutoff_contDiff a).comp_contDiffOn hq)
    hA (hSU hx) m
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * (CF * a ^ m) * RF := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hmi : m - i ≤ m := Nat.sub_le _ _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hcut' i him) (hraw' (m - i) hmi)
          (norm_nonneg _) (by positivity))
        (by positivity)
    _ = K * a ^ m := by
      rw [Finset.sum_mul, Finset.sum_mul, sum_choose_real]
      dsimp only [K]
      ring

end NavierStokes.V512ScaleRetainingCutProduct
