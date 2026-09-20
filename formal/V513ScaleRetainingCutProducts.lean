import NavierStokes.V512ScaleRetainingCutoffJets

/-!
# v5.13: scale-retaining cut-product jets on the active collar

v5.12 keeps the cutoff scale visible in derivatives of the composed scalar
cutoff.  The residual, however, sees differentiated products

  cutoff (a * q) • A.

This module passes the explicit scale through the exact Leibniz estimate used
by the pinned source.  For an m-jet of the cut product, the i-th Leibniz term
retains the factor a^i multiplying the complementary (m-i)-jet of the raw
stage.

No raw-stage lower bound, residual ordering, or force-norm ordering is asserted
here.  This is the product-level bridge needed before inserting the literal
stage estimates or comparing paired schedules.
-/

noncomputable section

namespace NavierStokes.V513ScaleRetainingCutProducts

open Set Function
open scoped Topology ContDiff BigOperators

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On the active reciprocal collar, every Leibniz contribution to a cut-stage
jet retains the corresponding explicit power of the cutoff scale. -/
theorem cutProduct_jet_scale_sum_on_collar
    {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hpos : ∀ x ∈ S, 0 < q x)
    (B : ℕ → ℝ)
    (hB : ∀ k x, x ∈ S →
      ‖iteratedFDeriv ℝ k q x‖ ≤ B k * q x ^ (1 - (k : ℝ)))
    {A : E → V} (hA : ContDiffOn ℝ ∞ A U)
    (m : ℕ) :
    ∃ C : ℕ → ℝ,
      (∀ i, 0 ≤ C i) ∧
      ∀ a : ℝ, 1 ≤ a → ∀ x ∈ S,
        1 / (2 * a) ≤ q x → q x ≤ 1 / a →
        ‖iteratedFDeriv ℝ m
          (fun y => SmoothCutoffs.cutoff (a * q y) • A y) x‖ ≤
          ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * (C i * a ^ i) *
              ‖iteratedFDeriv ℝ (m - i) A x‖ := by
  choose C hC hcut using fun i =>
    V512ScaleRetainingCutoffJets.composedCutoff_jet_scale_bound_on_collar
      hU hSU hq hpos B hB i
  refine ⟨C, hC, ?_⟩
  intro a ha x hx hlow hhigh
  have hχ : ContDiffOn ℝ ∞ (fun y => SmoothCutoffs.cutoff (a * q y)) U :=
    SmoothCutoffs.cutoff_contDiff.comp_contDiffOn (contDiffOn_const.mul hq)
  have hprod := CutStageEstimates.smul_jet_bound hU hχ hA (hSU hx) m
  apply hprod.trans
  apply Finset.sum_le_sum
  intro i hi
  have him : i ≤ m := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hci := hcut i a ha x hx hlow hhigh
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hci (by positivity))
    (norm_nonneg _)

end NavierStokes.V513ScaleRetainingCutProducts
