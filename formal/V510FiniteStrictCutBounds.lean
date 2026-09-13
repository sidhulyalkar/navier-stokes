import NavierStokes.CutStageEstimates
import NavierStokes.V510MinimalStrictSchedule

/-!
# v5.10: finite heterogeneous cut bounds with minimal strict growth

This is the first analytic consumer of the v5.10 schedule.  It mirrors the
pinned source theorem `CutStageEstimates.exists_finite_diagonal_cut_bounds`,
including the same coordinate bounds, raw field bounds, finite-family
aggregation, logarithmic absorption, and `cut_product_bound_of_threshold`.

The only change is the numerical selector: instead of
`DiagonalScale.exists_diagonal_scales` and its factor-two envelope, we use
`V510MinimalStrictSchedule.minimalStrictSchedule`.

The theorem therefore returns positivity, strict monotonicity, divergence to
infinity, and the same `CutStageBounds`, but intentionally does not assert
`2 * a j ≤ a (j+1)`.
-/

noncomputable section

namespace NavierStokes.V510FiniteStrictCutBounds

open Set Function Filter
open V510MinimalStrictSchedule V590CanonicalDiagonalScale
open scoped Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Exact finite-family source theorem with factor-two growth removed. -/
theorem exists_finite_strict_cut_bounds
    {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    (Bq : ℕ → ℝ)
    (hBq : ∀ k x, x ∈ S → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k q x‖ ≤ Bq k * q x ^ (1 - (k : ℝ)))
    {A : ∀ i, ℕ → E → W i}
    (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) U)
    (g L : ℕ → ℝ) (C p : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, CutStageEstimates.RawStageBounds q (A i) g L (C i) (p i) S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ,
      lower ≤ a 0 ∧
      (∀ j, 0 < a j) ∧
      StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      ∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q (A i)
        (fun j => g j / 2) (CutStageEstimates.cutLoss L) S := by
  classical
  choose K hK hb using fun i =>
    CutStageEstimates.exists_cut_stage_constants hU hSU hq hpos Bq hBq
      (hA i) g L (C i) (p i) (hraw i)
  let Kall : ℕ → ℕ → ℝ := fun j m => 1 + ∑ i, |K i j m|
  let Pall : ℕ → ℕ → ℝ := fun j m =>
    1 + ∑ i, |CutStageEstimates.cutLog (p i) j m|
  have hKall : ∀ j m, 0 < Kall j m := by
    intro j m
    have hs := Finset.sum_nonneg
      (fun i (_ : i ∈ Finset.univ) => abs_nonneg (K i j m))
    dsimp only [Kall]
    linarith
  have hKle : ∀ i j m, K i j m ≤ Kall j m := by
    intro i j m
    exact (le_abs_self _).trans
      ((Finset.single_le_sum
        (fun i (_ : i ∈ Finset.univ) => abs_nonneg (K i j m))
        (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
  have hPle : ∀ i j m, CutStageEstimates.cutLog (p i) j m ≤ Pall j m := by
    intro i j m
    exact (le_abs_self _).trans
      ((Finset.single_le_sum
        (fun i (_ : i ∈ Finset.univ) =>
          abs_nonneg (CutStageEstimates.cutLog (p i) j m))
        (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
  let a := minimalStrictSchedule Kall Pall g hg lower
  have ha := minimalStrictSchedule_spec Kall Pall g hg lower
  have hat : Tendsto (fun j => (a j : ℝ)) atTop atTop := by
    exact minimalStrictSchedule_tendsto_atTop Kall Pall g hg lower
  refine ⟨a, ha.1, ha.2.1, ha.2.2.1, hat, ?_⟩
  intro i j hj m hm x hx
  apply CutStageEstimates.cut_product_bound_of_threshold hU hSU hq hpos
    (hA i j hj) m
    (show (1 : ℝ) ≤ (a j : ℝ) by exact_mod_cast (Nat.succ_le_of_lt (ha.2.1 j)))
    (by positivity) (K := Kall j m) (P := Pall j m)
    (g := g j) (L := CutStageEstimates.cutLoss L m) ?_
    (ha.2.2.2.2 j hj m hm) x hx
  intro c hc y hy hq1
  apply (hb i j hj m c hc y hy hq1).trans
  have hlog : 1 ≤ 1 + |Real.log (q y)| :=
    le_add_of_nonneg_right (abs_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hpos y hy).le _)
  calc
    _ ≤ Kall j m * (1 + |Real.log (q y)|) ^
        (CutStageEstimates.cutLog (p i) j m) :=
      mul_le_mul_of_nonneg_right (hKle i j m)
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (hPle i j m)) (hKall j m).le

end NavierStokes.V510FiniteStrictCutBounds
