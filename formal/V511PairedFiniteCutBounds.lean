import NavierStokes.CutStageEstimates
import NavierStokes.V510StrictScheduleSeparation

/-!
# Paired finite cutoff schedules from identical analytic data

A force comparison is only meaningful if the strict and doubling candidates use
the same finite-stage fields and the same cutoff constants.  Calling the
source's existential schedule theorem twice would not provide that control.

This module therefore reproduces the finite heterogeneous cutoff construction
only up to the common aggregated constants `Kall/Pall`, chooses one common
initial floor, and then forks *only* the recursive schedule rule:

* `minimalStrictSchedule`;
* `canonicalSchedule` (the source doubling envelope).

Both schedules satisfy the same source-compatible cut-stage estimates.  The
chosen common floor can dominate any requested lower floor and is selected so
that the schedules agree at stage zero and are strictly separated at stage one.

This is a paired construction theorem.  It proves no ordering of the resulting
Navier--Stokes residual or force.
-/

noncomputable section

namespace NavierStokes.V511PairedFiniteCutBounds

open Set Function Filter
open V590CanonicalDiagonalScale
open V510MinimalStrictSchedule
open V510StrictScheduleSeparation
open scoped Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- One common aggregation of the source cutoff constants supports both the
minimal strict and doubling schedules.  The schedules therefore differ only in
their recursive envelope, not in their raw fields or analytic constants. -/
theorem exists_paired_finite_cut_bounds
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
    ∃ aStrict aDouble : ℕ → ℕ,
      lower ≤ aStrict 0 ∧
      lower ≤ aDouble 0 ∧
      (∀ j, 0 < aStrict j) ∧
      (∀ j, 0 < aDouble j) ∧
      StrictMono aStrict ∧
      StrictMono aDouble ∧
      Tendsto (fun j => (aStrict j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aDouble j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aDouble j ≤ aDouble (j + 1)) ∧
      aStrict 0 = aDouble 0 ∧
      aStrict 1 < aDouble 1 ∧
      (∀ j, aStrict j ≤ aDouble j) ∧
      (∀ i, DiagonalJetBounds.CutStageBounds (fun j => (aStrict j : ℝ))
        q (A i) (fun j => g j / 2) (CutStageEstimates.cutLoss L) S) ∧
      (∀ i, DiagonalJetBounds.CutStageBounds (fun j => (aDouble j : ℝ))
        q (A i) (fun j => g j / 2) (CutStageEstimates.cutLoss L) S) := by
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

  obtain ⟨B, hBlower, hsep0, hsep1⟩ :=
    exists_floor_ge_strict_schedule_separation Kall Pall g hg lower
  let aStrict := minimalStrictSchedule Kall Pall g hg B
  let aDouble := canonicalSchedule Kall Pall g hg B
  have hs := minimalStrictSchedule_spec Kall Pall g hg B
  have hd := canonicalSchedule_spec Kall Pall g hg B
  have hsTop : Tendsto (fun j => (aStrict j : ℝ)) atTop atTop := by
    simpa only [aStrict] using
      minimalStrictSchedule_tendsto_atTop Kall Pall g hg B
  have hdTop : Tendsto (fun j => (aDouble j : ℝ)) atTop atTop := by
    apply SolenoidalDiagonal.realScales_tendsto
    simpa only [aDouble] using hd.2.2.2.1
  have hsep0' : aStrict 0 = aDouble 0 := by
    simpa only [aStrict, aDouble] using hsep0
  have hsep1' : aStrict 1 < aDouble 1 := by
    simpa only [aStrict, aDouble] using hsep1
  have horder : ∀ j, aStrict j ≤ aDouble j := by
    intro j
    simpa only [aStrict, aDouble] using
      minimalStrictSchedule_le_canonicalSchedule Kall Pall g hg B j

  have hcut : ∀ (a : ℕ → ℕ),
      (∀ j, 0 < a j) →
      (∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ r : ℝ,
        0 < r → r ≤ 1 / (a j : ℝ) →
          |DiagonalScale.logPowerWeight (Kall j m) (Pall j m) (g j / 2) r| ≤
            (1 / 2 : ℝ) ^ j) →
      ∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
        q (A i) (fun j => g j / 2) (CutStageEstimates.cutLoss L) S := by
    intro a hapos hsmall i j hj m hm x hx
    apply CutStageEstimates.cut_product_bound_of_threshold hU hSU hq hpos
      (hA i j hj) m
      (show (1 : ℝ) ≤ (a j : ℝ) by
        exact_mod_cast (Nat.succ_le_of_lt (hapos j)))
      (by positivity) (K := Kall j m) (P := Pall j m)
      (g := g j) (L := CutStageEstimates.cutLoss L m) ?_
      (hsmall j hj m hm) x hx
    intro c hc y hy hq1
    apply (hb i j hj m c hc y hy hq1).trans
    have hlog : 1 ≤ 1 + |Real.log (q y)| :=
      le_add_of_nonneg_right (abs_nonneg _)
    apply mul_le_mul_of_nonneg_right _
      (Real.rpow_nonneg (hpos y hy).le _)
    calc
      _ ≤ Kall j m * (1 + |Real.log (q y)|) ^
          (CutStageEstimates.cutLog (p i) j m) :=
        mul_le_mul_of_nonneg_right (hKle i j m)
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlog (hPle i j m))
        (hKall j m).le

  have hStrictBounds : ∀ i, DiagonalJetBounds.CutStageBounds
      (fun j => (aStrict j : ℝ)) q (A i) (fun j => g j / 2)
      (CutStageEstimates.cutLoss L) S := by
    apply hcut aStrict
    · simpa only [aStrict] using hs.2.1
    · simpa only [aStrict] using hs.2.2.2.2
  have hDoubleBounds : ∀ i, DiagonalJetBounds.CutStageBounds
      (fun j => (aDouble j : ℝ)) q (A i) (fun j => g j / 2)
      (CutStageEstimates.cutLoss L) S := by
    apply hcut aDouble
    · simpa only [aDouble] using hd.2.1
    · simpa only [aDouble] using hd.2.2.2.2.2

  refine ⟨aStrict, aDouble,
    hBlower.trans ?_, hBlower.trans ?_,
    ?_, ?_, ?_, ?_, hsTop, hdTop, ?_,
    hsep0', hsep1', horder, hStrictBounds, hDoubleBounds⟩
  · simpa only [aStrict] using hs.1
  · simpa only [aDouble] using hd.1
  · simpa only [aStrict] using hs.2.1
  · simpa only [aDouble] using hd.2.1
  · simpa only [aStrict] using hs.2.2.1
  · simpa only [aDouble] using hd.2.2.2.1
  · simpa only [aDouble] using hd.2.2.1

end NavierStokes.V511PairedFiniteCutBounds
