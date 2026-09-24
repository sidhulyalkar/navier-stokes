import NavierStokes.CutStageEstimates
import NavierStokes.V517FloorSeparatedAdmissibleSchedules

/-!
# v5.17: finite cut bounds for floor-separated canonical schedules

This reuses the v5.11 common-constant aggregation, but forks the same canonical
schedule constructor at two different initial floors rather than changing the
recursive rule.

Both schedules use the same raw stage family, the same aggregated cutoff
constants `Kall/Pall`, and the same gain.  Their floors are `B` and `3B`.
Thus they satisfy the exact same finite cut-stage estimates while also meeting
the v5.16 stage-zero interior-separation ratio.
-/

noncomputable section

namespace NavierStokes.V517FloorSeparatedFiniteCutBounds

open Set Function Filter
open V590CanonicalDiagonalScale
open V510StrictScheduleSeparation
open V517FloorSeparatedAdmissibleSchedules
open scoped Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

theorem exists_floor_separated_finite_cut_bounds
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
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      lower ≤ Bsmall ∧
      1 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      (∀ j, 0 < aSmall j) ∧
      (∀ j, 0 < aLarge j) ∧
      StrictMono aSmall ∧
      StrictMono aLarge ∧
      Tendsto (fun j => (aSmall j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aLarge j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aSmall j ≤ aSmall (j + 1)) ∧
      (∀ j, 2 * aLarge j ≤ aLarge (j + 1)) ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      (∀ i, DiagonalJetBounds.CutStageBounds (fun j => (aSmall j : ℝ))
        q (A i) (fun j => g j / 2) (CutStageEstimates.cutLoss L) S) ∧
      (∀ i, DiagonalJetBounds.CutStageBounds (fun j => (aLarge j : ℝ))
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

  let Bsmall : ℕ := max 1 lower
  let Blarge : ℕ := 3 * Bsmall
  let aSmall := canonicalSchedule Kall Pall g hg Bsmall
  let aLarge := canonicalSchedule Kall Pall g hg Blarge
  have hBsmallOne : 1 ≤ Bsmall := le_max_left _ _
  have hBsmallLower : lower ≤ Bsmall := le_max_right _ _
  have hBlargeOne : 1 ≤ Blarge := by
    dsimp [Blarge]
    omega
  have hs := canonicalSchedule_spec Kall Pall g hg Bsmall
  have hl := canonicalSchedule_spec Kall Pall g hg Blarge
  have hs0 : aSmall 0 = Bsmall := by
    dsimp only [aSmall]
    exact canonicalSchedule_zero_eq_floor Kall Pall g hg hBsmallOne
  have hl0 : aLarge 0 = Blarge := by
    dsimp only [aLarge]
    exact canonicalSchedule_zero_eq_floor Kall Pall g hg hBlargeOne

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

  have hsCut : ∀ i, DiagonalJetBounds.CutStageBounds
      (fun j => (aSmall j : ℝ)) q (A i) (fun j => g j / 2)
      (CutStageEstimates.cutLoss L) S := by
    apply hcut aSmall
    · simpa only [aSmall] using hs.2.1
    · simpa only [aSmall] using hs.2.2.2.2.2
  have hlCut : ∀ i, DiagonalJetBounds.CutStageBounds
      (fun j => (aLarge j : ℝ)) q (A i) (fun j => g j / 2)
      (CutStageEstimates.cutLoss L) S := by
    apply hcut aLarge
    · simpa only [aLarge] using hl.2.1
    · simpa only [aLarge] using hl.2.2.2.2.2

  refine ⟨Bsmall, Blarge, aSmall, aLarge,
    hBsmallLower, hBsmallOne, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hs0, hl0, ?_, hsCut, hlCut⟩
  · simpa only [aSmall] using hs.2.1
  · simpa only [aLarge] using hl.2.1
  · simpa only [aSmall] using hs.2.2.2.1
  · simpa only [aLarge] using hl.2.2.2.1
  · exact SolenoidalDiagonal.realScales_tendsto
      (by simpa only [aSmall] using hs.2.2.2.1)
  · exact SolenoidalDiagonal.realScales_tendsto
      (by simpa only [aLarge] using hl.2.2.2.1)
  · simpa only [aSmall] using hs.2.2.1
  · simpa only [aLarge] using hl.2.2.1
  · rw [hs0, hl0]
    dsimp [Blarge]
    omega

end NavierStokes.V517FloorSeparatedFiniteCutBounds
