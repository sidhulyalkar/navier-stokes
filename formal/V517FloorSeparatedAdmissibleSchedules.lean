import NavierStokes.V590CanonicalDiagonalScale
import NavierStokes.V510StrictScheduleSeparation

/-!
# v5.17: floor-separated canonical admissible schedules

The v5.16 axis witness needs two schedules that already differ at stage zero.
The older strict-vs-doubling pair intentionally shares its initial floor, so it
cannot trigger that witness.

Here we keep the same local analytic data `C,p,g` and the same deterministic
canonical selector, but choose two support-compatible initial floors:

  Bsmall >= lower,
  Blarge = 3 * Bsmall.

Because positive-stage local admissibility is unchanged and each canonical
schedule independently satisfies the pinned numerical obligations, both are
legitimate schedules for the same raw finite-stage problem.  Their zeroth
scales are exact:

  aSmall 0 = Bsmall,
  aLarge 0 = 3 * Bsmall,

hence

  5 * aSmall 0 < 2 * aLarge 0.

The common small floor is also chosen large enough that the explicit v5.16
comparison point q★ = (2/5) / aSmall(0) lies strictly inside any prescribed
positive local-q radius `qbig`.

This is still a numerical schedule theorem.  It does not by itself construct
two forces or compare force norms.
-/

noncomputable section

namespace NavierStokes.V517FloorSeparatedAdmissibleSchedules

open Set Filter
open V590CanonicalDiagonalScale
open V510StrictScheduleSeparation
open scoped Topology

/-- For a floor at least one, the canonical source-style schedule starts
exactly at that floor. -/
theorem canonicalSchedule_zero_eq_floor
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) {B : ℕ} (hB : 1 ≤ B) :
    canonicalSchedule C p g hg B 0 = B := by
  unfold canonicalSchedule
  rw [leastLocalScale_zero_eq_max_one C p g hg B]
  simp only [DiagonalScale.doublingEnvelope]
  rw [max_eq_right hB, max_eq_right hB]

/-- Two canonical schedules for the same local analytic data, separated only by
their admissible initial floors.  Both stay inside the requested physical
local-q radius, and their stage-zero scales satisfy the strict v5.16 interior
ratio. -/
theorem exists_floor_separated_canonical_schedules
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j)
    {qbig : ℝ} (hqbig : 0 < qbig) (lower : ℕ) :
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      lower ≤ Bsmall ∧
      1 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      aSmall = canonicalSchedule C p g hg Bsmall ∧
      aLarge = canonicalSchedule C p g hg Blarge ∧
      (∀ j, 0 < aSmall j) ∧
      (∀ j, 0 < aLarge j) ∧
      StrictMono aSmall ∧
      StrictMono aLarge ∧
      Tendsto (fun j => (aSmall j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aLarge j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aSmall j ≤ aSmall (j + 1)) ∧
      (∀ j, 2 * aLarge j ≤ aLarge (j + 1)) ∧
      (∀ j, 1 / (aSmall j : ℝ) < qbig) ∧
      (∀ j, 1 / (aLarge j : ℝ) < qbig) ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) < qbig := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hqbig
  let Bsmall : ℕ := max lower (n + 1)
  let Blarge : ℕ := 3 * Bsmall
  let aSmall := canonicalSchedule C p g hg Bsmall
  let aLarge := canonicalSchedule C p g hg Blarge

  have hBsmallLower : lower ≤ Bsmall := by
    exact le_max_left _ _
  have hBsmallOne : 1 ≤ Bsmall := by
    exact (Nat.succ_le_succ (Nat.zero_le n)).trans (le_max_right _ _)
  have hBsmallPos : 0 < Bsmall := Nat.zero_lt_of_lt hBsmallOne
  have hBlargeOne : 1 ≤ Blarge := by
    dsimp [Blarge]
    omega

  have hs := canonicalSchedule_spec C p g hg Bsmall
  have hl := canonicalSchedule_spec C p g hg Blarge
  have hs0 : aSmall 0 = Bsmall := by
    dsimp only [aSmall]
    exact canonicalSchedule_zero_eq_floor C p g hg hBsmallOne
  have hl0 : aLarge 0 = Blarge := by
    dsimp only [aLarge]
    exact canonicalSchedule_zero_eq_floor C p g hg hBlargeOne

  have hsRecip : ∀ j, 1 / (aSmall j : ℝ) < qbig := by
    intro j
    have hmono : aSmall 0 ≤ aSmall j :=
      hs.2.2.2.1.monotone (Nat.zero_le j)
    have hBaj : Bsmall ≤ aSmall j := by simpa only [hs0] using hmono
    have hnB : n + 1 ≤ Bsmall := le_max_right _ _
    have hnaj : n + 1 ≤ aSmall j := hnB.trans hBaj
    have hle : (1 : ℝ) / (aSmall j : ℝ) ≤
        1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast hnaj)
    exact hle.trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

  have hlRecip : ∀ j, 1 / (aLarge j : ℝ) < qbig := by
    intro j
    have hmono : aLarge 0 ≤ aLarge j :=
      hl.2.2.2.1.monotone (Nat.zero_le j)
    have hsmallLarge : Bsmall ≤ Blarge := by
      dsimp [Blarge]
      omega
    have hBaj : Blarge ≤ aLarge j := by simpa only [hl0] using hmono
    have hnB : n + 1 ≤ Bsmall := le_max_right _ _
    have hnaj : n + 1 ≤ aLarge j := hnB.trans (hsmallLarge.trans hBaj)
    have hle : (1 : ℝ) / (aLarge j : ℝ) ≤
        1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast hnaj)
    exact hle.trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

  have hqStar :
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) < qbig := by
    have hs0pos : (0 : ℝ) < aSmall 0 := by
      exact_mod_cast hs.2.1 0
    have hfrac : (2 / 5 : ℝ) / (aSmall 0 : ℝ) <
        1 / (aSmall 0 : ℝ) := by
      apply div_lt_div_of_pos_right (by norm_num) hs0pos
    exact hfrac.trans (hsRecip 0)

  refine ⟨Bsmall, Blarge, aSmall, aLarge,
    hBsmallLower, hBsmallOne, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hsRecip, hlRecip, hs0, hl0, ?_, hqStar⟩
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

end NavierStokes.V517FloorSeparatedAdmissibleSchedules
