import NavierStokes.V590CanonicalDiagonalScale
import NavierStokes.SolenoidalDiagonal

/-!
# v5.10: minimal strict diagonal schedule

The pinned source selects local admissible integer scales and then replaces
them by `DiagonalScale.doublingEnvelope`, enforcing

  2 * a n ≤ a (n + 1).

The final mixed-candidate assembly visibly consumes positivity, strict
monotonicity, divergence of the real scales, local support separation, smooth
sums, and residual vanishing; it does not itself use the factor-two witness.

This file isolates the numerical part of that observation. We define the
smallest elementary envelope that dominates the local scales while being
strictly increasing:

  strictEnvelope b 0       = max 1 (b 0)
  strictEnvelope b (n + 1) = max (b (n + 1)) (strictEnvelope b n + 1).

This is not yet an end-to-end candidate theorem and does not prove a smaller
force norm.
-/

noncomputable section

namespace NavierStokes.V510MinimalStrictSchedule

open Set Filter
open V590CanonicalDiagonalScale
open scoped Topology

/-- Minimal recursive envelope that dominates `b` and grows strictly by at
least one, without imposing factor-two growth. -/
def strictEnvelope (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => max 1 (b 0)
  | n + 1 => max (b (n + 1)) (strictEnvelope b n + 1)

theorem strictEnvelope_ge (b : ℕ → ℕ) (n : ℕ) :
    b n ≤ strictEnvelope b n := by
  cases n with
  | zero => exact le_max_right _ _
  | succ n => exact le_max_left _ _

theorem strictEnvelope_growth (b : ℕ → ℕ) (n : ℕ) :
    strictEnvelope b n + 1 ≤ strictEnvelope b (n + 1) := by
  exact le_max_right _ _

theorem strictEnvelope_pos (b : ℕ → ℕ) (n : ℕ) :
    0 < strictEnvelope b n := by
  cases n with
  | zero => exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  | succ n => exact lt_of_lt_of_le (Nat.zero_lt_succ _) (strictEnvelope_growth b n)

theorem strictEnvelope_strictMono (b : ℕ → ℕ) :
    StrictMono (strictEnvelope b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (strictEnvelope_growth b n)

theorem strictEnvelope_lower_bound (b : ℕ → ℕ) (n : ℕ) :
    n + 1 ≤ strictEnvelope b n := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih => exact (Nat.succ_le_succ ih).trans (strictEnvelope_growth b n)

/-- The weaker +1 envelope is still unbounded quickly enough for local
finiteness at every fixed positive similarity coordinate. -/
theorem strictEnvelope_reciprocal_eventually_small (b : ℕ → ℕ)
    (q : ℝ) (hq : 0 < q) :
    ∃ N : ℕ, ∀ j ≥ N, 1 / (strictEnvelope b j : ℝ) < q := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hq
  refine ⟨N, ?_⟩
  intro j hj
  have hn : (N : ℝ) + 1 ≤ (strictEnvelope b j : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right hj 1).trans (strictEnvelope_lower_bound b j)
  exact lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hn) hN

/-- The minimal strict envelope is pointwise no larger than the source's
factor-two envelope on the same local scales. -/
theorem strictEnvelope_le_doublingEnvelope (b : ℕ → ℕ) :
    ∀ n, strictEnvelope b n ≤ DiagonalScale.doublingEnvelope b n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hdpos := DiagonalScale.doublingEnvelope_pos b n
      have hstep : strictEnvelope b n + 1 ≤
          2 * DiagonalScale.doublingEnvelope b n := by
        have h1 : strictEnvelope b n + 1 ≤
            DiagonalScale.doublingEnvelope b n + 1 := Nat.add_le_add_right ih 1
        have h2 : DiagonalScale.doublingEnvelope b n + 1 ≤
            2 * DiagonalScale.doublingEnvelope b n := by omega
        exact h1.trans h2
      exact max_le_max (le_refl _) hstep

/-- Increasing the integer cutoff scale only shrinks the interval on which a
`StageAdmissible` estimate must hold. -/
theorem stageAdmissible_mono_scale
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ) {B j a b : ℕ}
    (hab : a ≤ b) (ha : StageAdmissible C p g B j a) :
    StageAdmissible C p g B j b := by
  rcases ha with ⟨hapos, hB, hbound⟩
  have hbpos : 0 < b := lt_of_lt_of_le hapos hab
  refine ⟨hbpos, ?_, ?_⟩
  · intro hj0
    exact (hB hj0).trans hab
  · intro hj m hm q hq hqb
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hrecip : (1 : ℝ) / (b : ℝ) ≤ 1 / (a : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast hapos) habR
    exact hbound hj m hm q hq (hqb.trans hrecip)

/-- Canonical schedule using the same least local admissible scales as v5.9,
but only the minimal +1 strict envelope. -/
def minimalStrictSchedule (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ) : ℕ → ℕ :=
  strictEnvelope (leastLocalScale C p g hg B)

/-- The minimal strict schedule satisfies all numerical conclusions of the
source selector except the intentionally removed factor-two growth condition. -/
theorem minimalStrictSchedule_spec
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ) :
    B ≤ minimalStrictSchedule C p g hg B 0 ∧
    (∀ j, 0 < minimalStrictSchedule C p g hg B j) ∧
    StrictMono (minimalStrictSchedule C p g hg B) ∧
    (∀ q : ℝ, 0 < q → ∃ N : ℕ, ∀ j ≥ N,
      1 / (minimalStrictSchedule C p g hg B j : ℝ) < q) ∧
    (∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
      0 < q → q ≤ 1 / (minimalStrictSchedule C p g hg B j : ℝ) →
        |DiagonalScale.logPowerWeight (C j m) (p j m) (g j / 2) q| ≤
          (1 / 2 : ℝ) ^ j) := by
  let b := leastLocalScale C p g hg B
  have hb : ∀ j, StageAdmissible C p g B j (b j) := by
    intro j
    exact leastLocalScale_spec C p g hg B j
  refine ⟨?_, strictEnvelope_pos b, strictEnvelope_strictMono b,
    strictEnvelope_reciprocal_eventually_small b, ?_⟩
  · exact ((hb 0).2.1 rfl).trans (strictEnvelope_ge b 0)
  · intro j hj m hm q hq hqa
    have hstage := stageAdmissible_mono_scale C p g
      (strictEnvelope_ge b j) (hb j)
    exact hstage.2.2 hj m hm q hq hqa

/-- For identical local admissibility data, removing factor-two growth never
increases any selected cutoff scale. -/
theorem minimalStrictSchedule_le_canonicalSchedule
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B j : ℕ) :
    minimalStrictSchedule C p g hg B j ≤
      canonicalSchedule C p g hg B j := by
  exact strictEnvelope_le_doublingEnvelope
    (leastLocalScale C p g hg B) j

/-- The real-valued scales of the minimal strict schedule still tend to
infinity, exactly the property used by locally finite diagonal sums. -/
theorem minimalStrictSchedule_tendsto_atTop
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ) :
    Tendsto (fun j => (minimalStrictSchedule C p g hg B j : ℝ)) atTop atTop := by
  exact SolenoidalDiagonal.realScales_tendsto
    (minimalStrictSchedule_spec C p g hg B).2.2.1

end NavierStokes.V510MinimalStrictSchedule
