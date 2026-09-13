import NavierStokes.DiagonalScale

/-!
# v5.9: canonical least-admissible diagonal scales

The pinned source proves existence of a diagonal cutoff schedule by choosing an
unspecified local integer scale at every stage and then applying
`DiagonalScale.doublingEnvelope`.

For quantitative comparison that existential choice is too weak: two gain
certificates may produce unrelated witnesses.  This module replaces only the
*numerical scale selection* with a deterministic least-admissible local scale
(`Nat.find`), then applies the exact same source doubling envelope.

The main target is monotonicity:

  stronger stage gain  =>  no larger canonical cutoff scale.

Raw constants `C`, logarithmic powers `p`, the initial floor `B`, and the stage
index are held fixed.  This changes no PDE estimate and proves no force-norm
ordering by itself.
-/

noncomputable section

namespace NavierStokes.V590CanonicalDiagonalScale

open Set Filter
open scoped Topology BigOperators

/-- Exact local numerical obligation used inside the source proof of
`exists_diagonal_scales`. -/
def StageAdmissible (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (B j b : ℕ) : Prop :=
  0 < b ∧
  (j = 0 → B ≤ b) ∧
  (1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
    0 < q → q ≤ 1 / (b : ℝ) →
      |DiagonalScale.logPowerWeight (C j m) (p j m) (g j / 2) q| ≤
        (1 / 2 : ℝ) ^ j)

/-- The pinned logarithmic limit theorem gives at least one admissible local
integer scale at every stage. -/
theorem exists_stageAdmissible (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B j : ℕ) :
    ∃ b : ℕ, StageAdmissible C p g B j b := by
  by_cases hj : j = 0
  · refine ⟨max 1 B, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    · intro _
      exact le_max_right _ _
    · intro hpos
      omega
  · have hjpos : 1 ≤ j := by omega
    obtain ⟨b, hb, hbound⟩ := DiagonalScale.exists_integer_scale
      (Finset.range (j + 3)) (C j) (p j) (g j / 2)
      ((1 / 2 : ℝ) ^ j)
      (by linarith [hg j hjpos]) (by positivity)
    refine ⟨b, hb, ?_, ?_⟩
    · intro hzero
      exact False.elim (hj hzero)
    · intro _ m hm q hq hqb
      exact hbound m (Finset.mem_range.mpr (by omega)) q hq hqb

/-- Increasing the gain makes the local admissibility condition no harder for
the same integer scale.  The proof uses only `0 < q ≤ 1`. -/
theorem stageAdmissible_mono_gain
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    {B j b : ℕ}
    (hgain : 1 ≤ j → gWeak j ≤ gStrong j)
    (hb : StageAdmissible C p gWeak B j b) :
    StageAdmissible C p gStrong B j b := by
  rcases hb with ⟨hbpos, hB, hweak⟩
  refine ⟨hbpos, hB, ?_⟩
  intro hj m hm q hq hqb
  have hb1 : 1 ≤ b := by omega
  have hb1R : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
  have hrecip : (1 : ℝ) / (b : ℝ) ≤ 1 := by
    simpa using
      (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hb1R)
  have hq1 : q ≤ 1 := hqb.trans hrecip
  have hpow : q ^ (gStrong j / 2) ≤ q ^ (gWeak j / 2) := by
    exact Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith [hgain hj])
  have hweight :
      |DiagonalScale.logPowerWeight (C j m) (p j m) (gStrong j / 2) q| ≤
        |DiagonalScale.logPowerWeight (C j m) (p j m) (gWeak j / 2) q| := by
    rw [DiagonalScale.logPowerWeight, DiagonalScale.logPowerWeight]
    rw [abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hq.le _),
      abs_of_nonneg (Real.rpow_nonneg hq.le _)]
    exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  exact hweight.trans (hweak hj m hm q hq hqb)

/-- Least local integer scale satisfying the exact pinned numerical obligation. -/
def leastLocalScale (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B j : ℕ) : ℕ :=
  Nat.find (exists_stageAdmissible C p g hg B j)

theorem leastLocalScale_spec (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B j : ℕ) :
    StageAdmissible C p g B j (leastLocalScale C p g hg B j) :=
  Nat.find_spec (exists_stageAdmissible C p g hg B j)

/-- Pointwise gain improvement can only decrease the least admissible local
scale. -/
theorem leastLocalScale_mono_gain
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    (hWeak : ∀ j, 1 ≤ j → 0 < gWeak j)
    (hStrong : ∀ j, 1 ≤ j → 0 < gStrong j)
    (hgain : ∀ j, 1 ≤ j → gWeak j ≤ gStrong j)
    (B j : ℕ) :
    leastLocalScale C p gStrong hStrong B j ≤
      leastLocalScale C p gWeak hWeak B j := by
  apply Nat.find_min'
  exact stageAdmissible_mono_gain C p (hgain j)
    (leastLocalScale_spec C p gWeak hWeak B j)

/-- The source doubling envelope is monotone in its local-scale input. -/
theorem doublingEnvelope_mono {b c : ℕ → ℕ}
    (hbc : ∀ n, b n ≤ c n) :
    ∀ n, DiagonalScale.doublingEnvelope b n ≤
      DiagonalScale.doublingEnvelope c n := by
  intro n
  induction n with
  | zero =>
      simpa [DiagonalScale.doublingEnvelope] using
        (max_le_max (show (1 : ℕ) ≤ 1 by rfl) (hbc 0))
  | succ n ih =>
      simpa [DiagonalScale.doublingEnvelope] using
        (max_le_max (hbc (n + 1)) (Nat.mul_le_mul_left 2 ih))

/-- Deterministic diagonal schedule: least local admissible scales followed by
the exact source doubling envelope. -/
def canonicalSchedule (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ) : ℕ → ℕ :=
  DiagonalScale.doublingEnvelope (leastLocalScale C p g hg B)

/-- The canonical schedule satisfies the same numerical conclusions as the
source's existential `exists_diagonal_scales` theorem. -/
theorem canonicalSchedule_spec
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ) :
    B ≤ canonicalSchedule C p g hg B 0 ∧
    (∀ j, 0 < canonicalSchedule C p g hg B j) ∧
    (∀ j, 2 * canonicalSchedule C p g hg B j ≤
      canonicalSchedule C p g hg B (j + 1)) ∧
    StrictMono (canonicalSchedule C p g hg B) ∧
    (∀ q : ℝ, 0 < q → ∃ N : ℕ, ∀ j ≥ N,
      1 / (canonicalSchedule C p g hg B j : ℝ) < q) ∧
    (∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
      0 < q → q ≤ 1 / (canonicalSchedule C p g hg B j : ℝ) →
        |DiagonalScale.logPowerWeight (C j m) (p j m) (g j / 2) q| ≤
          (1 / 2 : ℝ) ^ j) := by
  let b := leastLocalScale C p g hg B
  have hb : ∀ j, StageAdmissible C p g B j (b j) := by
    intro j
    exact leastLocalScale_spec C p g hg B j
  refine ⟨?_, DiagonalScale.doublingEnvelope_pos b,
    DiagonalScale.doublingEnvelope_growth b,
    DiagonalScale.doublingEnvelope_strictMono b,
    DiagonalScale.doublingEnvelope_reciprocal_eventually_small b, ?_⟩
  · exact ((hb 0).2.1 rfl).trans (DiagonalScale.doublingEnvelope_ge b 0)
  · intro j hj m hm q hq hqa
    apply (hb j).2.2 hj m hm q hq
    apply hqa.trans
    apply one_div_le_one_div_of_le
    · exact_mod_cast (hb j).1
    · exact_mod_cast DiagonalScale.doublingEnvelope_ge b j

/-- Main Q1 comparison theorem: with raw constants, logarithmic powers and
initial floor fixed, pointwise stronger gain yields a pointwise no-larger
canonical cutoff schedule. -/
theorem canonicalSchedule_mono_gain
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    (hWeak : ∀ j, 1 ≤ j → 0 < gWeak j)
    (hStrong : ∀ j, 1 ≤ j → 0 < gStrong j)
    (hgain : ∀ j, 1 ≤ j → gWeak j ≤ gStrong j)
    (B j : ℕ) :
    canonicalSchedule C p gStrong hStrong B j ≤
      canonicalSchedule C p gWeak hWeak B j := by
  apply doublingEnvelope_mono
  intro n
  exact leastLocalScale_mono_gain C p hWeak hStrong hgain B n

end NavierStokes.V590CanonicalDiagonalScale
