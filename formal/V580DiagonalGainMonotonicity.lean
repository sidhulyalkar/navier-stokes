import NavierStokes.DiagonalScale

/-!
# v5.8 diagonal schedule monotonicity in the residual gain

The mixed diagonal construction selects a cutoff schedule using smallness of

  C * (1 + |log q|)^p * q^(g/2)

for `0 < q <= 1/a_j`. Once a stronger analytic/physical ledger raises the
finite-stage gain, the same selected cutoff schedule should not become harder
to satisfy: on `0 < q <= 1`, increasing the exponent only decreases the real
power `q^r`.

This file proves exactly that monotonicity, both for a single logarithmic
weight and for the full stagewise smallness predicate used by
`DiagonalScale.exists_diagonal_scales`.

It does **not** prove that the construction selects a strictly smaller scale,
because the source's scale theorem is existential and does not choose a
canonical or minimal witness.
-/

namespace NavierStokes.V580DiagonalGainMonotonicity

open NavierStokes.DiagonalScale

/-- On the punctured unit interval, increasing the positive-power exponent can
only decrease the absolute logarithmic weight. No sign hypothesis on `C` or
`p` is needed because the common prefactor is compared after taking absolute
values. -/
theorem abs_logPowerWeight_mono_exponent
    {C p r r' q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hrr : r ≤ r') :
    |logPowerWeight C p r' q| ≤ |logPowerWeight C p r q| := by
  unfold logPowerWeight
  rw [abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hq.le r'),
    abs_of_nonneg (Real.rpow_nonneg hq.le r)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 hrr)
    (mul_nonneg (abs_nonneg C) (abs_nonneg ((1 + |Real.log q|) ^ p)))

/-- Any scalar smallness certificate proved for exponent `r` is automatically
valid for a larger exponent `r'` on `0 < q ≤ 1`. -/
theorem smallness_mono_exponent
    {C p r r' q ε : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hrr : r ≤ r')
    (hsmall : |logPowerWeight C p r q| ≤ ε) :
    |logPowerWeight C p r' q| ≤ ε :=
  (abs_logPowerWeight_mono_exponent hq hq1 hrr).trans hsmall

/-- The complete stagewise numerical smallness property used by the diagonal
schedule is monotone in the gain. Therefore every schedule valid for `g`
remains valid for a pointwise larger `g'`.

The hypothesis `1 <= a j` is only used to infer `q <= 1` from the schedule's
native condition `q <= 1 / a j`. The actual schedules are positive naturals,
so this is automatic in downstream applications. -/
theorem schedule_smallness_mono_gain
    {C p : ℕ → ℕ → ℝ} {g g' : ℕ → ℝ} {a : ℕ → ℕ}
    (ha : ∀ j, 1 ≤ a j)
    (hgain : ∀ j, 1 ≤ j → g j ≤ g' j)
    (hold : ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
      0 < q → q ≤ 1 / (a j : ℝ) →
        |logPowerWeight (C j m) (p j m) (g j / 2) q| ≤ (1 / 2 : ℝ) ^ j) :
    ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
      0 < q → q ≤ 1 / (a j : ℝ) →
        |logPowerWeight (C j m) (p j m) (g' j / 2) q| ≤ (1 / 2 : ℝ) ^ j := by
  intro j hj m hm q hq hqa
  have haj : (1 : ℝ) ≤ (a j : ℝ) := by exact_mod_cast ha j
  have hajpos : (0 : ℝ) < (a j : ℝ) := lt_of_lt_of_le zero_lt_one haj
  have hrecip : (1 : ℝ) / (a j : ℝ) ≤ 1 := by
    rw [one_div, inv_le_one₀ hajpos]
    exact haj
  have hq1 : q ≤ 1 := hqa.trans hrecip
  have hhalf : g j / 2 ≤ g' j / 2 := by
    exact div_le_div_of_nonneg_right (hgain j hj) (by norm_num)
  exact smallness_mono_exponent hq hq1 hhalf (hold j hj m hm q hq hqa)

/-- A `+delta` gain with nonnegative `delta` is a direct specialization. -/
theorem schedule_smallness_add_gain
    {C p : ℕ → ℕ → ℝ} {g δ : ℕ → ℝ} {a : ℕ → ℕ}
    (ha : ∀ j, 1 ≤ a j)
    (hδ : ∀ j, 1 ≤ j → 0 ≤ δ j)
    (hold : ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
      0 < q → q ≤ 1 / (a j : ℝ) →
        |logPowerWeight (C j m) (p j m) (g j / 2) q| ≤ (1 / 2 : ℝ) ^ j) :
    ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
      0 < q → q ≤ 1 / (a j : ℝ) →
        |logPowerWeight (C j m) (p j m) ((g j + δ j) / 2) q| ≤ (1 / 2 : ℝ) ^ j := by
  apply schedule_smallness_mono_gain ha
  · intro j hj
    exact le_add_of_nonneg_right (hδ j hj)
  · exact hold

end NavierStokes.V580DiagonalGainMonotonicity
