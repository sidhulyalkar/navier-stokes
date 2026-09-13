import NavierStokes.V590StrictScaleCrossing

/-!
# v5.9: stronger gain buys cutoff-scale relaxation

The pinned diagonal-scale API hides the multiplicative constants used to pick
local integer scales.  For strict comparison we should not invent numerical
values for those existential constants.

This module proves a constant-cancelling comparison.  If a weak gain is already
admissible at scale `a`, then a stronger gain is admissible at a smaller scale
`b` provided the extra power compensates for the enlarged reciprocal interval:

  (1 / b)^(gStrong/2) ≤ (1 / a)^(gWeak/2).

On the old interval q ≤ 1/a we use monotonicity in the gain.  On the newly
exposed annulus 1/a < q ≤ 1/b, the nonnegative logarithmic power only decreases
as q moves away from zero, so the unknown multiplicative constant cancels
against the weak endpoint estimate at q = 1/a.

This changes no field and proves no force-norm ordering by itself.
-/

noncomputable section

namespace NavierStokes.V590GainBuysScale

open V590CanonicalDiagonalScale V590StrictScaleCrossing

/-- Scalar constant-cancelling comparison on a relaxed cutoff annulus. -/
theorem logPowerWeight_relax
    (C p gWeak gStrong q a b : ℝ)
    (hp : 0 ≤ p) (hgw : 0 ≤ gWeak) (hgs : 0 ≤ gStrong)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hqlo : 1 / a ≤ q) (hqhi : q ≤ 1 / b)
    (hpower : (1 / b) ^ (gStrong / 2) ≤ (1 / a) ^ (gWeak / 2)) :
    |DiagonalScale.logPowerWeight C p (gStrong / 2) q| ≤
      |DiagonalScale.logPowerWeight C p (gWeak / 2) (1 / a)| := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hqa0 : 0 < (1 : ℝ) / a := one_div_pos.mpr ha0
  have hqb0 : 0 < (1 : ℝ) / b := one_div_pos.mpr hb0
  have hq0 : 0 < q := lt_of_lt_of_le hqa0 hqlo
  have hqa1 : (1 : ℝ) / a ≤ 1 := by
    simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) ha)
  have hqb1 : (1 : ℝ) / b ≤ 1 := by
    simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hb)
  have hq1 : q ≤ 1 := hqhi.trans hqb1
  have hlog : Real.log (1 / a) ≤ Real.log q :=
    Real.log_le_log hqa0 hqlo
  have hloga : Real.log (1 / a) ≤ 0 := Real.log_nonpos hqa0.le hqa1
  have hlogq : Real.log q ≤ 0 := Real.log_nonpos hq0.le hq1
  have habslog : |Real.log q| ≤ |Real.log (1 / a)| := by
    rw [abs_of_nonpos hlogq, abs_of_nonpos hloga]
    linarith
  have hlogbase : 1 + |Real.log q| ≤ 1 + |Real.log (1 / a)| := by
    linarith
  have hlogpow :
      (1 + |Real.log q|) ^ p ≤ (1 + |Real.log (1 / a)|) ^ p := by
    apply Real.rpow_le_rpow
    · positivity
    · exact hlogbase
    · exact hp
  have hqpow : q ^ (gStrong / 2) ≤ (1 / b) ^ (gStrong / 2) := by
    apply Real.rpow_le_rpow hq0.le hqhi
    linarith
  have hpow : q ^ (gStrong / 2) ≤ (1 / a) ^ (gWeak / 2) :=
    hqpow.trans hpower
  unfold DiagonalScale.logPowerWeight
  rw [abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + |Real.log q|) p),
    abs_of_nonneg (Real.rpow_nonneg hq0.le (gStrong / 2)),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + |Real.log (1 / a)|) p),
    abs_of_nonneg (Real.rpow_nonneg hqa0.le (gWeak / 2))]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hlogpow (abs_nonneg C)) hpow
    (Real.rpow_nonneg hq0.le _) (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (by positivity) _))

/-- Constant-cancelling stage theorem.  A stronger gain may use a smaller
integer cutoff scale if its extra power pays for the enlarged interval. -/
theorem stageAdmissible_relax_scale
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    {B j a b : ℕ}
    (hj : 1 ≤ j)
    (hgain : gWeak j ≤ gStrong j)
    (hgw : 0 ≤ gWeak j) (hgs : 0 ≤ gStrong j)
    (hp : ∀ m, m ≤ j + 2 → 0 ≤ p j m)
    (hbpos : 0 < b)
    (hweak : StageAdmissible C p gWeak B j a)
    (hpower :
      ((1 : ℝ) / (b : ℝ)) ^ (gStrong j / 2) ≤
        ((1 : ℝ) / (a : ℝ)) ^ (gWeak j / 2)) :
    StageAdmissible C p gStrong B j b := by
  have hapos : 0 < a := hweak.1
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  refine ⟨hbpos, ?_, ?_⟩
  · intro hj0
    omega
  · intro _ m hm q hq hqb
    by_cases hqa : q ≤ 1 / (a : ℝ)
    · have hs := stageAdmissible_mono_gain C p
        (gWeak := gWeak) (gStrong := gStrong)
        (B := B) (j := j) (b := a) (fun _ => hgain) hweak
      exact hs.2.2 hj m hm q hq hqa
    · have hqlo : (1 : ℝ) / (a : ℝ) ≤ q := le_of_not_ge hqa
      have hcompare := logPowerWeight_relax
        (C j m) (p j m) (gWeak j) (gStrong j) q (a : ℝ) (b : ℝ)
        (hp m hm) hgw hgs (by exact_mod_cast ha1) (by exact_mod_cast hb1)
        hqlo hqb hpower
      have hweakEndpoint := hweak.2.2 hj m hm ((1 : ℝ) / (a : ℝ))
        (one_div_pos.mpr (by exact_mod_cast hapos)) le_rfl
      exact hcompare.trans hweakEndpoint

/-- Plugging the relaxation theorem into the strict-crossing interface: one
smaller integer satisfying the power budget forces the least local scale to
decrease. -/
theorem strict_local_crossing_of_power_budget
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    (hWeak : ∀ j, 1 ≤ j → 0 < gWeak j)
    (hStrong : ∀ j, 1 ≤ j → 0 < gStrong j)
    (hgain : ∀ j, 1 ≤ j → gWeak j ≤ gStrong j)
    (hp : ∀ j m, m ≤ j + 2 → 0 ≤ p j m)
    (B j b : ℕ) (hj : 1 ≤ j)
    (hbpos : 0 < b)
    (hbelow : b < leastLocalScale C p gWeak hWeak B j)
    (hpower :
      ((1 : ℝ) / (b : ℝ)) ^ (gStrong j / 2) ≤
        ((1 : ℝ) / (leastLocalScale C p gWeak hWeak B j : ℝ)) ^
          (gWeak j / 2)) :
    leastLocalScale C p gStrong hStrong B j <
      leastLocalScale C p gWeak hWeak B j := by
  apply strict_local_gain_crossing_of_candidate C p hWeak hStrong B j b hbelow
  apply stageAdmissible_relax_scale C p hj (hgain j hj)
    (hWeak j hj).le (hStrong j hj).le (hp j) hbpos
    (leastLocalScale_spec C p gWeak hWeak B j) hpower

end NavierStokes.V590GainBuysScale
