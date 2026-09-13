import NavierStokes.DiagonalJetBounds

/-!
# v5.8: gain monotonicity for fixed cut fields

This module isolates a claim-boundary fact needed to interpret the boosted
physical-stage certificate correctly.

For a fixed cutoff schedule `a` and fixed stage family `A`, a stronger decay
gain implies every weaker decay gain on a carrier where `0 < q ≤ 1`.  No new
schedule and no new physical field is constructed.

Consequently, if the v5.8 boosted assembly closes, the schedule/fields produced
from that boosted certificate can also be viewed through the original weaker
published gain.  This is a certificate-comparison theorem, not a force-norm
improvement theorem.
-/

noncomputable section

namespace NavierStokes.V580CutStageGainMonotonicity

open Set

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On `0 < q ≤ 1`, increasing the gain exponent strengthens a fixed
`CutStageBounds` certificate.  The cutoff schedule and stage family are kept
literally unchanged. -/
theorem cutStageBounds_mono_gain
    {a : ℕ → ℝ} {q : E → ℝ} {A : ℕ → E → V}
    {gStrong gWeak L : ℕ → ℝ} {U : Set E}
    (hq : ∀ x ∈ U, 0 < q x ∧ q x ≤ 1)
    (hgain : ∀ j, 1 ≤ j → gWeak j ≤ gStrong j)
    (hb : DiagonalJetBounds.CutStageBounds a q A gStrong L U) :
    DiagonalJetBounds.CutStageBounds a q A gWeak L U := by
  intro j hj m hm x hx
  have hstrong := hb j hj m hm x hx
  have hpow :
      q x ^ (gStrong j - L m) ≤ q x ^ (gWeak j - L m) := by
    exact Real.rpow_le_rpow_of_exponent_ge (hq x hx).1 (hq x hx).2
      (sub_le_sub_right (hgain j hj) (L m))
  exact hstrong.trans
    (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (1 / 2 : ℝ) ^ j))

end NavierStokes.V580CutStageGainMonotonicity
