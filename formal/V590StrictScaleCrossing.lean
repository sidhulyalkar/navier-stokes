import NavierStokes.V590CanonicalDiagonalScale

/-!
# v5.9: strict cutoff-scale crossing criteria

The canonical-scale theorem proves only a non-strict comparison under gain
improvement.  Because the selected scales are natural numbers, a stronger
analytic gain can remain in the same integer bucket.  This module isolates the
exact extra obligation required for a genuine construction change.

There are two layers:

1. a local least-admissible scale becomes strictly smaller exactly when the
   stronger gain admits some integer below the old least scale;
2. a strict local decrease survives the source `doublingEnvelope` whenever the
   old local scale, rather than the inherited doubling floor, is the active
   branch of the max.

These are construction-parameter statements only.  They do not yet assert a
smaller Navier--Stokes force norm.
-/

noncomputable section

namespace NavierStokes.V590StrictScaleCrossing

open V590CanonicalDiagonalScale

/-- Exact threshold characterization for the least admissible integer scale.
The least scale is below `t` iff some admissible integer already lies below
`t`. -/
theorem leastLocalScale_lt_iff_exists_admissible_below
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B j t : ℕ) :
    leastLocalScale C p g hg B j < t ↔
      ∃ b : ℕ, b < t ∧ StageAdmissible C p g B j b := by
  constructor
  · intro hlt
    exact ⟨leastLocalScale C p g hg B j, hlt,
      leastLocalScale_spec C p g hg B j⟩
  · rintro ⟨b, hbt, hb⟩
    have hmin : leastLocalScale C p g hg B j ≤ b := by
      classical
      unfold leastLocalScale
      apply Nat.find_min'
      exact hb
    exact lt_of_le_of_lt hmin hbt

/-- Q1-strict characterization.  A stronger certificate genuinely changes the
local integer scale exactly when it makes some integer below the old least
scale admissible. -/
theorem strict_local_gain_crossing_iff
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    (hWeak : ∀ j, 1 ≤ j → 0 < gWeak j)
    (hStrong : ∀ j, 1 ≤ j → 0 < gStrong j)
    (B j : ℕ) :
    leastLocalScale C p gStrong hStrong B j <
        leastLocalScale C p gWeak hWeak B j ↔
      ∃ b : ℕ,
        b < leastLocalScale C p gWeak hWeak B j ∧
        StageAdmissible C p gStrong B j b := by
  simpa using
    (leastLocalScale_lt_iff_exists_admissible_below
      C p gStrong hStrong B j (leastLocalScale C p gWeak hWeak B j))

/-- Convenient sufficient form: one explicit stronger-gain admissible integer
below the old least scale forces a strict local change. -/
theorem strict_local_gain_crossing_of_candidate
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    (hWeak : ∀ j, 1 ≤ j → 0 < gWeak j)
    (hStrong : ∀ j, 1 ≤ j → 0 < gStrong j)
    (B j b : ℕ)
    (hbelow : b < leastLocalScale C p gWeak hWeak B j)
    (hadm : StageAdmissible C p gStrong B j b) :
    leastLocalScale C p gStrong hStrong B j <
      leastLocalScale C p gWeak hWeak B j :=
  (strict_local_gain_crossing_iff C p hWeak hStrong B j).2
    ⟨b, hbelow, hadm⟩

/-- A strict local scale decrease survives the source doubling envelope when
the weak local scale is itself larger than the inherited doubled previous
scale.  This makes the max branch explicit and exposes the second quantization
barrier. -/
theorem doublingEnvelope_strict_of_local_dominates
    {bStrong bWeak : ℕ → ℕ}
    (hmono : ∀ n, bStrong n ≤ bWeak n) (n : ℕ)
    (hlocal : bStrong (n + 1) < bWeak (n + 1))
    (hdominates :
      2 * DiagonalScale.doublingEnvelope bWeak n < bWeak (n + 1)) :
    DiagonalScale.doublingEnvelope bStrong (n + 1) <
      DiagonalScale.doublingEnvelope bWeak (n + 1) := by
  have hprev : DiagonalScale.doublingEnvelope bStrong n ≤
      DiagonalScale.doublingEnvelope bWeak n :=
    doublingEnvelope_mono hmono n
  have htwice :
      2 * DiagonalScale.doublingEnvelope bStrong n < bWeak (n + 1) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 hprev) hdominates
  change
    max (bStrong (n + 1)) (2 * DiagonalScale.doublingEnvelope bStrong n) <
      max (bWeak (n + 1)) (2 * DiagonalScale.doublingEnvelope bWeak n)
  rw [max_eq_left (Nat.le_of_lt hdominates)]
  exact max_lt_iff.mpr ⟨hlocal, htwice⟩

/-- End-to-end strict schedule criterion.  Pointwise stronger gain gives the
non-strict local comparison; if one positive stage crosses an integer
admissibility threshold and the weak local scale dominates the inherited
source doubling floor, the canonical schedules are strictly different at that
stage. -/
theorem canonicalSchedule_strict_of_local_crossing
    (C p : ℕ → ℕ → ℝ) {gWeak gStrong : ℕ → ℝ}
    (hWeak : ∀ j, 1 ≤ j → 0 < gWeak j)
    (hStrong : ∀ j, 1 ≤ j → 0 < gStrong j)
    (hgain : ∀ j, 1 ≤ j → gWeak j ≤ gStrong j)
    (B n : ℕ)
    (hlocal :
      leastLocalScale C p gStrong hStrong B (n + 1) <
        leastLocalScale C p gWeak hWeak B (n + 1))
    (hdominates :
      2 * canonicalSchedule C p gWeak hWeak B n <
        leastLocalScale C p gWeak hWeak B (n + 1)) :
    canonicalSchedule C p gStrong hStrong B (n + 1) <
      canonicalSchedule C p gWeak hWeak B (n + 1) := by
  unfold canonicalSchedule at hdominates ⊢
  apply doublingEnvelope_strict_of_local_dominates
  · intro j
    exact leastLocalScale_mono_gain C p hWeak hStrong hgain B j
  · exact hlocal
  · exact hdominates

end NavierStokes.V590StrictScaleCrossing
