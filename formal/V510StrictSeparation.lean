import NavierStokes.V510MinimalStrictSchedule

/-!
# v5.10: strict separation from the source doubling envelope

Removing factor-two growth as a proof obligation does not automatically imply
that the selected numerical schedule changes.  The local admissibility scales
may themselves already grow fast enough that the minimal strict and doubling
envelopes coincide.

This module isolates a sufficient condition for an actual strict change.  If
the previous source doubling scale is larger than one and the next local scale
does not itself reach the doubled previous scale, then the minimal +1 envelope
is strictly smaller at the next stage.

This is a numerical construction statement only.  It proves no force-norm
ordering.
-/

noncomputable section

namespace NavierStokes.V510StrictSeparation

open V590CanonicalDiagonalScale V510MinimalStrictSchedule

/-- Sufficient condition for strict separation of the two envelopes on the
same local-scale sequence. -/
theorem strictEnvelope_lt_doublingEnvelope_of_local_below_double
    (b : ℕ → ℕ) (n : ℕ)
    (hprev : 1 < DiagonalScale.doublingEnvelope b n)
    (hlocal :
      b (n + 1) < 2 * DiagonalScale.doublingEnvelope b n) :
    strictEnvelope b (n + 1) <
      DiagonalScale.doublingEnvelope b (n + 1) := by
  have henv :
      strictEnvelope b n ≤ DiagonalScale.doublingEnvelope b n :=
    strictEnvelope_le_doublingEnvelope b n
  have hstep :
      strictEnvelope b n + 1 <
        2 * DiagonalScale.doublingEnvelope b n := by
    omega
  change
    max (b (n + 1)) (strictEnvelope b n + 1) <
      max (b (n + 1)) (2 * DiagonalScale.doublingEnvelope b n)
  rw [max_eq_right (Nat.le_of_lt hlocal)]
  exact max_lt hlocal hstep

/-- Instantiation for the canonical least-admissible local scales used by the
v5.9/v5.10 comparison framework. -/
theorem minimalStrictSchedule_lt_canonicalSchedule_of_local_below_double
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B n : ℕ)
    (hprev : 1 < canonicalSchedule C p g hg B n)
    (hlocal :
      leastLocalScale C p g hg B (n + 1) <
        2 * canonicalSchedule C p g hg B n) :
    minimalStrictSchedule C p g hg B (n + 1) <
      canonicalSchedule C p g hg B (n + 1) := by
  exact strictEnvelope_lt_doublingEnvelope_of_local_below_double
    (leastLocalScale C p g hg B) n hprev hlocal

/-- Equivalent failure mode for this sufficient criterion: if the next local
least scale already reaches the source doubled floor, the max recursion may be
controlled by the same local requirement and the envelope deletion need not
change the selected integer at that stage. -/
theorem doublingEnvelope_eq_local_of_double_le_local
    (b : ℕ → ℕ) (n : ℕ)
    (hlocal :
      2 * DiagonalScale.doublingEnvelope b n ≤ b (n + 1)) :
    DiagonalScale.doublingEnvelope b (n + 1) = b (n + 1) := by
  change max (b (n + 1)) (2 * DiagonalScale.doublingEnvelope b n) =
    b (n + 1)
  exact max_eq_left hlocal

end NavierStokes.V510StrictSeparation
