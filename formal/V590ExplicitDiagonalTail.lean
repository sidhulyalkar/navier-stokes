import NavierStokes.V590QuantitativeJetRate
import NavierStokes.DiagonalResidual

/-!
# v5.9: explicit constant for the pinned diagonal tail

`DiagonalResidual.jetRate_diagonal_tail` proves a fixed-prefix tail estimate
with the literal constant `(1/2)^J`, but the public `JetRate` proposition hides
that constant existentially.

This file replays that source proof into `QuantitativeJetRate`, retaining the
same physical field, exponent, neighborhood mechanism, and the exact constant

  C_J = (1/2)^J.

This is quantitative endpoint information.  It is not yet a force norm and it
does not compare two assembled witnesses.
-/

noncomputable section

namespace NavierStokes.V590ExplicitDiagonalTail

open Set Filter Function
open scoped Topology BigOperators ContDiff
open V590QuantitativeJetRate

variable {D V : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The same fixed-prefix diagonal-potential tail as the pinned source theorem,
now with the exact source constant `(1/2)^J` retained in the type. -/
theorem quantitative_diagonal_tail
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : D → ℝ} {A : ℕ → D → V} {g L : ℕ → ℝ}
    {U : Set D} {l : Filter D}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    (hlU : ∀ᶠ x in l, x ∈ U)
    (hlq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m ≤ J + 3) :
    V590QuantitativeJetRate.QuantitativeJetRate l q
      (fun x => SolenoidalDiagonal.potentialSum a q A x -
        DiagonalJetBounds.uncutPrefix A (J + 1) x)
      m (g (J + 1) - L m) := by
  obtain ⟨δ, hδ, hprefix⟩ :=
    DiagonalJetBounds.partialPotential_eventuallyEq_uncut a q A (J + 1)
  let S : Set D :=
    U ∩ {x | 0 < q x ∧ q x ≤ 1} ∩ {x | |q x| < δ}
  have hsmall : ∀ᶠ x in l, |q x| < δ :=
    hqzero.eventually (gt_mem_nhds hδ)
  have hS : S ∈ l := by
    filter_upwards [hlU, hlq, hsmall] with x hx hqx hs
    exact ⟨⟨hx, hqx⟩, hs⟩
  refine {
    carrier := S
    carrier_mem := hS
    constant := (1 / 2 : ℝ) ^ J
    constant_nonneg := by positivity
    bound := ?_
  }
  intro x hx
  rcases hx with ⟨⟨hxU, hqx⟩, hsmallx⟩
  have hpref := hprefix x (hq.contDiffAt (hU.mem_nhds hxU)).continuousAt
    (by simpa only [abs_of_pos hqx.1] using hsmallx)
  have heq :
      (fun y => SolenoidalDiagonal.potentialSum a q A y -
        SolenoidalDiagonal.partialPotential a q A (J + 1) y) =ᶠ[𝓝 x]
      (fun y => SolenoidalDiagonal.potentialSum a q A y -
        DiagonalJetBounds.uncutPrefix A (J + 1) y) := by
    filter_upwards [hpref] with y hy
    rw [hy]
  rw [← (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq heq m).self_of_nhds]
  exact DiagonalJetBounds.potential_tail_jet_bound ha hU hq hA hg hb hxU
    hqx.1 hqx.2 J m hm

@[simp] theorem quantitative_diagonal_tail_constant
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : D → ℝ} {A : ℕ → D → V} {g L : ℕ → ℝ}
    {U : Set D} {l : Filter D}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    (hlU : ∀ᶠ x in l, x ∈ U)
    (hlq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m ≤ J + 3) :
    (quantitative_diagonal_tail ha hU hq hA hg hb hlU hlq hqzero J m hm).constant =
      (1 / 2 : ℝ) ^ J := rfl

/-- Forgetting the explicit witness recovers the pinned public theorem's
`JetRate` conclusion. -/
theorem quantitative_diagonal_tail_jetRate
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : D → ℝ} {A : ℕ → D → V} {g L : ℕ → ℝ}
    {U : Set D} {l : Filter D}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    (hlU : ∀ᶠ x in l, x ∈ U)
    (hlq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m ≤ J + 3) :
    DiagonalResidual.JetRate l q
      (fun x => SolenoidalDiagonal.potentialSum a q A x -
        DiagonalJetBounds.uncutPrefix A (J + 1) x)
      m (g (J + 1) - L m) :=
  (quantitative_diagonal_tail ha hU hq hA hg hb hlU hlq hqzero J m hm).jetRate

end NavierStokes.V590ExplicitDiagonalTail
