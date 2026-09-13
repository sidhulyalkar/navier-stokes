import NavierStokes.DiagonalResidual
import NavierStokes.TimeLocalization

/-!
# v5.9: explicit quantitative witnesses behind `JetRate`

The pinned source's `DiagonalResidual.JetRate` intentionally packages an
endpoint estimate existentially:

  `∃ C ≥ 0, ∀ᶠ x in l, ‖D^m f x‖ ≤ C * q x ^ r`.

That is sufficient for flatness and vanishing-jet arguments, but it hides the
constant and the filter-large carrier on which the estimate is known.  Those
hidden choices must be exposed before one can make honest quantitative
comparisons between two gain certificates.

This file adds only a lossless interface plus constant-preserving algebra.  It
does **not** define a standard force norm, does not choose a canonical/minimal
constant, and does not claim a smaller force.
-/

noncomputable section

namespace NavierStokes.V590QuantitativeJetRate

open Set Filter Function ProblemStatement
open scoped Topology BigOperators ContDiff

variable {D V : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A named-set weighted derivative bound with an explicit constant. -/
def WeightedJetBoundOn (S : Set D) (q : D → ℝ) (f : D → V)
    (m : ℕ) (r C : ℝ) : Prop :=
  ∀ x ∈ S, ‖iteratedFDeriv ℝ m f x‖ ≤ C * (q x) ^ r

/-- The quantitative data hidden by `DiagonalResidual.JetRate`:

* one filter-large carrier set;
* one nonnegative constant;
* the weighted derivative bound on that carrier.

No optimality of the carrier or constant is asserted. -/
structure QuantitativeJetRate (l : Filter D) (q : D → ℝ) (f : D → V)
    (m : ℕ) (r : ℝ) where
  carrier : Set D
  carrier_mem : carrier ∈ l
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : WeightedJetBoundOn carrier q f m r constant

/-- `QuantitativeJetRate` is a lossless repackaging of the pinned source's
`JetRate`.  In particular this theorem adds no estimate. -/
theorem nonempty_quantitativeJetRate_iff_jetRate
    {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r : ℝ} :
    Nonempty (QuantitativeJetRate l q f m r) ↔
      DiagonalResidual.JetRate l q f m r := by
  constructor
  · rintro ⟨W⟩
    refine ⟨W.constant, W.constant_nonneg, ?_⟩
    filter_upwards [W.carrier_mem] with x hx
    exact W.bound x hx
  · rintro ⟨C, hC, hb⟩
    let S : Set D :=
      {x | ‖iteratedFDeriv ℝ m f x‖ ≤ C * (q x) ^ r}
    have hS : S ∈ l := by
      change ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C * (q x) ^ r
      exact hb
    refine ⟨{
      carrier := S
      carrier_mem := hS
      constant := C
      constant_nonneg := hC
      bound := ?_
    }⟩
    intro x hx
    exact hx

/-- Direct extraction form useful for later force-size consumers. -/
theorem exists_explicit_weighted_bound_of_jetRate
    {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r : ℝ}
    (hf : DiagonalResidual.JetRate l q f m r) :
    ∃ S : Set D, S ∈ l ∧ ∃ C : ℝ, 0 ≤ C ∧ WeightedJetBoundOn S q f m r C := by
  obtain ⟨W⟩ := nonempty_quantitativeJetRate_iff_jetRate.mpr hf
  exact ⟨W.carrier, W.carrier_mem, W.constant, W.constant_nonneg, W.bound⟩

namespace QuantitativeJetRate

/-- Restrict a quantitative certificate to any smaller carrier that is still
large in the same filter.  The constant is retained literally. -/
def restrict {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r : ℝ}
    (W : QuantitativeJetRate l q f m r) (S : Set D)
    (hS : S ∈ l) (hsub : S ⊆ W.carrier) :
    QuantitativeJetRate l q f m r where
  carrier := S
  carrier_mem := hS
  constant := W.constant
  constant_nonneg := W.constant_nonneg
  bound x hx := W.bound x (hsub hx)

@[simp] theorem restrict_constant
    {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r : ℝ}
    (W : QuantitativeJetRate l q f m r) (S : Set D)
    (hS : S ∈ l) (hsub : S ⊆ W.carrier) :
    (W.restrict S hS hsub).constant = W.constant := rfl

/-- Weaken the power on the *same carrier with the same constant*, provided
`q ∈ (0,1]` pointwise there.  This is the quantitative analogue of the pinned
`JetRate.weaken` theorem and is deliberately stronger bookkeeping than merely
reconstructing another existential `JetRate`. -/
def weaken {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r s : ℝ}
    (W : QuantitativeJetRate l q f m r)
    (hq : ∀ x ∈ W.carrier, 0 < q x ∧ q x ≤ 1) (hsr : s ≤ r) :
    QuantitativeJetRate l q f m s where
  carrier := W.carrier
  carrier_mem := W.carrier_mem
  constant := W.constant
  constant_nonneg := W.constant_nonneg
  bound := by
    intro x hx
    exact (W.bound x hx).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hq x hx).1 (hq x hx).2 hsr)
        W.constant_nonneg)

@[simp] theorem weaken_carrier
    {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r s : ℝ}
    (W : QuantitativeJetRate l q f m r)
    (hq : ∀ x ∈ W.carrier, 0 < q x ∧ q x ≤ 1) (hsr : s ≤ r) :
    (W.weaken hq hsr).carrier = W.carrier := rfl

@[simp] theorem weaken_constant
    {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r s : ℝ}
    (W : QuantitativeJetRate l q f m r)
    (hq : ∀ x ∈ W.carrier, 0 < q x ∧ q x ≤ 1) (hsr : s ≤ r) :
    (W.weaken hq hsr).constant = W.constant := rfl

/-- Transfer a quantitative certificate across an equality on an open set.
The carrier is intersected with that set and the constant is unchanged. -/
def congrOn {l : Filter D} {q : D → ℝ} {f g : D → V} {m : ℕ} {r : ℝ}
    (W : QuantitativeJetRate l q f m r) {U : Set D}
    (hU : IsOpen U) (hlU : U ∈ l) (hfg : EqOn f g U) :
    QuantitativeJetRate l q g m r where
  carrier := W.carrier ∩ U
  carrier_mem := inter_mem W.carrier_mem hlU
  constant := W.constant
  constant_nonneg := W.constant_nonneg
  bound := by
    intro x hx
    rw [← ResidualStability.iteratedFDeriv_eqOn hU hfg m hx.2]
    exact W.bound x hx.1

@[simp] theorem congrOn_constant
    {l : Filter D} {q : D → ℝ} {f g : D → V} {m : ℕ} {r : ℝ}
    (W : QuantitativeJetRate l q f m r) {U : Set D}
    (hU : IsOpen U) (hlU : U ∈ l) (hfg : EqOn f g U) :
    (W.congrOn hU hlU hfg).constant = W.constant := rfl

/-- Add two quantitative certificates without losing their constants to a new
existential choice.  The common carrier is their intersection with the open
smoothness domain, and the resulting constant is literally `C_f + C_g`. -/
def add {l : Filter D} {q : D → ℝ} {f g : D → V} {m : ℕ} {r : ℝ}
    (Wf : QuantitativeJetRate l q f m r)
    (Wg : QuantitativeJetRate l q g m r) {U : Set D}
    (hU : IsOpen U) (hlU : U ∈ l)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    QuantitativeJetRate l q (fun x => f x + g x) m r where
  carrier := (Wf.carrier ∩ Wg.carrier) ∩ U
  carrier_mem := inter_mem (inter_mem Wf.carrier_mem Wg.carrier_mem) hlU
  constant := Wf.constant + Wg.constant
  constant_nonneg := add_nonneg Wf.constant_nonneg Wg.constant_nonneg
  bound := by
    intro x hx
    calc
      ‖iteratedFDeriv ℝ m (fun y => f y + g y) x‖ ≤
          ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ :=
        ResidualStability.norm_jet_add_le hU hsf hsg hx.2 m
      _ ≤ Wf.constant * (q x) ^ r + Wg.constant * (q x) ^ r :=
        add_le_add (Wf.bound x hx.1.1) (Wg.bound x hx.1.2)
      _ = (Wf.constant + Wg.constant) * (q x) ^ r := by ring

@[simp] theorem add_constant
    {l : Filter D} {q : D → ℝ} {f g : D → V} {m : ℕ} {r : ℝ}
    (Wf : QuantitativeJetRate l q f m r)
    (Wg : QuantitativeJetRate l q g m r) {U : Set D}
    (hU : IsOpen U) (hlU : U ∈ l)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    (Wf.add Wg hU hlU hsf hsg).constant = Wf.constant + Wg.constant := rfl

/-- Forgetting the explicit data recovers exactly a source `JetRate`. -/
theorem jetRate {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r : ℝ}
    (W : QuantitativeJetRate l q f m r) :
    DiagonalResidual.JetRate l q f m r :=
  nonempty_quantitativeJetRate_iff_jetRate.mp ⟨W⟩

end QuantitativeJetRate

/-! ## Terminal activation bridge -/

/-- The open plateau on which the pinned time switch is identically one. -/
def terminalPlateau : Set SpaceTime := {z | (3 / 4 : ℝ) < z.1}

theorem terminalPlateau_open : IsOpen terminalPlateau := by
  change IsOpen (Prod.fst ⁻¹' Ioi (3 / 4 : ℝ))
  exact isOpen_Ioi.preimage continuous_fst

/-- Incoming presingular Navier--Stokes residual, as a spacetime field. -/
def incomingResidual (u : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual u p z.1 z.2

/-- Residual after the source's time activation, before later force extension. -/
def activatedResidual (u : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (TimeLocalization.activatedVelocity u)
    (TimeLocalization.activatedPressure p) z.1 z.2

/-- On the terminal plateau the activation changes no residual at all. -/
theorem incomingResidual_eq_activatedResidual_on_terminal
    (u : VelocityField) (p : PressureField) :
    EqOn (incomingResidual u p) (activatedResidual u p) terminalPlateau := by
  intro z hz
  change (3 / 4 : ℝ) < z.1 at hz
  exact (TimeLocalization.activated_residual_eq_late u p hz z.2).symm

/-- Any explicit endpoint residual certificate transfers to the activated
residual on the terminal plateau with the **same constant**.  Only the carrier
is intersected with `t > 3/4`.

This is the first quantitative force-pipeline bridge.  It is still not a
standard force norm and says nothing about the earlier activation interval. -/
def quantitativeActivatedResidualOfTerminal
    {l : Filter SpaceTime} {q : SpaceTime → ℝ} {m : ℕ} {r : ℝ}
    (u : VelocityField) (p : PressureField)
    (W : QuantitativeJetRate l q (incomingResidual u p) m r)
    (hlate : terminalPlateau ∈ l) :
    QuantitativeJetRate l q (activatedResidual u p) m r :=
  W.congrOn terminalPlateau_open hlate
    (incomingResidual_eq_activatedResidual_on_terminal u p)

@[simp] theorem quantitativeActivatedResidualOfTerminal_constant
    {l : Filter SpaceTime} {q : SpaceTime → ℝ} {m : ℕ} {r : ℝ}
    (u : VelocityField) (p : PressureField)
    (W : QuantitativeJetRate l q (incomingResidual u p) m r)
    (hlate : terminalPlateau ∈ l) :
    (quantitativeActivatedResidualOfTerminal u p W hlate).constant = W.constant := rfl

end NavierStokes.V590QuantitativeJetRate
