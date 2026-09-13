import NavierStokes.V590QuantitativeJetRate
import NavierStokes.SpacetimeEndpoint

/-!
# v5.9: source-endpoint specialization of the terminal activation bridge

The actual residual-flatness machinery is evaluated in the one-sided endpoint
filter

  `𝓝[SpacetimeEndpoint.openPast 1] (1, 0)`.

This file proves that the late-time plateau `t > 3/4` is automatically large in
that exact filter.  Consequently the constant-preserving activation bridge
from `V590QuantitativeJetRate` needs no extra plateau hypothesis when used at
the source endpoint.

This is still a weighted endpoint certificate, not a standard force norm.
-/

noncomputable section

namespace NavierStokes.V590EndpointActivationBridge

open Set Filter Function ProblemStatement
open scoped Topology BigOperators ContDiff
open V590QuantitativeJetRate

/-- The exact one-sided spacetime filter used by the pinned residual endpoint
arguments. -/
def endpoint : Filter SpaceTime :=
  𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))

/-- The time-switch plateau is automatically a neighborhood in the source's
one-sided endpoint filter. -/
theorem terminalPlateau_mem_endpoint :
    V590QuantitativeJetRate.terminalPlateau ∈ endpoint := by
  apply mem_nhdsWithin_of_mem_nhds
  apply V590QuantitativeJetRate.terminalPlateau_open.mem_nhds
  norm_num [V590QuantitativeJetRate.terminalPlateau]

/-- At the exact source endpoint, an explicit incoming-residual certificate
passes through time activation with the same constant, with no additional
late-time hypothesis supplied by the caller. -/
def quantitativeActivatedResidualAtEndpoint
    {q : SpaceTime → ℝ} {m : ℕ} {r : ℝ}
    (u : VelocityField) (p : PressureField)
    (W : V590QuantitativeJetRate.QuantitativeJetRate endpoint q
      (V590QuantitativeJetRate.incomingResidual u p) m r) :
    V590QuantitativeJetRate.QuantitativeJetRate endpoint q
      (V590QuantitativeJetRate.activatedResidual u p) m r :=
  V590QuantitativeJetRate.quantitativeActivatedResidualOfTerminal
    u p W terminalPlateau_mem_endpoint

@[simp] theorem quantitativeActivatedResidualAtEndpoint_constant
    {q : SpaceTime → ℝ} {m : ℕ} {r : ℝ}
    (u : VelocityField) (p : PressureField)
    (W : V590QuantitativeJetRate.QuantitativeJetRate endpoint q
      (V590QuantitativeJetRate.incomingResidual u p) m r) :
    (quantitativeActivatedResidualAtEndpoint u p W).constant = W.constant := rfl

end NavierStokes.V590EndpointActivationBridge
