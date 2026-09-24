import NavierStokes.CandidateFromLimits
import NavierStokes.MixedPeriodicAssembly

/-!
# v5.11: late-time force to mixed-residual bridge

The final force is defined by `CandidateFromLimits.force` through a smooth
Taylor--Borel extension at the singular time. For physical comparison of two
schedule choices, that future extension should not be mistaken for an
additional source of presingular force.

The key bridge is stated for generic presingular inputs `u,p₀`, together with
source-native local equalities identifying them with the mixed physical fields
at the comparison point. This formulation avoids forcing Lean's elaborator to
unfold the full periodic/localized construction merely to type-check the
dependent derivative-limit witness.

On `3/4 < t < 1`, activation is locally the identity. If `u,p₀` are locally
the mixed velocity/pressure at `(t,x)`, the actual globally smooth force is
exactly `MixedPeriodicAssembly.originalResidual` there.

No force-size or norm ordering is claimed.
-/

noncomputable section

namespace NavierStokes.V511LateForceResidualBridge

open ProblemStatement Set Filter
open scoped Topology ContDiff

/-- Generic late-time bridge. The only spatial input needed is local equality
of the force inputs with the mixed physical velocity and pressure.

The dependent `CandidateFromLimits.force` expression is expensive for Lean to
elaborate even though its source theorem is already compiled, so this bridge
uses a larger local heartbeat budget without changing any assumptions or
conclusions. -/
set_option maxHeartbeats 800000 in
theorem force_eq_originalResidual_of_eventuallyEq_late
    {u : VelocityField} {p₀ : PressureField}
    {A v : VelocityField} {p : PressureField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p₀ preSingularDomain)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly
      (fun t x => iteratedFDeriv ℝ n
        (fun z => navierStokesResidual u p₀ z.1 z.2) (t, x))
      (fun x => L x n) (𝓝[<] (1 : ℝ)))
    {t : ℝ} (ht : 3 / 4 < t) (ht1 : t < 1)
    {x : Space}
    (hvel : u =ᶠ[𝓝 (t, x)] MixedPeriodicAssembly.velocity A v)
    (hpress : p₀ =ᶠ[𝓝 (t, x)] p) :
    CandidateFromLimits.force u p₀ hu hp L hlim (t, x) =
      MixedPeriodicAssembly.originalResidual A v p (t, x) := by
  have ht0 : 0 ≤ t := by linarith
  have hforce :
      CandidateFromLimits.force u p₀ hu hp L hlim (t, x) =
        navierStokesResidual
          (TimeLocalization.activatedVelocity u)
          (TimeLocalization.activatedPressure p₀) t x :=
    CandidateFromLimits.force_eq_activated_residual
      u p₀ hu hp L hlim ht0 ht1 x

  have htime :=
    ResidualRegularity.residual_eventuallyEq
      (TimeLocalization.activatedVelocity_eventuallyEq_late u ht x)
      (TimeLocalization.activatedPressure_eventuallyEq_late p₀ ht x)
  have hlate := htime.self_of_nhds

  have hspace :=
    ResidualRegularity.residual_eventuallyEq hvel hpress
  have hphysical := hspace.self_of_nhds

  calc
    CandidateFromLimits.force u p₀ hu hp L hlim (t, x) =
      navierStokesResidual
        (TimeLocalization.activatedVelocity u)
        (TimeLocalization.activatedPressure p₀) t x := hforce
    _ =
      navierStokesResidual u p₀ t x := hlate
    _ = MixedPeriodicAssembly.originalResidual A v p (t, x) := by
      simpa only [MixedPeriodicAssembly.originalResidual] using hphysical

/-- The source periodic/localized inputs satisfy the local hypotheses of the
generic bridge everywhere on the spatial plateau. -/
theorem periodic_inputs_eventuallyEq_on_plateau
    (A v : VelocityField) (p : PressureField)
    {t : ℝ} {x : Space} (hx : x ∈ SpatialLocalization.plateau) :
    MixedPeriodicAssembly.periodicVelocity A v
        =ᶠ[𝓝 (t, x)] MixedPeriodicAssembly.velocity A v ∧
      SpatialLocalization.periodicPressure p =ᶠ[𝓝 (t, x)] p := by
  exact ⟨
    MixedPeriodicAssembly.periodicVelocity_eventuallyEq
      (z := (t, x)) A v hx,
    SpatialLocalization.periodicPressure_eventuallyEq
      (z := (t, x)) p hx⟩

end NavierStokes.V511LateForceResidualBridge
