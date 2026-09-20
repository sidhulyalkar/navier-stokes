import NavierStokes.CandidateFromLimits
import NavierStokes.MixedPeriodicAssembly

/-!
# v5.11: late-time force to mixed-residual bridge

The final force is defined by `CandidateFromLimits.force` through a smooth
Taylor--Borel extension at the singular time. For physical comparison of two
schedule choices, that future extension should not be mistaken for an
additional source of presingular force.

This module proves an exact source-locked bridge. At every point with

* `3/4 < t < 1`, so the time switch is locally one; and
* spatial coordinate in `SpatialLocalization.plateau`, so the spatial
  localization/periodization is locally the identity,

the actual constructed force equals the incoming
`MixedPeriodicAssembly.originalResidual` exactly.

The result is independent of the future-side extension details. It is the
intended P3 bridge for comparing paired strict-vs-doubling constructions on a
late-time physical region.
-/

noncomputable section

namespace NavierStokes.V511LateForceResidualBridge

open ProblemStatement Set Filter
open scoped Topology ContDiff

/-- Short names keep the final force input and its derivative-limit hypothesis
syntactically identical, avoiding an expensive definitional-equality search
through the full periodic/localized expressions. -/
private abbrev periodicU (A v : VelocityField) : VelocityField :=
  MixedPeriodicAssembly.periodicVelocity A v

private abbrev periodicP (p : PressureField) : PressureField :=
  SpatialLocalization.periodicPressure p

/-- On the late-time spatial plateau, the actual globally smooth force is
exactly the original mixed Navier--Stokes residual. -/
theorem force_eq_originalResidual_late_plateau
    {A v : VelocityField} {p : PressureField}
    (hu : ContDiffOn ℝ ∞ (periodicU A v) preSingularDomain)
    (hp : ContDiffOn ℝ ∞ (periodicP p) preSingularDomain)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly
      (fun t x => iteratedFDeriv ℝ n
        (fun z => navierStokesResidual (periodicU A v) (periodicP p) z.1 z.2)
        (t, x))
      (fun x => L x n) (𝓝[<] (1 : ℝ)))
    {t : ℝ} (ht : 3 / 4 < t) (ht1 : t < 1)
    {x : Space} (hx : x ∈ SpatialLocalization.plateau) :
    CandidateFromLimits.force (periodicU A v) (periodicP p)
        hu hp L hlim (t, x) =
      MixedPeriodicAssembly.originalResidual A v p (t, x) := by
  rw [CandidateFromLimits.force_eq_activated_residual
    (periodicU A v) (periodicP p)
    hu hp L hlim (by linarith) ht1 x]

  have htime :=
    ResidualRegularity.residual_eventuallyEq
      (TimeLocalization.activatedVelocity_eventuallyEq_late
        (periodicU A v) ht x)
      (TimeLocalization.activatedPressure_eventuallyEq_late
        (periodicP p) ht x)
  have hlate := htime.self_of_nhds

  have hspace :=
    ResidualRegularity.residual_eventuallyEq
      (MixedPeriodicAssembly.periodicVelocity_eventuallyEq A v hx)
      (SpatialLocalization.periodicPressure_eventuallyEq p hx)
  have hplateau := hspace.self_of_nhds

  calc
    navierStokesResidual
        (TimeLocalization.activatedVelocity (periodicU A v))
        (TimeLocalization.activatedPressure (periodicP p)) t x =
      navierStokesResidual (periodicU A v) (periodicP p) t x := hlate
    _ = MixedPeriodicAssembly.originalResidual A v p (t, x) := by
      simpa only [periodicU, periodicP, MixedPeriodicAssembly.originalResidual]
        using hplateau

end NavierStokes.V511LateForceResidualBridge
