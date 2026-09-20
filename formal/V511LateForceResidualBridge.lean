import NavierStokes.CandidateFromLimits
import NavierStokes.MixedPeriodicAssembly

/-!
# v5.11: late-time force to mixed-residual bridge

The final force is defined by `CandidateFromLimits.force` through a smooth
Taylor--Borel extension at the singular time.  For physical comparison of two
schedule choices, that future extension should not be mistaken for an
additional source of presingular force.

This module proves an exact source-locked bridge.  At every point with

* `3/4 < t < 1`, so the time switch is locally one; and
* spatial coordinate in `SpatialLocalization.plateau`, so the spatial
  localization/periodization is locally the identity,

the actual constructed force equals the incoming
`MixedPeriodicAssembly.originalResidual` exactly.

The result is independent of the future-side extension details.  It is the
intended P3 bridge for comparing paired strict-vs-doubling constructions on a
late-time physical region.
-/

noncomputable section

namespace NavierStokes.V511LateForceResidualBridge

open ProblemStatement Set Filter
open scoped Topology ContDiff

/-- On the late-time spatial plateau, the actual globally smooth force is
exactly the original mixed Navier--Stokes residual. -/
theorem force_eq_originalResidual_late_plateau
    {A v : VelocityField} {p : PressureField}
    (hu : ContDiffOn ℝ ∞ (MixedPeriodicAssembly.periodicVelocity A v)
      preSingularDomain)
    (hp : ContDiffOn ℝ ∞ (SpatialLocalization.periodicPressure p)
      preSingularDomain)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly
      (fun t x => iteratedFDeriv ℝ n
        (fun z => navierStokesResidual
          (MixedPeriodicAssembly.periodicVelocity A v)
          (SpatialLocalization.periodicPressure p) z.1 z.2)
        (t, x))
      (fun x => L x n) (𝓝[<] (1 : ℝ)))
    {t : ℝ} (ht : 3 / 4 < t) (ht1 : t < 1)
    {x : Space} (hx : x ∈ SpatialLocalization.plateau) :
    CandidateFromLimits.force
        (MixedPeriodicAssembly.periodicVelocity A v)
        (SpatialLocalization.periodicPressure p)
        hu hp L hlim (t, x) =
      MixedPeriodicAssembly.originalResidual A v p (t, x) := by
  rw [CandidateFromLimits.force_eq_activated_residual
    (MixedPeriodicAssembly.periodicVelocity A v)
    (SpatialLocalization.periodicPressure p)
    hu hp L hlim (by linarith) ht1 x]

  have htime :=
    ResidualRegularity.residual_eventuallyEq
      (TimeLocalization.activatedVelocity_eventuallyEq_late
        (MixedPeriodicAssembly.periodicVelocity A v) ht x)
      (TimeLocalization.activatedPressure_eventuallyEq_late
        (SpatialLocalization.periodicPressure p) ht x)

  have hspace :=
    ResidualRegularity.residual_eventuallyEq
      (MixedPeriodicAssembly.periodicVelocity_eventuallyEq A v hx)
      (SpatialLocalization.periodicPressure_eventuallyEq p hx)

  have hall := htime.trans hspace
  simpa only [MixedPeriodicAssembly.originalResidual] using hall.self_of_nhds

end NavierStokes.V511LateForceResidualBridge
