import NavierStokes.PrimaryTargetBounds

/-!
# v5.14: nonvanishing of the literal leading target on the active annulus

The paired cutoff geometry already gives an explicit radius where the strict
schedule is on its plateau and the doubling schedule is zero.  To turn that
scalar separation into physical separation we need a genuine nonzero source
observable.

This module records the first source-native rung of that argument.  On every
positive-time point whose normalized radial coordinate lies in the open active
annulus, the literal spectral stress vector is nonzero, and hence the actual
primary covariance target is nonzero.

No statement about the full positive-stage sum is made here.  Cancellation
between particular, signed, and mean pieces remains a separate obligation.
-/

noncomputable section

namespace NavierStokes.V514TargetNonvanishing

open Set Function
open scoped Topology ContDiff

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W)
  {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The Euclidean stress vector cannot vanish in the literal open active
annulus.  This is extracted from the source's nonvanishing leading-stress
theorem without introducing a new analytic assumption. -/
theorem stressVector_ne_zero
    (hcone : LeadingStressWeights.FullTrueCone v)
    {p : PhaseCalculus.Slow} (hT : 0 < p.2.2)
    (hX : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    ProfileSpectralCone.stressVector v.profiles F.data.h
      (BaseChartJets.normalizedCoordinates F.data.h p).2 ≠ 0 := by
  let w := (BaseChartJets.normalizedCoordinates F.data.h p).2
  have heta :=
    (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half hT).le
  have hw : w ∈ FinalSlowBase.annulus W := by
    exact ⟨hX, abs_le.mp heta⟩
  have hlead : FinalSlowBase.leadingStress v w ≠ 0 :=
    FinalSlowBase.leading_ne_zero v hcone hw
  intro hz
  apply hlead
  apply norm_eq_zero.mp
  have hb := PrimaryTargetBounds.stress_norm_le_plane v w
  rw [hz, norm_zero] at hb
  exact le_antisymm hb (norm_nonneg _)

/-- The literal primary covariance target is nonzero at every positive-time
point in the open active annulus.  The only additional factor is a strictly
positive real power of the normalized similarity coordinate. -/
theorem actualTarget_ne_zero
    (hcone : LeadingStressWeights.FullTrueCone v)
    {p : PhaseCalculus.Slow} (hT : 0 < p.2.2)
    (hX : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    PrimaryTargetBounds.actualTarget v p ≠ 0 := by
  have hq :=
    BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half hT
  have hs := stressVector_ne_zero H v hcone hT hX
  intro hz
  unfold PrimaryTargetBounds.actualTarget at hz
  have hscalar :
      (BaseChartJets.normalizedCoordinates F.data.h p).1 ^
          (-CoordinateAlgebra.A F.data.h - 1 / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hq _).ne'
  exact hs ((smul_eq_zero.mp hz).resolve_left hscalar)

end NavierStokes.V514TargetNonvanishing
