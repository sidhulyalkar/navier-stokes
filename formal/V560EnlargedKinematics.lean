import NavierStokes.BasePhaseGeometry

/-!
# v5.6 enlarged ambient-frame kinematics

The pinned source's `FamilyData.kinematics` proof has four ingredients. Three
are global in slot time; the only interval-sensitive one is normal
nondegeneracy, already proved on the larger source slot `(-L,2L)`.

This file replays that proof on `[0,3L/2]`. It is a frame-kinematics statement,
not a Navier-Stokes residual or force-removal statement.
-/

noncomputable section

namespace NavierStokes.BasePhaseGeometry.FamilyData

open Set
open scoped Topology ContDiff InnerProductSpace

variable {ι : Type*} {D : PhaseJetBounds.Domain ι Slow} {h r0 u M : ℝ}
variable (a : FamilyData D h r0 u M)

/-- The enlarged interval sits inside the source's actual open analysis slot. -/
theorem interval_three_halves_subset_slot_kinematics (hr : 0 < r0) (i : ι) :
    Icc 0 (3 * a.length i / 2) ⊆ a.slot i := by
  intro v hv
  have hL := a.length_pos hr i
  change -a.length i < v ∧ v < 2 * a.length i
  constructor <;> nlinarith [hv.1, hv.2]

/-- The exact source frame kinematics persist on `[0,3L/2]`. -/
theorem kinematics_three_halves
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : |u| ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i))
    {q : Slow} (hq : q ∈ D.carrier i) :
    (a.frame i).Kinematics q (Icc 0 (3 * a.length i / 2)) := by
  apply PrimaryODE.FrameData.ofNormalLocal_kinematics
  · intro v _
    exact PhaseCalculus.hasDerivAt_phaseNormal_slot _ _ _ _ _ _ _ _ _
      (ChartScales.epsilon_pos h (a.band i)).ne'
      ((a.base i).actualF q (a.inside i hq))
      ((a.base i).actualG q (a.inside i hq))
  · intro v hv
    exact (a.normal_nonzero hh hr hM hu hL hslot i hn hq
      (a.interval_three_halves_subset_slot_kinematics hr i hv)).2
  · intro v _
    exact mul_ne_zero (a.ratio_ne hM i)
      (by positivity : Real.sqrt (1 + PulseGrowth.slotMagnitude u (a.length i) v ^ 2) ≠ 0)
  · intro v _
    exact PrimaryODE.hasDerivAt_referenceProfile (a.c0 i) u (a.length i) v

end NavierStokes.BasePhaseGeometry.FamilyData
