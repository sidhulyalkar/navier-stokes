import NavierStokes.BasePhaseGeometry
import NavierStokes.TangentODE

/-!
# v5.6 source-locked enlarged-primary interval audit

This file is compiled against the pinned OpenAI source revision.  It proves
only the interval wrappers needed for the first one-sided continuation
experiment.  It does not construct an unforced Navier-Stokes solution.
-/

noncomputable section

namespace NavierStokes.BasePhaseGeometry

open Set Filter
open scoped Topology ContDiff InnerProductSpace

namespace FamilyData

variable {ι : Type*} {D : PhaseJetBounds.Domain ι Slow} {h r0 u M : ℝ}
variable (a : FamilyData D h r0 u M)

/-- The first one-sided audit interval stays strictly inside the source's
larger analysis slot `(-L,2L)`. -/
theorem interval_three_halves_subset_slot (hr : 0 < r0) (i : ι) :
    Icc 0 (3 * a.length i / 2) ⊆ a.slot i := by
  intro v hv
  have hL := a.length_pos hr i
  change -a.length i < v ∧ v < 2 * a.length i
  constructor <;> nlinarith [hv.1, hv.2]

/-- `coefficient_jets` is already proved on the open source slot.  The
published `PrimaryTargetBounds.coefficient_continuous` wrapper restricts it to
`[0,L]`; this audit restricts the same source theorem to `[0,3L/2]`. -/
theorem coefficient_continuous_three_halves
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i)) (i : ι) :
    ContinuousOn ((a.frame i).coefficient 1)
      (D.carrier i ×ˢ Icc 0 (3 * a.length i / 2)) :=
  ((a.coefficient_jets hh hr hM hu huM hL hslot hlarge 1).smooth i).continuousOn.mono
    (fun _ hz => ⟨hz.1, a.interval_three_halves_subset_slot hr i hz.2⟩)

/-- The source proof of `FamilyData.kinematics` only uses its `[0,L]`
restriction to invoke `normal_nonzero`, which is itself valid on the larger
open slot.  Replacing that inclusion gives the same kinematics on
`[0,3L/2]`. -/
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
      (a.interval_three_halves_subset_slot hr i hv)).2
  · intro v _
    exact mul_ne_zero (a.ratio_ne hM i)
      (by positivity : Real.sqrt (1 + PulseGrowth.slotMagnitude u (a.length i) v ^ 2) ≠ 0)
  · intro v _
    exact PrimaryODE.hasDerivAt_referenceProfile (a.c0 i) u (a.length i) v

end FamilyData
end NavierStokes.BasePhaseGeometry
