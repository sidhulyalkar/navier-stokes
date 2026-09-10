import NavierStokes.BasePhaseGeometry
import NavierStokes.PrimaryODE

/-!
# v5.6 source-locked enlarged-primary interval audit

Stage A proves only the minimum wrapper needed to construct a longer modal
primary: the candidate interval lies inside the source analysis slot and the
modal coefficient is continuous there. Ambient kinematics is deliberately a
later theorem so proof failures stay localized.

No statement in this file claims an unforced Navier-Stokes solution.
-/

noncomputable section

namespace NavierStokes.BasePhaseGeometry

open Set Filter
open scoped Topology ContDiff InnerProductSpace

namespace FamilyData

variable {ι : Type*} {D : PhaseJetBounds.Domain ι Slow} {h r0 u M : ℝ}
variable (a : FamilyData D h r0 u M)

/-- The one-sided audit interval `[0,3L/2]` stays strictly inside the source
analysis slot `(-L,2L)`. -/
theorem interval_three_halves_subset_slot (hr : 0 < r0) (i : ι) :
    Icc 0 (3 * a.length i / 2) ⊆ a.slot i := by
  intro v hv
  have hL := a.length_pos hr i
  change -a.length i < v ∧ v < 2 * a.length i
  constructor <;> nlinarith [hv.1, hv.2]

/-- `coefficient_jets` is already proved on the open source slot. This is the
compact restriction required by `PrimaryODE.primary_hasDerivAt` on the longer
modal interval. -/
theorem coefficient_continuous_three_halves
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i)) (i : ι) :
    ContinuousOn ((a.frame i).coefficient 1)
      (D.carrier i ×ˢ Icc 0 (3 * a.length i / 2)) :=
  ((a.coefficient_jets hh hr hM hu huM hL hslot hlarge 1).smooth i).continuousOn.mono
    (fun _ hz => ⟨hz.1, a.interval_three_halves_subset_slot hr i hz.2⟩)

end FamilyData
end NavierStokes.BasePhaseGeometry
