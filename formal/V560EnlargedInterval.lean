import NavierStokes.BasePhaseGeometry
import NavierStokes.PrimaryODE

/-!
# v5.6 source-locked enlarged-primary interval audit

Stage A proves the minimum wrapper needed to construct a longer modal primary:
the candidate interval lies inside the source analysis slot and the modal
coefficient is continuous there.

Stage B reuses the upstream `PrimaryODE.primary` constructor on `[0,3L/2]`,
proves the homogeneous modal ODE there, and proves agreement with the native
`[0,L]` primary by the upstream finite-interval uniqueness theorem.

Ambient kinematics and full Navier-Stokes residual closure are deliberately
later gates. No statement in this file claims an unforced Navier-Stokes
solution.
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

/-- The native interval is contained in the enlarged one-sided audit interval. -/
theorem interval_subset_three_halves (hr : 0 < r0) (i : ι) :
    Icc 0 (a.length i) ⊆ Icc 0 (3 * a.length i / 2) := by
  intro v hv
  have hL := a.length_pos hr i
  exact ⟨hv.1, by nlinarith [hv.2]⟩

/-- The enlarged right endpoint is a valid finite forward time. -/
theorem three_halves_nonneg (hr : 0 < r0) (i : ι) :
    0 ≤ 3 * a.length i / 2 := by
  have hL := a.length_pos hr i
  nlinarith

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

/-- The same upstream modal-primary constructor, now instantiated on
`[0,3L/2]` with the unchanged Gaussian reference envelope and t=0 seed. -/
noncomputable def primaryThreeHalves (hr : 0 < r0) (i : ι) (p : Slow) : ℝ → PrimaryODE.State :=
  PrimaryODE.primary (a.three_halves_nonneg hr i) (a.frame i)
    (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p

/-- The enlarged primary satisfies the same homogeneous modal ODE throughout
`[0,3L/2]`. This is a modal statement only; no ambient PDE claim is made. -/
theorem primaryThreeHalves_hasDerivAt
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i))
    (i : ι) {p : Slow} (hp : p ∈ D.carrier i) {v : ℝ}
    (hv : v ∈ Icc 0 (3 * a.length i / 2)) :
    HasDerivAt (a.primaryThreeHalves hr i p)
      ((a.frame i).coefficient 1 (p, v) (a.primaryThreeHalves hr i p v)) v := by
  unfold primaryThreeHalves
  exact PrimaryODE.primary_hasDerivAt (a.three_halves_nonneg hr i) (a.frame i)
    (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2)
    (a.coefficient_continuous_three_halves hh hr hM hu huM hL hslot hlarge i) hp hv

/-- The enlarged same-seed primary agrees exactly with the source-native
primary on the overlap `[0,L]`. Thus Stage B is a genuine continuation of the
canonical modal trajectory, rather than a nearby replacement. -/
theorem primaryThreeHalves_eq_native
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i))
    (i : ι) {p : Slow} (hp : p ∈ D.carrier i) :
    EqOn (a.primaryThreeHalves hr i p)
      (PrimaryODE.primary (a.length_pos hr i).le (a.frame i)
        (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p)
      (Icc 0 (a.length i)) := by
  have hA3 := a.coefficient_continuous_three_halves hh hr hM hu huM hL hslot hlarge i
  have hA0 : ContinuousOn ((a.frame i).coefficient 1)
      (D.carrier i ×ˢ Icc 0 (a.length i)) :=
    hA3.mono (Set.prod_mono Subset.rfl (a.interval_subset_three_halves hr i))
  have hAslice : ContinuousOn (fun v => (a.frame i).coefficient 1 (p, v))
      (Icc 0 (a.length i)) :=
    hA0.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hp, hv⟩)
  apply TangentODE.linear_solution_unique (a.length_pos hr i).le
    (fun v => (a.frame i).coefficient 1 (p, v)) (fun _ => 0) hAslice
  · intro v hv
    have h := a.primaryThreeHalves_hasDerivAt hh hr hM hu huM hL hslot hlarge i hp
      (a.interval_subset_three_halves hr i hv)
    simpa only [add_zero] using h
  · intro v hv
    have h := PrimaryODE.primary_hasDerivAt (a.length_pos hr i).le (a.frame i)
      (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) hA0 hp hv
    simpa only [add_zero] using h
  · simp only [primaryThreeHalves, PrimaryODE.primary_initial]

end FamilyData
end NavierStokes.BasePhaseGeometry
