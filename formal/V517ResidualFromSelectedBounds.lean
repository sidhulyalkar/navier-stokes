import NavierStokes.MixedDiagonalResidual

/-!
# v5.17: residual flatness from prescribed mixed cut bounds

The pinned source proves vanishing endpoint jets after internally selecting one
schedule.  The analytic part of that proof is actually schedule-agnostic:
once a prescribed real scale tends to infinity and the three literal field
families satisfy `ThreeCutBounds`, the same finite-background and
finite-residual estimates imply vanishing joint residual jets.

This module exposes that implication directly so a floor-separated pair of
admissible schedules can share the exact same raw finite-stage data.
-/

noncomputable section

namespace NavierStokes.V517ResidualFromSelectedBounds

open Set Filter ProblemStatement
open DiagonalResidual (JetRate)
open scoped Topology ContDiff

/-- The residual-flatness part of
`MixedDiagonalResidual.exists_physical_schedule_residual_zero`, with the
schedule supplied rather than selected internally. -/
theorem physical_vanishingJointJets_of_threeCutBounds
    {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hSopen : IsOpen S)
    (hS : S ⊆ PhysicalWaveSum.preterminal)
    (hlS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ S)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j)
      (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j)
      (CutStageEstimates.physicalSublevel h qbig))
    (g LA LB LP Lbg Lres : ℕ → ℝ)
    (hg0 : 0 ≤ g 0) (hgmono : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hbg : ∀ J m,
      JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
        (PhysicalWaveSum.physicalQ h)
        (MixedDiagonalResidual.uncutVelocity A B J) m (-Lbg m))
    (hres : ∀ J m,
      JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
        (PhysicalWaveSum.physicalQ h)
        (fun z => navierStokesResidual
          (MixedDiagonalResidual.uncutVelocity A B J)
          (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2)
        m (g J - Lres m))
    {a : ℕ → ℕ}
    (hatop : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    (hb : MixedDiagonalSchedule.ThreeCutBounds a h A B P
      (fun j => g j / 2)
      (MixedDiagonalSchedule.commonLoss LA LB LP) S) :
    JointResidualLimits.VanishingJointJets
      (MixedDiagonalResidual.residual (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ h) A B P) := by
  let U := S ∩ CutStageEstimates.physicalSublevel h qbig
  have hU : IsOpen U :=
    hSopen.inter (CutStageEstimates.physicalSublevel_open hh hh1 qbig)
  have hUp : U ⊆ PhysicalWaveSum.preterminal := fun _ hx => hS hx.1
  have hqzero :=
    AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  have hlU :
      ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ U := by
    filter_upwards [hlS, hqzero.eventually (gt_mem_nhds hqbig)] with z hz hqz
    exact ⟨hz, hS hz, hqz⟩
  have hlq :
      ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
        0 < PhysicalWaveSum.physicalQ h z ∧
          PhysicalWaveSum.physicalQ h z ≤ 1 := by
    filter_upwards
      [hlS, hqzero.eventually
        (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with z hz hqz
    exact ⟨PhysicalWaveSum.physicalQ_pos hh hh1 (hS hz), hqz.le⟩
  have hhalfmono : Monotone (fun j => g j / 2) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (hgmono hij) (by norm_num)
  have hhalftop : Tendsto (fun j => g j / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [hgtop.eventually (eventually_ge_atTop (2 * r))] with j hj
    linarith
  have hnonneg (J : ℕ) : 0 ≤ g J :=
    hg0.trans (hgmono (Nat.zero_le J))
  apply MixedDiagonalResidual.physical_vanishingJointJets
    (Lbg := Lbg) (Lres := Lres) hh hh1 hatop hU hUp hlU
    (fun j => (hA j).mono inter_subset_right)
    (fun j => (hB j).mono inter_subset_right)
    (fun j => (hP j).mono inter_subset_right)
    hhalfmono hhalftop
    (fun j hj m hm z hz => hb.potential j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.direct j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.pressure j hj m hm z hz.1)
    hbg
  intro J m
  exact (hres J m).weaken hlq (by linarith [hnonneg J])

end NavierStokes.V517ResidualFromSelectedBounds
