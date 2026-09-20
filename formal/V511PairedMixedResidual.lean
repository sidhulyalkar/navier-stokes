import NavierStokes.MixedDiagonalResidual
import NavierStokes.V511PairedMixedSchedule

/-!
# v5.11: paired mixed residual vanishing

The strict and doubling schedules are selected together from identical
finite-stage fields and identical aggregated cutoff data by
`V511PairedMixedSchedule`.

This module pushes both schedules through the same pinned
`MixedDiagonalResidual.physical_vanishingJointJets` theorem.  The finite
background and finite residual rates are supplied once and reused for both
schedules.  Thus no second existential stage construction or independent
constant selection is introduced.

The theorem proves that both paired mixed residuals have vanishing joint jets
at the singular endpoint while retaining stage-zero equality, stage-one strict
separation, and pointwise schedule order.

This is a paired residual construction result.  It does not order either
residual or the final force in a norm.
-/

noncomputable section

namespace NavierStokes.V511PairedMixedResidual

open ProblemStatement Set Filter
open DiagonalResidual (JetRate)
open scoped Topology ContDiff

/-- The same finite-stage data produce two endpoint-flat mixed residuals whose
only schedule-level difference is minimal strict versus factor-two recursion. -/
theorem exists_physical_paired_schedule_residual_zero {h qbig : ℝ}
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
    (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
    (rawA : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) A g LA CA pA
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawB : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) B g LB CB pB
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawP : CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) P g LP CP pP
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (hg0 : 0 ≤ g 0) (hg : ∀ j, 1 ≤ j → 0 < g j)
    (hgmono : Monotone g) (hgtop : Tendsto g atTop atTop)
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
    (lower : ℕ) :
    ∃ aStrict aDouble : ℕ → ℕ,
      lower ≤ aStrict 0 ∧
      lower ≤ aDouble 0 ∧
      (∀ j, 0 < aStrict j) ∧
      (∀ j, 0 < aDouble j) ∧
      StrictMono aStrict ∧
      StrictMono aDouble ∧
      Tendsto (fun j => (aStrict j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aDouble j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aDouble j ≤ aDouble (j + 1)) ∧
      (∀ j, 1 / (aStrict j : ℝ) < qbig) ∧
      (∀ j, 1 / (aDouble j : ℝ) < qbig) ∧
      aStrict 0 = aDouble 0 ∧
      aStrict 1 < aDouble 1 ∧
      (∀ j, aStrict j ≤ aDouble j) ∧
      MixedDiagonalSchedule.ThreeCutBounds aStrict h A B P
        (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums aStrict h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (aStrict j : ℝ))
          (PhysicalWaveSum.physicalQ h) A B P) ∧
      MixedDiagonalSchedule.ThreeCutBounds aDouble h A B P
        (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums aDouble h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (aDouble j : ℝ))
          (PhysicalWaveSum.physicalQ h) A B P) := by
  obtain ⟨aStrict, aDouble,
      hsLower, hdLower,
      hsPos, hdPos,
      hsMono, hdMono,
      hsTop, hdTop,
      hdGrowth,
      hsRecip, hdRecip,
      hEq0, hLt1, hOrder,
      hsCut, hsSmooth,
      hdCut, hdSmooth⟩ :=
    V511PairedMixedSchedule.exists_three_component_local_paired_schedule
      hh hh1 hqbig hS hA hB hP
      g LA LB LP CA CB CP pA pB pP
      rawA rawB rawP hg lower

  let U := S ∩ CutStageEstimates.physicalSublevel h qbig
  have hU : IsOpen U :=
    hSopen.inter (CutStageEstimates.physicalSublevel_open hh hh1 qbig)
  have hUp : U ⊆ PhysicalWaveSum.preterminal := fun _ hx => hS hx.1
  have hqzero := AnnularEndpoint.physicalQ_tendsto_zero hh hh1
    (x := (0 : Space)) rfl
  have hlU :
      ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ U := by
    filter_upwards [hlS, hqzero.eventually (gt_mem_nhds hqbig)] with z hz hqz
    exact ⟨hz, hS hz, hqz⟩
  have hlq :
      ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
        0 < PhysicalWaveSum.physicalQ h z ∧
          PhysicalWaveSum.physicalQ h z ≤ 1 := by
    filter_upwards [hlS,
      hqzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with z hz hqz
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

  have vanishOne :
      ∀ (a : ℕ → ℕ),
        Tendsto (fun j => (a j : ℝ)) atTop atTop →
        MixedDiagonalSchedule.ThreeCutBounds a h A B P
          (fun j => g j / 2)
          (MixedDiagonalSchedule.commonLoss LA LB LP) S →
        JointResidualLimits.VanishingJointJets
          (MixedDiagonalResidual.residual (fun j => (a j : ℝ))
            (PhysicalWaveSum.physicalQ h) A B P) := by
    intro a hat hb
    apply MixedDiagonalResidual.physical_vanishingJointJets
      (Lbg := Lbg) (Lres := Lres)
      hh hh1 hat hU hUp hlU
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

  have hsZero := vanishOne aStrict hsTop hsCut
  have hdZero := vanishOne aDouble hdTop hdCut

  exact ⟨aStrict, aDouble,
    hsLower, hdLower, hsPos, hdPos, hsMono, hdMono,
    hsTop, hdTop, hdGrowth, hsRecip, hdRecip,
    hEq0, hLt1, hOrder,
    hsCut, hsSmooth, hsZero,
    hdCut, hdSmooth, hdZero⟩

end NavierStokes.V511PairedMixedResidual
