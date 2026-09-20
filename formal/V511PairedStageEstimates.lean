import NavierStokes.MixedCandidateAssembly
import NavierStokes.V511PairedMixedResidual

/-!
# v5.11: paired adapter for literal StageEstimates

The pinned final assembly consumes a
`MixedCandidateAssembly.StageEstimates h qbig A B P` object.  The generic
paired v5.11 theorems are useful only if they can be instantiated from that
literal record without rebuilding or changing any finite-stage data.

This module is the thin adapter.  It feeds the exact fields of one
`StageEstimates` object into the paired residual theorem, with
`S = PhysicalWaveSum.preterminal`.

Therefore both schedules use exactly the same:

* potential/direct/pressure stage families;
* gain and loss functions;
* raw constants and logarithmic powers;
* finite-background estimate; and
* finite-residual estimate.

The schedules agree at stage zero, differ strictly at stage one, and both have
smooth sums and endpoint-flat mixed residuals.  No residual or force norm
ordering is asserted.
-/

noncomputable section

namespace NavierStokes.V511PairedStageEstimates

open Set Filter ProblemStatement
open scoped Topology ContDiff

/-- One literal pinned `StageEstimates` record yields the controlled paired
strict-vs-doubling schedules and residuals. -/
theorem stageEstimates_exists_paired_schedule
    {h qbig : ℝ} {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : MixedCandidateAssembly.StageEstimates h qbig A B P)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig) (lower : ℕ) :
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
      MixedDiagonalSchedule.ThreeSmoothSums aStrict h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (aStrict j : ℝ))
          (PhysicalWaveSum.physicalQ h) A B P) ∧
      MixedDiagonalSchedule.ThreeSmoothSums aDouble h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (aDouble j : ℝ))
          (PhysicalWaveSum.physicalQ h) A B P) := by
  have hS :
      ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
        z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1

  obtain ⟨aStrict, aDouble,
      hsLower, hdLower,
      hsPos, hdPos,
      hsMono, hdMono,
      hsTop, hdTop,
      hdGrowth,
      hsRecip, hdRecip,
      hEq0, hLt1, hOrder,
      _, hsSmooth, hsZero,
      _, hdSmooth, hdZero⟩ :=
    V511PairedMixedResidual.exists_physical_paired_schedule_residual_zero
      hh hh1 hqbig
      PhysicalWaveSum.preterminal_open (Subset.refl _) hS
      E.potential_smooth E.direct_smooth E.pressure_smooth
      E.gain E.potentialLoss E.directLoss E.pressureLoss
      E.backgroundLoss E.residualLoss
      E.potentialConstant E.directConstant E.pressureConstant
      E.potentialLog E.directLog E.pressureLog
      E.potential_bound E.direct_bound E.pressure_bound
      E.gain_zero E.gain_pos E.gain_mono E.gain_top
      E.finite_background E.finite_residual lower

  exact ⟨aStrict, aDouble,
    hsLower, hdLower, hsPos, hdPos, hsMono, hdMono,
    hsTop, hdTop, hdGrowth, hsRecip, hdRecip,
    hEq0, hLt1, hOrder,
    hsSmooth, hsZero, hdSmooth, hdZero⟩

end NavierStokes.V511PairedStageEstimates
