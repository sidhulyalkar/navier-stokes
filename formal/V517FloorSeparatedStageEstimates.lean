import NavierStokes.MixedCandidateAssembly
import NavierStokes.V517FloorSeparatedMixedResidual

/-!
# v5.17: StageEstimates adapter for floor-separated selected schedules

One literal pinned `MixedCandidateAssembly.StageEstimates` record now yields
two fully selected schedules over exactly the same stage families.  The only
numerical difference is the initial canonical floor B versus 3B.
-/

noncomputable section

namespace NavierStokes.V517FloorSeparatedStageEstimates

open Set Filter ProblemStatement
open scoped Topology ContDiff

theorem stageEstimates_exists_floor_separated_selected
    {h qbig : ℝ} {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : MixedCandidateAssembly.StageEstimates h qbig A B P)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig) (lower : ℕ) :
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      lower ≤ Bsmall ∧
      1 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) < qbig ∧
      MixedCandidateWitness.SelectedSchedule h qbig A B P aSmall ∧
      MixedCandidateWitness.SelectedSchedule h qbig A B P aLarge := by
  have hS :
      ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
        z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1

  exact
    V517FloorSeparatedMixedResidual.exists_floor_separated_selected_schedules
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

end NavierStokes.V517FloorSeparatedStageEstimates
