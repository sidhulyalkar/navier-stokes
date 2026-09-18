import NavierStokes.MixedCandidateAssembly
import NavierStokes.V510MixedStrictResidual

/-!
# v5.10: final singular candidate without factor-two schedule growth

This module replays the pinned `MixedCandidateAssembly.candidate_of_finite_stages`
proof while replacing only the source schedule selector by the qualified v5.10
strict-schedule / mixed-residual theorem.

The literal finite-stage potential, direct, and pressure families are unchanged.
The support hypotheses, away extensions, angular divergence theorem, origin
blowup theorem, mixed residual vanishing statement, and final
`MixedPeriodicAssembly.exists_candidate_force` constructor are unchanged.

The removed datum is only

  2 * a j ≤ a (j + 1).

This theorem does not compare the resulting forcing in any norm.
-/

noncomputable section

namespace NavierStokes.V510FinalStrictCandidate

open Set Filter ProblemStatement
open JointResidualLimits (OneSidedExtension)
open DiagonalResidual (JetRate)
open scoped Topology ContDiff

universe u

/-- `StageEstimates` produces the same smooth sums and vanishing mixed
residual using the v5.10 strict schedule, without returning factor-two
growth. -/
theorem stageEstimates_exists_strict_schedule {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : MixedCandidateAssembly.StageEstimates h qbig A B P)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig) (lower : ℕ) :
    ∃ a : ℕ → ℕ,
      lower ≤ a 0 ∧
      (∀ j, 0 < a j) ∧
      StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (a j : ℝ))
          (PhysicalWaveSum.physicalQ h) A B P) := by
  have hS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1
  obtain ⟨a, hal, hap, ham, hat, hrecip, _, hs, hz⟩ :=
    V510MixedStrictResidual.exists_physical_strict_schedule_residual_zero
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
  exact ⟨a, hal, hap, ham, hat, hrecip, hs, hz⟩

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W)
    {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- Exact final-candidate replay with the factor-two schedule certificate
removed.  Every downstream physical theorem is the same pinned source theorem
used by `MixedCandidateAssembly.candidate_of_finite_stages`. -/
theorem candidate_of_finite_stages_strict
    (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : MixedCandidateAssembly.StageEstimates F.data.h qbig
      (MixedCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig initial.field)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig (stages j).field)
    (hDirect : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig (LocalAngularDiagonal.rawSeries D j))
    (hpInitial : MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig pInitial)
    (hpStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig (pStages j))
    (eA : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension
        (MixedCandidateAssembly.potentialStages
          H v upper bandFloor initial stages j) x))
    (eB : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (LocalAngularDiagonal.rawSeries D j) x))
    (eP : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension
        (MixedCandidateAssembly.pressureStages
          H v upper bandFloor pInitial pStages j) x)) :
    candidateStatement := by
  let A := MixedCandidateAssembly.potentialStages
    H v upper bandFloor initial stages
  let B := LocalAngularDiagonal.rawSeries D
  let P := MixedCandidateAssembly.pressureStages
    H v upper bandFloor pInitial pStages

  obtain ⟨a, _, hap, ham, hat, hgap, hs, hz⟩ :=
    stageEstimates_exists_strict_schedule
      E F.data.h_pos F.data.h_lt_half hqbig 1

  let ar : ℕ → ℝ := fun j => (a j : ℝ)
  have ha0 : 0 < ar 0 := by
    dsimp [ar]
    exact_mod_cast hap 0
  have hamin (j : ℕ) : ar 0 ≤ ar j := by
    dsimp [ar]
    exact_mod_cast ham.monotone (Nat.zero_le j)

  have hA0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (A 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension
      F.data.h_pos F.data.h_lt_half hqbig
      hInitial hx hxz
      (Classical.choice
        (TailGaugePotential.finalPotential_awayExtensions
          H v upper bandFloor x hx))

  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (P 0) x) := by
    intro x hx hxz
    have h := MixedDiagonalExtensions.initial_add_extension
      F.data.h_pos F.data.h_lt_half hqbig
      hpInitial hx hxz
      (Classical.choice
        ((SlowBaseEndpoint.final_fields_awayExtensions
          H v upper bandFloor).2 x hx))
    simp only [P]
    exact h

  have hB0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (B 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.extension_of_eventually_zero
      ((hDirect 0).eventually_zero
        F.data.h_pos F.data.h_lt_half hqbig hx hxz)

  have hAsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport
        F.data.h C qbig (A j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j

  have hPsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport
        F.data.h C qbig (P j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j =>
        simpa only [P, MixedCandidateAssembly.pressureStages_succ]
          using hpStages j

  have ea := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig
    hat ha0 hamin (hgap 0) hAsupport hA0 eA
  have eb := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig
    hat ha0 hamin (hgap 0)
    (fun j _ => hDirect j) hB0 eB
  have ep := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig
    hat ha0 hamin (hgap 0) hPsupport hP0 eP

  have hcut := LocalAngularDiagonal.spatialCut_angularSum_divergence
    F.data.h_pos F.data.h_lt_half D hat ha0 hamin (hgap 0)

  have haxis := MixedAxisPreservation.local_initialized_final_origin_blowup
    H v upper bandFloor hqbig initial stages
      (LocalAngularDiagonal.angularSupport D) hat

  obtain ⟨forcing, hc, _, _⟩ := MixedPeriodicAssembly.exists_candidate_force
    (A := SolenoidalDiagonal.potentialSum
      ar (PhysicalWaveSum.physicalQ F.data.h) A)
    (v := SolenoidalDiagonal.potentialSum
      ar (PhysicalWaveSum.physicalQ F.data.h) B)
    (p := SolenoidalDiagonal.potentialSum
      ar (PhysicalWaveSum.physicalQ F.data.h) P)
    (hs.potential.mono (fun _ hx => hx.1))
    (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1))
    hcut hz ea eb ep haxis

  exact ⟨_, _, forcing, hc⟩

end ActualBase

end NavierStokes.V510FinalStrictCandidate
