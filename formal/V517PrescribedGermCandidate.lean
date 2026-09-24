import NavierStokes.GermCandidateAssembly

/-!
# v5.17: realized force witness from a prescribed selected schedule

This is the schedule-retaining form of the post-selection half of
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages`.

The initial and positive potential stages are already realized velocity fields,
matching `ActualCandidateAssembly`.  Given a pinned `SelectedSchedule`,
the source-native away extensions, angular divergence, origin blow-up and force
construction are replayed unchanged.
-/

noncomputable section

namespace NavierStokes.V517PrescribedGermCandidate

open Set Filter ProblemStatement MixedCandidateAssembly
open JointResidualLimits (OneSidedExtension)
open scoped Topology ContDiff

theorem exists_force_of_selected_schedule
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W)
    {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)
    (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig initial)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig (stages j))
    (hDirect : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig (LocalAngularDiagonal.rawSeries D j))
    (hpInitial : MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig pInitial)
    (hpStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport
      F.data.h C qbig (pStages j))
    (eA : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension
        (GermCandidateAssembly.potentialStages
          H v upper bandFloor initial stages j) x))
    (eB : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (LocalAngularDiagonal.rawSeries D j) x))
    (eP : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension
        (MixedCandidateAssembly.pressureStages
          H v upper bandFloor pInitial pStages j) x))
    (hInitialAxis : GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStagesAxis : ∀ j, GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain F.data.h qbig) (stages j))
    (a : ℕ → ℕ)
    (ha : MixedCandidateWitness.SelectedSchedule F.data.h qbig
      (GermCandidateAssembly.potentialStages
        H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages
        H v upper bandFloor pInitial pStages) a) :
    let A := GermCandidateAssembly.potentialStages
      H v upper bandFloor initial stages
    let B := LocalAngularDiagonal.rawSeries D
    let P := MixedCandidateAssembly.pressureStages
      H v upper bandFloor pInitial pStages
    let ASum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ F.data.h) A
    let BSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ F.data.h) B
    let PSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ F.data.h) P
    ∃ forcing : VelocityField,
      CandidateProperties
        (TimeLocalization.activatedVelocity
          (MixedPeriodicAssembly.periodicVelocity ASum BSum))
        (TimeLocalization.activatedPressure
          (SpatialLocalization.periodicPressure PSum))
        forcing := by
  let A := GermCandidateAssembly.potentialStages
    H v upper bandFloor initial stages
  let B := LocalAngularDiagonal.rawSeries D
  let P := MixedCandidateAssembly.pressureStages
    H v upper bandFloor pInitial pStages
  let ar : ℕ → ℝ := fun j => (a j : ℝ)
  rcases ha with ⟨_, hap, _, ham, hat, hgap, hs, hz⟩

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
      F.data.h_pos F.data.h_lt_half hqbig hInitial hx hxz
      (Classical.choice
        (TailGaugePotential.finalPotential_awayExtensions
          H v upper bandFloor x hx))

  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (P 0) x) := by
    intro x hx hxz
    have h := MixedDiagonalExtensions.initial_add_extension
      F.data.h_pos F.data.h_lt_half hqbig hpInitial hx hxz
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
  have haxis := GermCandidateAssembly.origin_blowup
    H v upper bandFloor hqbig initial stages D
    hInitialAxis hStagesAxis hat

  obtain ⟨forcing, hc, _, _⟩ :=
    MixedPeriodicAssembly.exists_candidate_force
      (A := SolenoidalDiagonal.potentialSum ar
        (PhysicalWaveSum.physicalQ F.data.h) A)
      (v := SolenoidalDiagonal.potentialSum ar
        (PhysicalWaveSum.physicalQ F.data.h) B)
      (p := SolenoidalDiagonal.potentialSum ar
        (PhysicalWaveSum.physicalQ F.data.h) P)
      (hs.potential.mono (fun _ hx => hx.1))
      (hs.direct.mono (fun _ hx => hx.1))
      (hs.pressure.mono (fun _ hx => hx.1))
      hcut hz ea eb ep haxis
  exact ⟨forcing, hc⟩

end NavierStokes.V517PrescribedGermCandidate
