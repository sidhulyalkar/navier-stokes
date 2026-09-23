import NavierStokes.GermCandidateAssembly

/-!
# v5.16: axis-germ realization of floor-separated schedules

The stage-zero isolation idea becomes substantially stronger on the physical
axis. Positive potential increments in the pinned construction vanish on a
neighborhood of every axis point, while every direct angular diagonal vanishes
at the axis itself.

Consequently, if one schedule places its zeroth cutoff strictly inside the
constant-one plateau and a second schedule places the same zeroth field
strictly outside cutoff support, then at that axis point:

* the first mixed velocity is exactly the curl of the base potential;
* the second mixed velocity is exactly zero.

This is a velocity-level separation. It avoids any nonvanishing claim for a
later correction cycle.
-/

noncomputable section

namespace NavierStokes.V516AxisFloorSeparation

open Set Filter ProblemStatement
open scoped Topology ContDiff

/-- If all positive stages have zero germs and the zeroth cutoff is strictly
outside its support, then the whole potential diagonal has zero germ. -/
theorem potentialSum_eq_zero_germ
    {scales : ℕ → ℝ} (hscales : Tendsto scales atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {w : SpaceTime}
    (hq : ContinuousAt q w) (hpos : 0 < q w)
    (hzero : ∀ j : ℕ, j ≠ 0 → A j =ᶠ[𝓝 w] fun _ => 0)
    (hlarge : 1 < |scales 0 * q w|) :
    SolenoidalDiagonal.potentialSum scales q A =ᶠ[𝓝 w] fun _ => 0 := by
  have hfirst :=
    AxisPreservation.potentialSum_eq_first_near hscales hq hpos hzero
  have hcut :=
    (SmoothCutoffs.scaledCutoff_eventually_zero hlarge).comp_tendsto hq
  apply hfirst.trans
  filter_upwards [hcut] with y hy
  change SmoothCutoffs.scaledCutoff (scales 0) (q y) = 0 at hy
  simp only [SolenoidalDiagonal.cutStage, hy, zero_smul]

/-- The corresponding velocity sum is exactly zero at the comparison point. -/
theorem velocitySum_eq_zero
    {scales : ℕ → ℝ} (hscales : Tendsto scales atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {w : SpaceTime}
    (hq : ContinuousAt q w) (hpos : 0 < q w)
    (hzero : ∀ j : ℕ, j ≠ 0 → A j =ᶠ[𝓝 w] fun _ => 0)
    (hlarge : 1 < |scales 0 * q w|) :
    SolenoidalDiagonal.velocitySum scales q A w = 0 := by
  have hz := potentialSum_eq_zero_germ hscales hq hpos hzero hlarge
  exact SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq hz

/-- Two floor-separated schedules give exact mixed-velocity values at an axis
point. The first sees only the base curl; the second sees zero. -/
theorem mixedVelocity_axis_floor_separated
    {h qbig : ℝ}
    {base initial : VelocityField} {stages : ℕ → VelocityField}
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain h qbig))
    {q : SpaceTime → ℝ} {t : ℝ}
    {small large : ℕ → ℝ}
    (hsmallTop : Tendsto small atTop atTop)
    (hlargeTop : Tendsto large atTop atTop)
    (hq : ContinuousAt q (t, 0))
    (hpos : 0 < q (t, 0))
    (hInitial : initial =ᶠ[𝓝 (t, 0)] fun _ => 0)
    (hStages : ∀ j, stages j =ᶠ[𝓝 (t, 0)] fun _ => 0)
    (hsmall : |small 0 * q (t, 0)| < 1 / 2)
    (hlarge : 1 < |large 0 * q (t, 0)|) :
    MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum small q
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum small q
          (LocalAngularDiagonal.rawSeries D)) (t, 0) =
        SpatialCurl.spatialCurl base (t, 0) ∧
      MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum large q
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum large q
          (LocalAngularDiagonal.rawSeries D)) (t, 0) = 0 := by
  have htail :
      ∀ j : ℕ, j ≠ 0 →
        GermCandidateAssembly.initializedSeries base initial stages j
          =ᶠ[𝓝 (t, 0)] fun _ => 0 := by
    intro j hj
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j

  have hsmallPot :
      SolenoidalDiagonal.velocitySum small q
        (GermCandidateAssembly.initializedSeries base initial stages) (t, 0) =
        SpatialCurl.spatialCurl
          (GermCandidateAssembly.initializedSeries base initial stages 0) (t, 0) :=
    AxisPreservation.velocitySum_eq_first
      hsmallTop hq hpos htail hsmall

  have hzeroInitial :
      GermCandidateAssembly.initializedSeries base initial stages 0
        =ᶠ[𝓝 (t, 0)] base := by
    filter_upwards [hInitial] with y hy
    simp only [GermCandidateAssembly.initializedSeries_zero, hy, add_zero]
  have hsmallBase :
      SolenoidalDiagonal.velocitySum small q
        (GermCandidateAssembly.initializedSeries base initial stages) (t, 0) =
        SpatialCurl.spatialCurl base (t, 0) := by
    rw [hsmallPot]
    exact SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq hzeroInitial

  have hlargePot :
      SolenoidalDiagonal.velocitySum large q
        (GermCandidateAssembly.initializedSeries base initial stages) (t, 0) = 0 :=
    velocitySum_eq_zero hlargeTop hq hpos htail hlarge

  have hsmallDirect :
      SolenoidalDiagonal.potentialSum small q
        (LocalAngularDiagonal.rawSeries D) (t, 0) = 0 :=
    DirectAngularDiagonal.angularSum_axis small q
      (fun j => (D j).scalar) t 0 rfl rfl
  have hlargeDirect :
      SolenoidalDiagonal.potentialSum large q
        (LocalAngularDiagonal.rawSeries D) (t, 0) = 0 :=
    DirectAngularDiagonal.angularSum_axis large q
      (fun j => (D j).scalar) t 0 rfl rfl

  constructor
  · change
      SolenoidalDiagonal.velocitySum small q
          (GermCandidateAssembly.initializedSeries base initial stages) (t, 0) +
        SolenoidalDiagonal.potentialSum small q
          (LocalAngularDiagonal.rawSeries D) (t, 0) =
        SpatialCurl.spatialCurl base (t, 0)
    rw [hsmallBase, hsmallDirect, add_zero]
  · change
      SolenoidalDiagonal.velocitySum large q
          (GermCandidateAssembly.initializedSeries base initial stages) (t, 0) +
        SolenoidalDiagonal.potentialSum large q
          (LocalAngularDiagonal.rawSeries D) (t, 0) = 0
    rw [hlargePot, hlargeDirect, add_zero]

/-- A nonzero base velocity therefore produces an exact separation of the two
assembled mixed velocities at the same axis point. -/
theorem mixedVelocity_axis_ne_of_base_ne
    {h qbig : ℝ}
    {base initial : VelocityField} {stages : ℕ → VelocityField}
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain h qbig))
    {q : SpaceTime → ℝ} {t : ℝ}
    {small large : ℕ → ℝ}
    (hsmallTop : Tendsto small atTop atTop)
    (hlargeTop : Tendsto large atTop atTop)
    (hq : ContinuousAt q (t, 0))
    (hpos : 0 < q (t, 0))
    (hInitial : initial =ᶠ[𝓝 (t, 0)] fun _ => 0)
    (hStages : ∀ j, stages j =ᶠ[𝓝 (t, 0)] fun _ => 0)
    (hsmall : |small 0 * q (t, 0)| < 1 / 2)
    (hlarge : 1 < |large 0 * q (t, 0)|)
    (hbase : SpatialCurl.spatialCurl base (t, 0) ≠ 0) :
    MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum small q
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum small q
          (LocalAngularDiagonal.rawSeries D)) (t, 0) ≠
      MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum large q
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum large q
          (LocalAngularDiagonal.rawSeries D)) (t, 0) := by
  obtain ⟨hs, hl⟩ :=
    mixedVelocity_axis_floor_separated D hsmallTop hlargeTop hq hpos
      hInitial hStages hsmall hlarge
  rw [hs, hl]
  exact hbase

/-- Physical-axis specialization.  The comparison point is explicit:
`q★ = (2/5)/small(0)` and `t★ = 1-q★`.  The pinned identity
`physicalQ(t,0)=1-t` realizes exactly that scale. -/
theorem physical_axis_floor_separated
    {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {base initial : VelocityField} {stages : ℕ → VelocityField}
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain h qbig))
    {small large : ℕ → ℝ}
    (hsmallTop : Tendsto small atTop atTop)
    (hlargeTop : Tendsto large atTop atTop)
    (hsmall0 : 0 < small 0)
    (hRatio : 5 * small 0 < 2 * large 0)
    (hqbig : (2 / 5 : ℝ) / small 0 < qbig)
    (hInitialAxis :
      GermCandidateAssembly.AxisZeroOn
        (MixedAxisPreservation.localDomain h qbig) initial)
    (hStagesAxis : ∀ j,
      GermCandidateAssembly.AxisZeroOn
        (MixedAxisPreservation.localDomain h qbig) (stages j)) :
    let qStar : ℝ := (2 / 5 : ℝ) / small 0
    let tStar : ℝ := 1 - qStar
    MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum small (PhysicalWaveSum.physicalQ h)
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum small (PhysicalWaveSum.physicalQ h)
          (LocalAngularDiagonal.rawSeries D)) (tStar, 0) =
        SpatialCurl.spatialCurl base (tStar, 0) ∧
      MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum large (PhysicalWaveSum.physicalQ h)
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum large (PhysicalWaveSum.physicalQ h)
          (LocalAngularDiagonal.rawSeries D)) (tStar, 0) = 0 := by
  dsimp only
  let qStar : ℝ := (2 / 5 : ℝ) / small 0
  let tStar : ℝ := 1 - qStar
  have hqStar : 0 < qStar := by
    dsimp [qStar]
    positivity
  have htStar : tStar < 1 := by
    dsimp [tStar]
    linarith
  have hqAxis :
      PhysicalWaveSum.physicalQ h (tStar, 0) = qStar := by
    rw [AxisPreservation.physicalQ_origin hh hh1 htStar]
    dsimp [tStar]
    ring
  have hw :
      (tStar, (0 : Space)) ∈ MixedAxisPreservation.localDomain h qbig := by
    exact ⟨htStar, by rw [hqAxis]; exact hqbig⟩
  have haxis :
      PhysicalGraphBounds.radialProjection (tStar, (0 : Space)) = 0 :=
    MixedAxisPreservation.radialProjection_origin tStar
  have hInitial := hInitialAxis (tStar, 0) hw haxis
  have hStages : ∀ j, stages j =ᶠ[𝓝 (tStar, 0)] fun _ => 0 :=
    fun j => hStagesAxis j (tStar, 0) hw haxis
  have hqcont :
      ContinuousAt (PhysicalWaveSum.physicalQ h) (tStar, 0) :=
    (PhysicalWaveSum.physicalQ_smoothAt hh hh1 htStar).continuousAt
  have hqpos : 0 < PhysicalWaveSum.physicalQ h (tStar, 0) := by
    rw [hqAxis]
    exact hqStar

  have hsProd : small 0 * qStar = 2 / 5 := by
    dsimp [qStar]
    field_simp [ne_of_gt hsmall0]
  have hsmallCut :
      |small 0 * PhysicalWaveSum.physicalQ h (tStar, 0)| < 1 / 2 := by
    rw [hqAxis, hsProd, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5)]
    norm_num

  have hlargePos : 0 < large 0 := by
    have hs5 : 0 < 5 * small 0 := mul_pos (by norm_num) hsmall0
    nlinarith
  have hlargeProd :
      1 < large 0 * qStar := by
    have heq :
        large 0 * qStar = (2 * large 0) / (5 * small 0) := by
      dsimp [qStar]
      field_simp [ne_of_gt hsmall0]
      <;> ring
    rw [heq]
    apply (lt_div_iff₀ (mul_pos (by norm_num) hsmall0)).2
    simpa only [one_mul] using hRatio
  have hlargeCut :
      1 < |large 0 * PhysicalWaveSum.physicalQ h (tStar, 0)| := by
    rw [hqAxis, abs_of_pos]
    · exact hlargeProd
    · exact mul_pos hlargePos hqStar

  exact mixedVelocity_axis_floor_separated D
    hsmallTop hlargeTop hqcont hqpos hInitial hStages hsmallCut hlargeCut

/-- At the same explicit physical point, nonzero anchored base velocity gives
an unconditional assembled-velocity distinction between the two schedules. -/
theorem physical_axis_velocity_ne_of_base_ne
    {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {base initial : VelocityField} {stages : ℕ → VelocityField}
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain h qbig))
    {small large : ℕ → ℝ}
    (hsmallTop : Tendsto small atTop atTop)
    (hlargeTop : Tendsto large atTop atTop)
    (hsmall0 : 0 < small 0)
    (hRatio : 5 * small 0 < 2 * large 0)
    (hqbig : (2 / 5 : ℝ) / small 0 < qbig)
    (hInitialAxis :
      GermCandidateAssembly.AxisZeroOn
        (MixedAxisPreservation.localDomain h qbig) initial)
    (hStagesAxis : ∀ j,
      GermCandidateAssembly.AxisZeroOn
        (MixedAxisPreservation.localDomain h qbig) (stages j))
    (hbase :
      let tStar : ℝ := 1 - (2 / 5 : ℝ) / small 0
      SpatialCurl.spatialCurl base (tStar, 0) ≠ 0) :
    let tStar : ℝ := 1 - (2 / 5 : ℝ) / small 0
    MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum small (PhysicalWaveSum.physicalQ h)
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum small (PhysicalWaveSum.physicalQ h)
          (LocalAngularDiagonal.rawSeries D)) (tStar, 0) ≠
      MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum large (PhysicalWaveSum.physicalQ h)
          (GermCandidateAssembly.initializedSeries base initial stages))
        (SolenoidalDiagonal.potentialSum large (PhysicalWaveSum.physicalQ h)
          (LocalAngularDiagonal.rawSeries D)) (tStar, 0) := by
  dsimp only at hbase ⊢
  obtain ⟨hs, hl⟩ :=
    physical_axis_floor_separated hh hh1 D hsmallTop hlargeTop hsmall0
      hRatio hqbig hInitialAxis hStagesAxis
  rw [hs, hl]
  exact hbase

/-- The anchored slow base is nonzero at every physical axis time before the
singular endpoint.  This follows from the pinned exact origin formula, not
merely from asymptotic blow-up. -/
theorem finalSlowBase_axis_ne_zero
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W)
    {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)
    (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) :
    FinalSlowBase.velocity H v upper B (t, 0) ≠ 0 := by
  rw [FinalSlowBase.origin H v upper B ht]
  have hpow :
      0 < (1 - t) ^ (-CoordinateAlgebra.A F.data.h) :=
    Real.rpow_pos_of_pos (sub_pos.mpr ht) _
  have hcoef :
      0 < (1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j :=
    mul_pos hpow W.axis.small.j_pos
  intro hz
  have hz2 := congrArg (fun y : ProblemStatement.Space => y 2) hz
  simp only [Pi.smul_apply, smul_eq_mul, ProblemStatement.coordinateVector,
    EuclideanSpace.single_apply, if_pos rfl, mul_one, PiLp.zero_apply] at hz2
  exact hcoef.ne' hz2

/-- The gauge-modified base potential therefore has nonzero curl at every
physical axis time before one. -/
theorem anchoredBase_axis_curl_ne_zero
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W)
    {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)
    (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) :
    SpatialCurl.spatialCurl
        (TailGaugePotential.finalPotential H v upper B) (t, 0) ≠ 0 := by
  rw [TailGaugePotential.finalPotential_sameCurl H v upper B ht]
  exact finalSlowBase_axis_ne_zero H v upper B ht

/-- The conditional base-nonvanishing premise in
`physical_axis_velocity_ne_of_base_ne` is automatic for the actual anchored
slow base. -/
theorem actualBase_physical_axis_velocity_ne
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W)
    {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)
    (upper : ℝ) (bandFloor : ℕ)
    {qbig : ℝ} (hh : 0 < F.data.h) (hh1 : F.data.h < 1 / 2)
    {initial : VelocityField} {stages : ℕ → VelocityField}
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    {small large : ℕ → ℝ}
    (hsmallTop : Tendsto small atTop atTop)
    (hlargeTop : Tendsto large atTop atTop)
    (hsmall0 : 0 < small 0)
    (hRatio : 5 * small 0 < 2 * large 0)
    (hqbig : (2 / 5 : ℝ) / small 0 < qbig)
    (hInitialAxis :
      GermCandidateAssembly.AxisZeroOn
        (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStagesAxis : ∀ j,
      GermCandidateAssembly.AxisZeroOn
        (MixedAxisPreservation.localDomain F.data.h qbig) (stages j)) :
    let tStar : ℝ := 1 - (2 / 5 : ℝ) / small 0
    MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum small
          (PhysicalWaveSum.physicalQ F.data.h)
          (GermCandidateAssembly.initializedSeries
            (TailGaugePotential.finalPotential H v upper bandFloor)
            initial stages))
        (SolenoidalDiagonal.potentialSum small
          (PhysicalWaveSum.physicalQ F.data.h)
          (LocalAngularDiagonal.rawSeries D)) (tStar, 0) ≠
      MixedPeriodicAssembly.velocity
        (SolenoidalDiagonal.potentialSum large
          (PhysicalWaveSum.physicalQ F.data.h)
          (GermCandidateAssembly.initializedSeries
            (TailGaugePotential.finalPotential H v upper bandFloor)
            initial stages))
        (SolenoidalDiagonal.potentialSum large
          (PhysicalWaveSum.physicalQ F.data.h)
          (LocalAngularDiagonal.rawSeries D)) (tStar, 0) := by
  dsimp only
  apply physical_axis_velocity_ne_of_base_ne
    hh hh1 D hsmallTop hlargeTop hsmall0 hRatio hqbig
    hInitialAxis hStagesAxis
  have hqStar : 0 < (2 / 5 : ℝ) / small 0 := by positivity
  apply anchoredBase_axis_curl_ne_zero H v upper bandFloor
  linarith

end NavierStokes.V516AxisFloorSeparation
