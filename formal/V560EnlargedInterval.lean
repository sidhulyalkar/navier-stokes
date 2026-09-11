import NavierStokes.BasePhaseGeometry
import NavierStokes.PrimaryODE

/-!
# v5.6 source-locked enlarged-primary interval audit

Stage A restricts the source's open-slot coefficient jets to `[0,3L/2]`.
Stage B reuses `PrimaryODE.primary` on that longer interval and proves exact
agreement with the native primary on `[0,L]` by finite-interval uniqueness.
Stage C extends the scalar spectral/Gaussian reference estimates and replays
`PrimaryODE.primary_bounds` under an explicit enlarged-gap cone condition.

Ambient kinematics and full Navier-Stokes residual closure remain later gates.
No statement here claims force removal or an unforced Navier-Stokes solution.
-/

noncomputable section

namespace NavierStokes.V560Audit

open Set

/-- On `[0,3*ell/2]` the native slot magnitude ranges from `u/2` to `2u`. -/
theorem slotMagnitude_mem_three_halves {u ell time : ℝ} (hu : 0 ≤ u) (hell : 0 < ell)
    (ht : time ∈ Icc 0 (3 * ell / 2)) :
    PulseGrowth.slotMagnitude u ell time ∈ Icc (u / 2) (2 * u) := by
  have hq0 : 0 ≤ u * time / ell := div_nonneg (mul_nonneg hu ht.1) hell.le
  have hm := mul_le_mul_of_nonneg_left ht.2 hu
  have hq1 : u * time / ell ≤ 3 * u / 2 := by
    apply (div_le_iff₀ hell).2
    nlinarith [hm]
  unfold PulseGrowth.slotMagnitude
  constructor <;> linarith

/-- The source reference-slope upper constant replayed on `s ∈ [u/2,2u]`. -/
noncomputable def referenceMaxSlopeThreeHalves (lam u : ℝ) : ℝ :=
  2 * lam * u + 4 * lam * u / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

theorem referenceMaxSlopeThreeHalves_pos {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    0 < referenceMaxSlopeThreeHalves lam u := by
  unfold referenceMaxSlopeThreeHalves
  exact add_pos (mul_pos (mul_pos (by norm_num) hlam) hu)
    (div_pos (mul_pos (mul_pos (by norm_num) hlam) hu)
      (PulseGrowth.dampingDenominator_pos u))

/-- Explicit reference-rate slope bounds on the enlarged magnitude interval. -/
theorem referenceSlope_bounds_three_halves {lam u s : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hs : s ∈ Icc (u / 2) (2 * u)) :
    -referenceMaxSlopeThreeHalves lam u ≤ GaussianEnvelope.referenceSlope lam u s ∧
      GaussianEnvelope.referenceSlope lam u s ≤ -GaussianEnvelope.referenceMinSlope lam u := by
  have hspos : 0 < s := by linarith [hs.1]
  have hn : 0 ≤ lam * s := le_of_lt (mul_pos hlam hspos)
  have hS : 1 ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hroot : 1 ≤ Real.sqrt (1 + s ^ 2) := Real.one_le_sqrt.2 hS
  have hden : 1 ≤ (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) :=
        mul_le_mul hS hroot (by norm_num) (le_of_lt (PulseGrowth.one_add_sq_pos s))
  have hfirst : lam * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) ≤ lam * s := by
    apply (div_le_iff₀ (PulseGrowth.dampingDenominator_pos s)).2
    nlinarith [mul_le_mul_of_nonneg_left hden hn]
  have hfirst0 : 0 ≤ lam * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) :=
    div_nonneg hn (PulseGrowth.dampingDenominator_pos s).le
  have hmul := mul_le_mul_of_nonneg_left hs.2 hlam.le
  have hfirstUpper : lam * s ≤ 2 * lam * u := by nlinarith [hmul]
  have hsecondUpper : 2 * lam * s / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) ≤
      4 * lam * u / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) := by
    apply (div_le_div_iff_of_pos_right (PulseGrowth.dampingDenominator_pos u)).2
    nlinarith [hmul]
  have hsecondLower : lam * u / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) ≤
      2 * lam * s / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) := by
    apply (div_le_div_iff_of_pos_right (PulseGrowth.dampingDenominator_pos u)).2
    nlinarith [hs.1]
  unfold GaussianEnvelope.referenceSlope referenceMaxSlopeThreeHalves
    GaussianEnvelope.referenceMinSlope
  rw [neg_mul, neg_div]
  constructor <;> linarith

/-- Slot-time derivative bounds for the exact source reference rate on `[0,3ell/2]`. -/
theorem referenceRate_deriv_bounds_three_halves {lam u ell time : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hell : 0 < ell)
    (ht : time ∈ Icc 0 (3 * ell / 2)) :
    -(u * referenceMaxSlopeThreeHalves lam u) / ell ≤
        deriv (GaussianEnvelope.referenceRate lam u ell) time ∧
      deriv (GaussianEnvelope.referenceRate lam u ell) time ≤
        -(u * GaussianEnvelope.referenceMinSlope lam u) / ell := by
  have hb := referenceSlope_bounds_three_halves hlam hu
    (slotMagnitude_mem_three_halves hu.le hell ht)
  have hpos : 0 ≤ u / ell := (div_pos hu hell).le
  rw [(GaussianEnvelope.hasDerivAt_referenceRate lam u ell time).deriv]
  constructor
  · convert! mul_le_mul_of_nonneg_right hb.1 hpos using 1
    ring
  · convert! mul_le_mul_of_nonneg_right hb.2 hpos using 1
    ring

/-- Explicit two-sided Gaussian bounds for the exact reference envelope on the
one-sided enlarged interval. The lower-decay constant is unchanged; only the
upper slope constant grows. -/
theorem reference_gaussian_bounds_three_halves {lam u ell time : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hell : 0 < ell)
    (ht : time ∈ Icc 0 (3 * ell / 2)) :
    Real.exp (-(u * referenceMaxSlopeThreeHalves lam u) * (time - ell / 2) ^ 2 / (2 * ell)) ≤
        GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u ell) (ell / 2) time ∧
      GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u ell) (ell / 2) time ≤
        Real.exp (-(u * GaussianEnvelope.referenceMinSlope lam u) *
          (time - ell / 2) ^ 2 / (2 * ell)) := by
  have hdiff : Differentiable ℝ (GaussianEnvelope.referenceRate lam u ell) :=
    fun x => (GaussianEnvelope.hasDerivAt_referenceRate lam u ell x).differentiableAt
  apply GaussianEnvelope.gaussian_envelope_bounds (convex_Icc (0 : ℝ) (3 * ell / 2))
    hdiff.continuous.continuousOn hdiff.differentiableOn
  · intro x hx
    exact referenceRate_deriv_bounds_three_halves hlam hu hell (interior_subset hx)
  · constructor <;> nlinarith
  · exact ht
  · exact PulseGrowth.netGrowth_slot_midpoint lam u ell hell.ne'

/-- Positive Gaussian constants independent of slot length for the 3/2 audit. -/
theorem reference_uniform_gaussian_bounds_three_halves {lam u : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ell : ℝ, 0 < ell →
      ∀ time ∈ Icc 0 (3 * ell / 2),
        Real.exp (-C * (time - ell / 2) ^ 2 / ell) ≤
            GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u ell) (ell / 2) time ∧
          GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u ell) (ell / 2) time ≤
            Real.exp (-c * (time - ell / 2) ^ 2 / ell) := by
  refine ⟨u * GaussianEnvelope.referenceMinSlope lam u / 2,
    u * referenceMaxSlopeThreeHalves lam u / 2,
    div_pos (mul_pos hu (GaussianEnvelope.referenceMinSlope_pos hlam hu)) (by norm_num),
    div_pos (mul_pos hu (referenceMaxSlopeThreeHalves_pos hlam hu)) (by norm_num), ?_⟩
  intro ell hell time ht
  have hmax : -(u * referenceMaxSlopeThreeHalves lam u / 2) *
      (time - ell / 2) ^ 2 / ell =
      -(u * referenceMaxSlopeThreeHalves lam u) * (time - ell / 2) ^ 2 / (2 * ell) := by ring
  have hmin : -(u * GaussianEnvelope.referenceMinSlope lam u / 2) *
      (time - ell / 2) ^ 2 / ell =
      -(u * GaussianEnvelope.referenceMinSlope lam u) * (time - ell / 2) ^ 2 / (2 * ell) := by ring
  rw [hmax, hmin]
  exact reference_gaussian_bounds_three_halves hlam hu hell ht

/-- The exact enlarged spectral gap corresponding to the endpoint magnitude `2u`. -/
theorem referenceEigenvalue_lower_three_halves {lam u ell v : ℝ}
    (hlam : 0 < lam) (hu : 0 ≤ u) (hell : 0 < ell)
    (hv : v ∈ Icc 0 (3 * ell / 2)) :
    lam / Real.sqrt (1 + (2 * u) ^ 2) ≤
      ViscousPropagator.referenceEigenvalue lam u ell v := by
  have hs := slotMagnitude_mem_three_halves hu hell hv
  unfold ViscousPropagator.referenceEigenvalue
  apply div_le_div_of_nonneg_left hlam.le (PulseGrowth.radius_pos _)
  apply Real.sqrt_le_sqrt
  nlinarith [hs.2]

end NavierStokes.V560Audit

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

/-- `coefficient_jets` is already proved on the open source slot. -/
theorem coefficient_continuous_three_halves
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i)) (i : ι) :
    ContinuousOn ((a.frame i).coefficient 1)
      (D.carrier i ×ˢ Icc 0 (3 * a.length i / 2)) :=
  ((a.coefficient_jets hh hr hM hu huM hL hslot hlarge 1).smooth i).continuousOn.mono
    (fun _ hz => ⟨hz.1, a.interval_three_halves_subset_slot hr i hz.2⟩)

/-- Same source constructor, unchanged Gaussian reference and t=0 seed. -/
noncomputable def primaryThreeHalves (hr : 0 < r0) (i : ι) (p : Slow) : ℝ → PrimaryODE.State :=
  PrimaryODE.primary (a.three_halves_nonneg hr i) (a.frame i)
    (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p

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

/-- The longer solution is exactly the native primary on their overlap. -/
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
    have hd := a.primaryThreeHalves_hasDerivAt hh hr hM hu huM hL hslot hlarge i hp
      (a.interval_subset_three_halves hr i hv)
    simpa only [add_zero] using hd
  · intro v hv
    have hd := PrimaryODE.primary_hasDerivAt (a.length_pos hr i).le (a.frame i)
      (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) hA0 hp hv
    simpa only [add_zero] using hd
  · simp only [primaryThreeHalves, PrimaryODE.primary_initial]

/-- The generic source `primary_bounds` theorem replayed on `[0,3L/2]`.
The only genuinely stronger modal hypothesis is the explicit cone condition
for the smaller enlarged spectral gap. -/
theorem primaryThreeHalves_reference_comparable
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i))
    (i : ι) {p : Slow} (hp : p ∈ D.carrier i)
    (hcone : 2 * GrowingMode.coneConstant
      (a.lam i / Real.sqrt (1 + (2 * u) ^ 2)) (modalConstant M u) ≤ D.scale i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ v ∈ Icc 0 (3 * a.length i / 2),
      0 < PrimaryODE.radialPrimary (a.three_halves_nonneg hr i) (a.frame i)
        (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p v ∧
      c * PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) v ≤
        PrimaryODE.radialPrimary (a.three_halves_nonneg hr i) (a.frame i)
          (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p v ∧
      PrimaryODE.radialPrimary (a.three_halves_nonneg hr i) (a.frame i)
          (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p v ≤
        C * PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) v := by
  let gap := a.lam i / Real.sqrt (1 + (2 * u) ^ 2)
  have hgap : 0 < gap := div_pos (a.lambda_pos hM i) (PulseGrowth.radius_pos _)
  have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
  have hA := a.coefficient_continuous_three_halves hh hr hM hu huM hL hslot hlarge i
  have herrors := error_constants_nonneg (u := u) hM
  have hslotL : a.length i ≤ (2 * r0 * ChartScales.Tg) * D.scale i := by
    simpa only [FamilyData.length, a.scale_eq i, mul_assoc] using
      (ChartScales.slotLength_bounds r0 h hr.le hh (hlarge i).four_le).2
  have hrt : 0 ≤ r0 * ChartScales.Tg := mul_nonneg hr.le ChartScales.Tg_pos.le
  have hthree : 3 * r0 * ChartScales.Tg ≤ M := by nlinarith [hslot]
  have hbudget : 3 * a.length i / 2 - 0 ≤ M * D.scale i := by
    calc
      3 * a.length i / 2 - 0 ≤ 3 * ((2 * r0 * ChartScales.Tg) * D.scale i) / 2 := by
        gcongr
      _ = (3 * r0 * ChartScales.Tg) * D.scale i := by ring
      _ ≤ M * D.scale i := mul_le_mul_of_nonneg_right hthree hS.le
  have hPpos (v : ℝ) (_hv : v ∈ Icc 0 (3 * a.length i / 2)) :
      0 < PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) v :=
    PrimaryPulseBounds.referenceP_pos _ _ _ _
  have hPeq (v : ℝ) (hv : v ∈ Icc 0 (3 * a.length i / 2)) :
      HasDerivAt (PrimaryPulseBounds.referenceP (a.lam i) u (a.length i))
        (((a.frame i).eigenvalue (p, v) -
          ViscousPropagator.referenceViscosity (a.lam i) u (a.length i) v) *
          PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) v) v := by
    change HasDerivAt (PrimaryPulseBounds.referenceP (a.lam i) u (a.length i))
      ((ViscousPropagator.referenceEigenvalue (a.lam i) u (a.length i) v -
        ViscousPropagator.referenceViscosity (a.lam i) u (a.length i) v) *
        PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) v) v
    exact PrimaryPulseBounds.referenceP_hasDerivAt _ _ _ _
  have hb := PrimaryODE.primary_bounds (a.three_halves_nonneg hr i) (a.frame i)
    (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2)
    hA hp hgap herrors.2.1 herrors.2.2 hS (by simpa only [gap] using hcone) hbudget
    (ViscousPropagator.referenceViscosity (a.lam i) u (a.length i))
    (fun v hv => by
      change gap ≤ ViscousPropagator.referenceEigenvalue (a.lam i) u (a.length i) v
      exact NavierStokes.V560Audit.referenceEigenvalue_lower_three_halves
        (a.lambda_pos hM i) hu.le (a.length_pos hr i) hv)
    (fun v hv => a.modal_errors hh hr hM hu huM hL hslot i (hlarge i) hp
      (a.interval_three_halves_subset_slot hr i hv))
    (fun v hv => a.damping_error hh hr hM hu huM hL hslot i (hlarge i) hp
      (a.interval_three_halves_subset_slot hr i hv))
    hPpos hPeq
  refine ⟨Real.exp (-(dampingConstant M + 2 * modalConstant M u) * M) / 2,
    3 * Real.exp ((dampingConstant M + 2 * modalConstant M u) * M) / 2,
    by positivity, by positivity, ?_⟩
  intro v hv
  have hvb := hb v hv
  exact ⟨hvb.1, hvb.2.1, hvb.2.2.1⟩

end FamilyData
end NavierStokes.BasePhaseGeometry
