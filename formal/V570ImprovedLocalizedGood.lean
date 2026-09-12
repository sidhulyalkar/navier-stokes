import NavierStokes.LocalizedWaveBounds

/-!
# v5.7 localized retained-good sharpening

The global linear-wave sharpening in `V570ImprovedLinearRemainder` is not by
itself enough for the actual primary family.  The construction passes through
`LocalizedWaveBounds`, where the same `3κ` common target is reintroduced.

This file tests the corresponding local/uniform estimate directly from the
same primitive local hypotheses.  The intended target is

  α + 1/2 - κ

instead of

  α + 1/2 - 3κ.

No actual-primary or cycle-invariant claim is made here.
-/

noncomputable section

namespace NavierStokes.V570ImprovedLocalizedGood

open Set Function Filter WeightedClasses HarmonicCalculus LinearWaveBounds
open LocalizedWaveBounds
open scoped Topology ContDiff BigOperators InnerProductSpace

variable {D I : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]

variable {s : StripData D} {K : ℕ → I → Set D} {P : ℕ → I → D → ℝ}
  {α κ : ℝ} {d : GraphDirections D} {a : WaveFamily D I}

/-- Local slow transport fits the improved common target. -/
theorem slowTransport_mem_improved
    (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - κ) (fun n i x =>
      LinearWaveResidual.slowTransport (s.epsilon n) (a.radialBase n i) (a.axialBase n i)
        (fun _ => d.slow) (d.radialField n) (d.axialField s n) (a.amplitude n i) x j) := by
  have ht := ((Dt_mem d (h.amplitude j)).band_smul (LinearWaveBounds.band_epsilon s)).neg
  have hr := real_mul_complex h.radial_base
    (Dr_mem d (h.amplitude j) h.radial_profile h.radial_scale h.loss_nonneg)
  have hz := real_mul_complex h.axial_base (Dz_mem d (h.amplitude j))
  have ht' := ht.mono_exponent
    (show α + 1 / 2 - κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hr' := hr.mono_exponent
    (show α + 1 / 2 - κ ≤ 1 + (α - κ) by linarith)
  have hz' := hz.mono_exponent
    (show α + 1 / 2 - κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  simpa only [LinearWaveResidual.slowTransport, Dt, Dr, Dz, Complex.real_smul, neg_mul]
    using (ht'.add hr').add hz'

/-- Local material phase defect has additional slack. -/
theorem phaseDefect_mem_improved
    (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - κ) (fun n i x =>
      phaseFactor (a.frequency n i) * Complex.ofReal (a.defect s d n i x) * a.amplitude n i x j) := by
  have hh := frequency_mul (real_mul_complex h.defect (h.amplitude j)) h.frequency_scale
  have hh' := hh.mono_exponent
    (show α + 1 / 2 - κ ≤ (1 + α) - 1 / 2 by linarith [h.loss_nonneg])
  simpa only [mul_assoc] using hh'

/-- Local base-derivative remainder has at least one full power of slack. -/
theorem baseDerivativeRemainder_mem_improved
    (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - κ) (fun n i x =>
      LinearWaveResidual.baseDerivativeRemainder (a.radius n i) (a.radialBase n i)
        (a.frequencyBase n i) (a.axialBase n i) (d.radialField n) (d.axialField s n)
        (a.amplitude n i) x j) := by
  have hbr := Dr_base_mem d h.radial_base h.radial_base_aux
  have h0 := (complex_mul_real (h.amplitude 0) hbr).mono_exponent
    (show α + 1 / 2 - κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hbinv := unweighted_mul h.radial_base h.inverse_radius
  have h1 := (real_mul_complex hbinv (h.amplitude 1)).mono_exponent
    (show α + 1 / 2 - κ ≤ (1 + 0) + α by linarith [h.loss_nonneg])
  have hz (q : Fin 3) :=
    (complex_mul_real (h.amplitude 2) (Dz_mem d (h.base_components q))).mono_exponent
      (show α + 1 / 2 - κ ≤ α + (0 + 1) by linarith [h.loss_nonneg])
  fin_cases j
  · simpa [LinearWaveResidual.baseDerivativeRemainder, Dr, Dz] using h0.add (hz 0)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, Dz, div_eq_mul_inv] using h1.add (hz 1)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, Dz] using hz 2

/-- The local radial pressure derivative reaches the improved target exactly. -/
theorem pressureGradient_mem_improved
    (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - κ) (fun n i x =>
      LinearWaveResidual.strippedPressureGradient (d.radialField n) (d.axialField s n)
        (a.pressure n i) x j) := by
  fin_cases j
  · have hh := Dr_mem d h.pressure h.radial_profile h.radial_scale h.loss_nonneg
    simp [LinearWaveResidual.strippedPressureGradient] at hh ⊢
    exact hh
  · simpa [LinearWaveResidual.strippedPressureGradient] using
      (LocalClass.zero (α := α + 1 / 2 - κ) (E := ℂ) (h.amplitude 0).weight_nonneg)
  · have hh := (Dz_mem d h.pressure).mono_exponent
      (show α + 1 / 2 - κ ≤ (α + 1 / 2) + 1 by linarith)
    simp [LinearWaveResidual.strippedPressureGradient] at hh ⊢
    exact hh

/-- Local viscous remainder before multiplication by epsilon. -/
theorem viscousRemainder_mem_improved
    (h : InputBounds s K P α κ d a) (hκ : κ ≤ 1 / 2) (j : Fin 3) :
    LocalWave s K P (α - 1 / 2 - κ) (fun n i x =>
      LinearWaveResidual.viscousRemainder (a.radius n i) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n i) (a.phase n i) (a.amplitude n i) x j) := by
  have hAi := h.amplitude j
  have hDr := Dr_mem d hAi h.radial_profile h.radial_scale h.loss_nonneg
  have hDrr := Dr_mem d hDr h.radial_profile h.radial_scale h.loss_nonneg
  have hDz := Dz_mem d hAi
  have hDzz := Dz_mem d hDz
  have hri := real_mul_complex h.inverse_radius hDr
  have hJ := angular_classes h.amplitude
  have hJJ := angular_classes hJ
  have hjj := real_mul_complex h.inverse_radius_sq (hJJ j)
  have hcrossr := real_mul_complex (h.normal_component 0) hDr
  have hcrossz := real_mul_complex (h.normal_component 2) hDz
  have hcrossr' : LocalWave s K P (α - κ) (fun n i x =>
      Complex.ofReal (a.normal s d n i x 0) * Dr d (fun n i x => a.amplitude n i x j) n i x) := by
    simpa only [zero_add] using hcrossr
  have hcrossz' := hcrossz.mono_exponent
    (show α - κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  have hcross := constant_complex_mul
    (frequency_mul (hcrossr'.add hcrossz') h.frequency_scale) 2
  have hNr := Dr_mem d (h.normal_component 0) h.radial_profile h.radial_scale h.loss_nonneg
  have hNi := unweighted_mul (h.normal_component 0) h.inverse_radius
  have hNz := Dz_mem d (h.normal_component 2)
  have hNr' : LocalUnweighted s K (-κ) (Dr d (fun n i x => a.normal s d n i x 0)) := by
    simpa only [zero_sub] using hNr
  have hNi' := hNi.mono_exponent (show -κ ≤ 0 + 0 by linarith [h.loss_nonneg])
  have hNz' := hNz.mono_exponent (show -κ ≤ 0 + 1 by linarith [h.loss_nonneg])
  have hdiv := frequency_mul (real_mul_complex ((hNr'.add hNi').add hNz') hAi) h.frequency_scale
  have htheta := constant_complex_mul
    (frequency_mul
      (real_mul_complex (unweighted_mul (h.normal_component 1) h.inverse_radius) (hJ j))
      h.frequency_scale) 2
  have hDrr' := hDrr.mono_exponent
    (show α - 1 / 2 - κ ≤ (α - κ) - κ by linarith)
  have hri' := hri.mono_exponent
    (show α - 1 / 2 - κ ≤ 0 + (α - κ) by linarith)
  have hDzz' := hDzz.mono_exponent
    (show α - 1 / 2 - κ ≤ (α + 1) + 1 by linarith [h.loss_nonneg])
  have hjj' := hjj.mono_exponent
    (show α - 1 / 2 - κ ≤ 0 + α by linarith [h.loss_nonneg])
  have hcross' := hcross.mono_exponent
    (show α - 1 / 2 - κ ≤ (α - κ) - 1 / 2 by linarith)
  have hdiv' := hdiv.mono_exponent
    (show α - 1 / 2 - κ ≤ (-κ + α) - 1 / 2 by linarith)
  have htheta' := htheta.mono_exponent
    (show α - 1 / 2 - κ ≤ ((0 + 0) + α) - 1 / 2 by linarith [h.loss_nonneg])
  have hh := (((((hDrr'.add hri').add hDzz').add hjj').add hcross').add hdiv').add htheta'
  simpa only [LinearWaveResidual.viscousRemainder, Dr, Dz, WaveFamily.normal,
    WaveFamily.coefficients, WaveCoefficients.normal, Complex.real_smul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_assoc] using hh

/-- Multiplication by epsilon restores one exponent. -/
theorem viscousPart_mem_improved
    (h : InputBounds s K P α κ d a) (hκ : κ ≤ 1 / 2) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - κ) (fun n i x => (s.epsilon n : ℂ) *
      LinearWaveResidual.viscousRemainder (a.radius n i) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n i) (a.phase n i) (a.amplitude n i) x j) := by
  have hh := (viscousRemainder_mem_improved h hκ j).band_smul (LinearWaveBounds.band_epsilon s)
  have he : (α - 1 / 2 - κ) + 1 = α + 1 / 2 - κ := by ring
  rw [he] at hh
  simpa only [Complex.real_smul] using hh

/-- Every literal localized remainder term admits the improved target. -/
theorem remainder_components_improved
    (h : InputBounds s K P α κ d a) (hκ : κ ≤ 1 / 2) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - κ) (fun n i x => a.remainder s d n i x j) := by
  have hh := ((((slowTransport_mem_improved h j).add (phaseDefect_mem_improved h j)).add
    (baseDerivativeRemainder_mem_improved h j)).add
    (pressureGradient_mem_improved h j)).sub (viscousPart_mem_improved h hκ j)
  simpa only [WaveFamily.remainder, WaveFamily.defect, WaveFamily.coefficients,
    WaveCoefficients.remainder, WaveCoefficients.defect, LinearWaveResidual.remainder] using hh

theorem remainder_class_improved
    (h : InputBounds s K P α κ d a) (hκ : κ ≤ 1 / 2) :
    LocalWave s K P (α + 1 / 2 - κ) (a.remainder s d) :=
  component_classes (remainder_components_improved h hκ)

/-- Localized retained-good estimate with the proof-only `2κ` weakening removed. -/
theorem retainedGood_class_improved
    (h : InputBounds s K P α κ d a) (hκ : κ ≤ 1 / 2)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖a.normal s d n i x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖a.normal s d n i x‖ ≤ M)
    (hfreq : LocalUnweighted s K (1 / 2) (fun n i _ => 1 / a.frequency n i)) :
    LocalWave s K P (α + 1 / 2 - κ) (a.retainedGood s d) := by
  have hc := h.curlCorrection_class hb hlower hupper hfreq
  have hci q := hc.map (ContinuousLinearMap.proj q)
  have hp := h.principalVelocity_class hci
  exact hp.add (remainder_class_improved (h.add_curl_amplitude hκ hci) hκ)

end NavierStokes.V570ImprovedLocalizedGood
