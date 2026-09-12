import NavierStokes.LinearWaveBounds

/-!
# v5.7 improved linear-wave remainder gain

This file tests a source-locked quantitative sharpening of the pinned
`LinearWaveBounds` remainder ledger.

The pinned helper theorem `remainder_components` places every term in the
common class

  α + 1/2 - 3κ.

Inspecting the primitive estimates shows that, under the already-used
hypothesis `κ ≤ 1/2`, each concrete remainder term can instead be placed in

  α + 1/2 - κ.

For the actual primary parameters α=1/2 and κ=1/10 this is 9/10 instead of
7/10.  This file proves only that local weighted-class sharpening.  It does
not claim that downstream correction-cycle ledgers automatically inherit the
stronger exponent, that the estimate is sharp, or that any forcing norm is
reduced.
-/

noncomputable section

namespace NavierStokes.V570ImprovedLinearRemainder

open Set Filter
open WeightedClasses HarmonicCalculus
open LinearWaveBounds
open scoped Topology ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

variable {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
  {d : GraphDirections D} {a : WaveCoefficients D}

/-- The slow transport term has substantial slack relative to the improved
common target `α + 1/2 - κ`. -/
theorem slowTransport_mem_improved
    (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - κ) (fun n x =>
      LinearWaveResidual.slowTransport (s.epsilon n) (a.radialBase n) (a.axialBase n)
        (fun _ => d.slow) (d.radialField n) (d.axialField s n) (a.amplitude n) x i) := by
  have ht := class_neg ((d.Dt_mem (h.amplitude i)).band_smul (band_epsilon s))
  have hr := real_mul_complex h.b_unweighted
    (d.Dr_mem (h.amplitude i) h.radial_profile h.radial_scale h.loss_nonneg)
  have hz := real_mul_complex h.axial_base (d.Dz_mem (h.amplitude i))
  have ht' := ht.mono_exponent
    (show α + 1 / 2 - κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hr' := hr.mono_exponent
    (show α + 1 / 2 - κ ≤ 1 + (α - κ) by linarith)
  have hz' := hz.mono_exponent
    (show α + 1 / 2 - κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  simpa only [LinearWaveResidual.slowTransport, GraphDirections.Dt, GraphDirections.Dr,
    GraphDirections.Dz, Complex.real_smul, neg_mul] using (ht'.add hr').add hz'

/-- The phase-defect term is naturally in the stronger class `α + 1/2`. -/
theorem phaseDefect_mem_improved
    (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - κ) (fun n x =>
      phaseFactor (a.frequency n) * Complex.ofReal (a.defect s d n x) * a.amplitude n x i) := by
  have hh := frequency_mul (real_mul_complex h.defect (h.amplitude i)) h.frequency_scale
  have hh' := hh.mono_exponent
    (show α + 1 / 2 - κ ≤ (1 + α) - 1 / 2 by linarith [h.loss_nonneg])
  simpa only [mul_assoc] using hh'

/-- The base-derivative remainder is naturally at least order `α+1`, so it
also fits the improved common target. -/
theorem baseDerivativeRemainder_mem_improved
    (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - κ) (fun n x =>
      LinearWaveResidual.baseDerivativeRemainder (a.radius n) (a.radialBase n)
        (a.frequencyBase n) (a.axialBase n) (d.radialField n) (d.axialField s n)
        (a.amplitude n) x i) := by
  have hbr := d.Dr_base_mem h.b_unweighted h.radial_base_aux
  have h0 := (complex_mul_real (h.amplitude 0) hbr).mono_exponent
    (show α + 1 / 2 - κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hbinv := unweighted_mul h.b_unweighted h.inverse_radius
  have h1 := (real_mul_complex hbinv (h.amplitude 1)).mono_exponent
    (show α + 1 / 2 - κ ≤ (1 + 0) + α by linarith [h.loss_nonneg])
  have hz (j : Fin 3) :=
    (complex_mul_real (h.amplitude 2) (d.Dz_mem (h.base_components j))).mono_exponent
      (show α + 1 / 2 - κ ≤ α + (0 + 1) by linarith [h.loss_nonneg])
  fin_cases i
  · simpa [LinearWaveResidual.baseDerivativeRemainder, GraphDirections.Dr, GraphDirections.Dz]
      using h0.add (hz 0)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, GraphDirections.Dz, div_eq_mul_inv]
      using h1.add (hz 1)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, GraphDirections.Dz] using hz 2

/-- The radial pressure derivative exactly reaches the improved common target;
the axial pressure derivative is stronger and the angular component vanishes. -/
theorem pressureGradient_mem_improved
    (h : InputBounds s P α κ d a) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - κ) (fun n x =>
      LinearWaveResidual.strippedPressureGradient (d.radialField n) (d.axialField s n)
        (a.pressure n) x i) := by
  fin_cases i
  · have hh := d.Dr_mem h.pressure h.radial_profile h.radial_scale h.loss_nonneg
    simp [LinearWaveResidual.strippedPressureGradient] at hh ⊢
    exact hh
  · simpa [LinearWaveResidual.strippedPressureGradient] using
      (MemClass.zero (α := α + 1 / 2 - κ) (E := ℂ) (h.amplitude 0).weight_nonneg)
  · have hh := (d.Dz_mem h.pressure).mono_exponent
      (show α + 1 / 2 - κ ≤ (α + 1 / 2) + 1 by linarith [h.loss_nonneg])
    simp [LinearWaveResidual.strippedPressureGradient] at hh ⊢
    exact hh

/-- Before multiplication by viscosity scale `epsilon`, the weakest visible
viscous cross/divergence terms have exponent `α - 1/2 - κ`.  The only extra
hypothesis needed to place the two-radial-derivative term in the same class is
`κ ≤ 1/2`, already assumed by the source's good-coefficient theorem. -/
theorem viscousRemainder_mem_improved
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2) (i : Fin 3) :
    WaveClass s P (α - 1 / 2 - κ) (fun n x =>
      LinearWaveResidual.viscousRemainder (a.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n) (a.phase n) (a.amplitude n) x i) := by
  have hAi := h.amplitude i
  have hDr := d.Dr_mem hAi h.radial_profile h.radial_scale h.loss_nonneg
  have hDrr := d.Dr_mem hDr h.radial_profile h.radial_scale h.loss_nonneg
  have hDz := d.Dz_mem hAi
  have hDzz := d.Dz_mem hDz
  have hri := real_mul_complex h.inverse_radius hDr
  have hJ := angular_classes h.amplitude
  have hJJ := angular_classes hJ
  have hjj := real_mul_complex h.inverse_radius_sq (hJJ i)
  have hcrossr := real_mul_complex (h.normal 0) hDr
  have hcrossz := real_mul_complex (h.normal 2) hDz
  have hcrossr' : WaveClass s P (α - κ) (fun n x =>
      Complex.ofReal (a.normal s d n x 0) * d.Dr (fun n x => a.amplitude n x i) n x) := by
    simpa only [zero_add] using hcrossr
  have hcrossz' := hcrossz.mono_exponent
    (show α - κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  have hcross := constant_complex_mul
    (frequency_mul (hcrossr'.add hcrossz') h.frequency_scale) 2
  have hNr := d.Dr_mem (h.normal 0) h.radial_profile h.radial_scale h.loss_nonneg
  have hNi := unweighted_mul (h.normal 0) h.inverse_radius
  have hNz := d.Dz_mem (h.normal 2)
  have hNr' : UnweightedClass s (-κ) (d.Dr (fun n x => a.normal s d n x 0)) := by
    simpa only [zero_sub] using hNr
  have hNi' := hNi.mono_exponent (show -κ ≤ 0 + 0 by linarith [h.loss_nonneg])
  have hNz' := hNz.mono_exponent (show -κ ≤ 0 + 1 by linarith [h.loss_nonneg])
  have hdiv := frequency_mul (real_mul_complex ((hNr'.add hNi').add hNz') hAi) h.frequency_scale
  have htheta := constant_complex_mul
    (frequency_mul (real_mul_complex (unweighted_mul (h.normal 1) h.inverse_radius) (hJ i))
      h.frequency_scale) 2
  have hDrr' := hDrr.mono_exponent
    (show α - 1 / 2 - κ ≤ (α - κ) - κ by linarith [hκ])
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
  simpa only [LinearWaveResidual.viscousRemainder, GraphDirections.Dr, GraphDirections.Dz,
    WaveCoefficients.normal, Complex.real_smul, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_assoc] using hh

/-- Multiplication by `epsilon` recovers one full exponent and places the
viscous contribution at the improved target. -/
theorem viscousPart_mem_improved
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - κ) (fun n x => (s.epsilon n : ℂ) *
      LinearWaveResidual.viscousRemainder (a.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n) (a.phase n) (a.amplitude n) x i) := by
  have hh := (viscousRemainder_mem_improved h hκ i).band_smul (band_epsilon s)
  have he : (α - 1 / 2 - κ) + 1 = α + 1 / 2 - κ := by ring
  rw [he] at hh
  simpa only [Complex.real_smul] using hh

/-- Improved common remainder class obtained without changing any primitive
source assumptions. -/
theorem remainder_components_improved
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2) (i : Fin 3) :
    WaveClass s P (α + 1 / 2 - κ) (fun n x => a.remainder s d n x i) := by
  have hh := class_sub
    ((((slowTransport_mem_improved h i).add (phaseDefect_mem_improved h i)).add
      (baseDerivativeRemainder_mem_improved h i)).add
      (pressureGradient_mem_improved h i))
      (viscousPart_mem_improved h hκ i)
  simpa only [WaveCoefficients.remainder, WaveCoefficients.defect, LinearWaveResidual.remainder] using hh

theorem remainder_class_improved
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2) :
    WaveClass s P (α + 1 / 2 - κ) (a.remainder s d) :=
  component_classes (remainder_components_improved h hκ)

/-- The principal operator preserves the curl-correction class exactly, so it
needs no additional `2κ` weakening. -/
theorem curl_principal_gain_improved
    (h : InputBounds s P α κ d a)
    {f : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i)) :
    WaveClass s P (α + 1 / 2 - κ) (a.principalVelocity s d f) :=
  h.principalVelocity_class hf

/-- Stronger good-coefficient theorem using the exact principal preservation
and the sharpened remainder ledger. -/
theorem goodCoefficient_class_improved
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ)
    {f : ℕ → D → ComplexVector}
    (hf : ∀ i, WaveClass s P (α + 1 / 2 - κ) (fun n x => f n x i)) :
    WaveClass s P (α + 1 / 2 - κ) (a.goodCoefficient s d ψ f) := by
  exact (curl_principal_gain_improved h hf).add
    (remainder_class_improved ((h.with_cutoff hψ).add_curl_amplitude hκ hf) hκ)

/-- Source-compatible strengthening for the actual curl-corrected coefficient. -/
theorem constructed_goodCoefficient_class_improved
    (h : InputBounds s P α κ d a) (hκ : κ ≤ 1 / 2)
    {ψ : ℕ → D → ℝ} (hψ : UnweightedClass s 0 ψ) {R : D → ℝ}
    (hR : a.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n)) :
    WaveClass s P (α + 1 / 2 - κ) (a.constructedGood s d ψ) := by
  have hc := (h.with_cutoff hψ).curlCorrection_class hR hN hb hlower hupper hK
  exact goodCoefficient_class_improved h hκ hψ
    (fun i => CurlClassBounds.class_component hc i)

/-- Numeric specialization of the gain used by the pinned actual primary. -/
theorem actual_primary_gain :
    (1 / 2 : ℝ) + 1 / 2 - 1 / 10 = 9 / 10 := by
  norm_num

/-- The strengthened candidate gain is strictly larger than the source helper's
`7/10` specialization. -/
theorem actual_primary_gain_strict :
    (7 / 10 : ℝ) < 9 / 10 := by
  norm_num

end NavierStokes.V570ImprovedLinearRemainder