import NavierStokes.ActualInitialization

/-!
# v5.7 three-gate promotion of the initial analytic invariant

`CycleAnalyticInvariant` carries many structural, support, regularity, and
representation fields, but only three fields depend quantitatively on the
accuracy parameter `σ`:

* the nonconstant harmonic residual at exponent `1/2 + σ`;
* the mean residual bound at parameter `σ`;
* the pressure/debt defect bound at parameter `σ`.

This file proves that upgrading exactly those three gates from `σ = 1/5` to
`σ = 2/5` upgrades the complete existing initial invariant.  It intentionally
does not prove the three upgraded estimates themselves.
-/

noncomputable section

namespace NavierStokes.V570InitialInvariantPromotion

open Set Filter Function WeightedClasses CorrectionState CorrectionStep
open HarmonicMeanInteraction HarmonicWaveInteraction UniformHarmonicInteraction
open scoped ContDiff Topology BigOperators

open NavierStokes.ActualInitialization

variable {B N0 : ℕ}

/-- No fourth quantitative gate is hidden in `CycleAnalyticInvariant`: once
residual, mean, and debt are available at the `σ = 2/5` targets, all remaining
fields are inherited verbatim from the already-proved initial invariant. -/
theorem initial_invariant_two_fifths_of_three_gates
    (hres : UniformVelocity strip envelope (9/10)
      (initialResidualBlock (B := B) (N0 := N0)))
    (hmean : MeanResidualBounds strip (2/5)
      (ActualPrimary.commonContext B) (initialState B N0))
    (hdebt : DefectBounds slowStrip (2/5)
      (ActualPrimary.commonContext B) (initialState B N0)) :
    CycleAnalyticInvariant geometry (ActualPrimary.commonContext B)
      (tangentBlock (B := B) (N0 := N0)) envelope labelCarrier (2/5)
      (initialCycleState B N0) := by
  let H := initial_invariant B N0
  refine
    { representation := H.representation
      bands := H.bands
      realCoefficients := H.realCoefficients
      inputSupport := H.inputSupport
      sourceBand := H.sourceBand
      zeroVelocity := H.zeroVelocity
      zeroPressure := H.zeroPressure
      carrier := H.carrier
      phase := H.phase
      frequency := H.frequency
      angular := H.angular
      coefficientSmooth := H.coefficientSmooth
      pressureCoefficientSmooth := H.pressureCoefficientSmooth
      gaussianCoefficientSmooth := H.gaussianCoefficientSmooth
      solenoidal := H.solenoidal
      wave := H.wave
      pressure := H.pressure
      difference := H.difference
      cumulative := H.cumulative
      covariance := H.covariance
      residual := ?_
      mean := ?_
      meanHypotheses := H.meanHypotheses
      debt := ?_
      primitives := H.primitives
      reconstructed := H.reconstructed
      masses := H.masses
      oscillationSmooth := H.oscillationSmooth
      oscillatoryPressureSmooth := H.oscillatoryPressureSmooth
      oscillationPeriodic := H.oscillationPeriodic
      oscillationSupport := H.oscillationSupport
      gaussianFlat := H.gaussianFlat
      gaussianMean := H.gaussianMean
      aliasCoefficients := H.aliasCoefficients
      axisFlat := H.axisFlat
      baseAngular := H.baseAngular }
  · have he : (1 / 2 : ℝ) + 2 / 5 = 9 / 10 := by norm_num
    rw [he]
    simpa [initialResidualBlock, initialCycleState, coefficients] using hres
  · simpa [initialCycleState] using hmean
  · simpa [initialCycleState, geometry_slowStrip] using hdebt

end NavierStokes.V570InitialInvariantPromotion
