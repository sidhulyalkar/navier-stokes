import NavierStokes.HarmonicSourceSupport

/-!
# v5.13: Fourier coefficient to physical-field witness

P2c needs a source-backed way to turn nonvanishing of one actual harmonic
coefficient into nonvanishing of the evaluated real physical field.

The pinned source already proves Fourier uniqueness in the opposite direction:
if the evaluated real harmonic field vanishes for every angle, then every
real-projected coefficient vanishes. This module packages the contrapositive
as an existential physical witness.

This is a structural bridge only. It does not yet prove that a particular
positive-stage coefficient is nonzero in the strict-vs-doubling comparison
region.
-/

noncomputable section

namespace NavierStokes.V513FourierPhysicalWitness

open HarmonicFields HarmonicResidual HarmonicSourceSupport

/-- A nonzero actual real-projected harmonic coefficient forces a nonzero
value of the evaluated real field at some angle. -/
theorem exists_angle_field_ne_of_realCoefficient_ne
    {D : Type}
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (j : ℤ) (x : D)
    (hc : realCoefficients c j x ≠ 0) :
    ∃ θ : ℝ, (HarmonicFields.field c k Φ kp (x, θ)).re ≠ 0 := by
  by_contra h
  push_neg at h
  exact hc
    (HarmonicSourceSupport.realCoefficient_eq_zero_of_field
      c k Φ hkp j x h)

/-- Componentwise vector version, convenient for actual velocity blocks. -/
theorem exists_angle_vectorField_component_ne_of_realCoefficient_ne
    {D : Type}
    (a : HarmonicResidual.VectorCoefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (i : Fin 3) (j : ℤ) (x : D)
    (hc : realCoefficients (a i) j x ≠ 0) :
    ∃ θ : ℝ,
      (HarmonicResidual.vectorField a k Φ kp (x, θ) i).re ≠ 0 := by
  obtain ⟨θ, hθ⟩ :=
    exists_angle_field_ne_of_realCoefficient_ne (a i) k Φ hkp j x hc
  exact ⟨θ, by simpa [HarmonicResidual.vectorField] using hθ⟩

end NavierStokes.V513FourierPhysicalWitness
