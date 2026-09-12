import NavierStokes.ActualIterationLedger

/-!
# v5.8 metadata-level ceiling for the common physical gain

The v5.8 common boost

  gain(h,j) + h*(3/5-kappa)

is not an arbitrary conservative choice inside the existing metadata adapter.
The potential-wave channel can attain exactly this target when its class
exponent and shift saturate the current `StageMetadata` lower bounds:

  alpha = waveNative(kappa,j),
  shift = -h.

Since the physical potential offset is `+h`, the two shift terms cancel and
the resulting admissible gain is exactly `h*waveNative`, i.e. the v5.8 boosted
gain. Therefore a strictly larger *uniform* gain cannot be certified from the
current potential metadata premises alone. It would require stronger factual
information about the actual potential stages, such as a better class exponent
or a better shift bound.

This is a sharpness statement about the metadata interface, not a claim that
the actual constructed potential stage saturates those bounds.
-/

noncomputable section

namespace NavierStokes.V580MetadataGainCeiling

open NavierStokes.ActualIterationLedger

noncomputable def boostedGain (h κ : ℝ) (j : ℕ) : ℝ :=
  gain h j + h * (3 / 5 - κ)

/-- The potential channel's extremal metadata data produce exactly the v5.8
boosted gain. -/
theorem potential_extremal_eq_boostedGain
    (h κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    h * waveNative κ j + (-h) + (offsets h).wavePotential =
      boostedGain h κ j := by
  rw [wave_physical_gap h κ hj]
  simp only [offsets]
  unfold boostedGain
  ring

/-- Equivalently, the source metadata inequality for the potential channel is
sharp at the level of its stated premises. -/
theorem potential_extremal_ceiling
    {h κ target : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (htarget : boostedGain h κ j < target) :
    ¬ target ≤ h * waveNative κ j + (-h) + (offsets h).wavePotential := by
  rw [potential_extremal_eq_boostedGain h κ hj]
  exact not_le.mpr htarget

/-- At the pinned kappa, the metadata-level ceiling is exactly the published
gain plus `59999/100000*h`. -/
theorem pinned_potential_ceiling
    (h : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    h * waveNative kappa j + (-h) + (offsets h).wavePotential =
      gain h j + h * (59999 / 100000 : ℝ) := by
  rw [potential_extremal_eq_boostedGain h kappa hj]
  unfold boostedGain
  norm_num [kappa]

end NavierStokes.V580MetadataGainCeiling
