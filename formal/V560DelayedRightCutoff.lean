import NavierStokes.GaussianTailFlat
import NavierStokes.WaveEnvelopeTransport

/-!
# v5.6 delayed right-cutoff geometry

This file contains only two source-locked geometric layers:

1. a normalized smooth cutoff deformation that preserves the native left
   transition, erases the native right transition, and delays shutdown to 3/2
   native slot lengths;
2. a wrapper around the pinned common-cover separation theorem showing that
   a 3/2-length rectangle is admissible whenever the small-chart radius has
   the corresponding `3*r0/2 < R` slack.

No residual norm, force reduction, or Navier-Stokes solution is asserted here.
-/

noncomputable section

namespace NavierStokes.V560DelayedRightCutoff

open Set

/-- Affine argument for a copy of OpenAI's fixed smooth cutoff. -/
def patchArgument (θ : ℝ) : ℝ := (20 * θ - 19) / 11

/-- A smooth patch supported in normalized time `[2/5,3/2]`, with plateau
`[27/40,49/40]`. -/
noncomputable def patchProfile (θ : ℝ) : ℝ := SmoothCutoffs.cutoff (patchArgument θ)

/-- The delayed normalized slot profile. -/
noncomputable def delayedProfile (θ : ℝ) : ℝ :=
  GaussianTailFlat.profile θ + patchProfile θ * (1 - GaussianTailFlat.profile θ)

theorem patchProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) patchProfile := by
  unfold patchProfile patchArgument
  exact SmoothCutoffs.cutoff_contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 11

/-- Exact patch plateau. -/
theorem patchProfile_one {θ : ℝ} (hθ : θ ∈ Icc (27 / 40 : ℝ) (49 / 40 : ℝ)) :
    patchProfile θ = 1 := by
  unfold patchProfile
  apply SmoothCutoffs.cutoff_one_of_abs_le
  rcases hθ with ⟨hlo, hhi⟩
  unfold patchArgument
  rw [abs_le]
  constructor <;> norm_num at hlo hhi ⊢ <;> linarith

/-- Exact left exterior of the patch support. -/
theorem patchProfile_zero_left {θ : ℝ} (hθ : θ ≤ (2 / 5 : ℝ)) :
    patchProfile θ = 0 := by
  unfold patchProfile
  apply SmoothCutoffs.cutoff_zero_of_one_le_abs
  have harg : patchArgument θ ≤ -1 := by
    unfold patchArgument
    norm_num at hθ ⊢
    linarith
  rw [abs_of_nonpos (by linarith [harg])]
  linarith

/-- Exact right exterior of the patch support. -/
theorem patchProfile_zero_right {θ : ℝ} (hθ : (3 / 2 : ℝ) ≤ θ) :
    patchProfile θ = 0 := by
  unfold patchProfile
  apply SmoothCutoffs.cutoff_zero_of_one_le_abs
  have harg : 1 ≤ patchArgument θ := by
    unfold patchArgument
    norm_num at hθ ⊢
    linarith
  rw [abs_of_nonneg (by linarith [harg])]
  exact harg

/-- Native profile plateau rewritten as a normalized interval. -/
theorem nativeProfile_one {θ : ℝ} (hθ : θ ∈ Icc (3 / 10 : ℝ) (7 / 10 : ℝ)) :
    GaussianTailFlat.profile θ = 1 := by
  apply GaussianTailFlat.profile_one
  rcases hθ with ⟨hlo, hhi⟩
  rw [abs_le]
  constructor <;> norm_num at hlo hhi ⊢ <;> linarith

/-- Native profile vanishes to the left of its exact support. -/
theorem nativeProfile_zero_left {θ : ℝ} (hθ : θ ≤ (1 / 6 : ℝ)) :
    GaussianTailFlat.profile θ = 0 := by
  apply GaussianTailFlat.profile_zero
  have harg : θ - 1 / 2 ≤ -(1 / 3 : ℝ) := by linarith
  rw [abs_of_nonpos (by linarith [harg])]
  linarith

/-- Native profile vanishes to the right of its exact support. -/
theorem nativeProfile_zero_right {θ : ℝ} (hθ : (5 / 6 : ℝ) ≤ θ) :
    GaussianTailFlat.profile θ = 0 := by
  apply GaussianTailFlat.profile_zero
  have harg : (1 / 3 : ℝ) ≤ θ - 1 / 2 := by linarith
  rw [abs_of_nonneg (by linarith [harg])]
  exact harg

/-- The patch's left transition lies entirely inside the native plateau. -/
theorem native_one_on_patch_left {θ : ℝ}
    (hθ : θ ∈ Icc (2 / 5 : ℝ) (27 / 40 : ℝ)) :
    GaussianTailFlat.profile θ = 1 :=
  nativeProfile_one ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- The entire native right derivative collar lies inside the patch plateau. -/
theorem patch_one_on_native_right {θ : ℝ}
    (hθ : θ ∈ Icc (7 / 10 : ℝ) (5 / 6 : ℝ)) :
    patchProfile θ = 1 :=
  patchProfile_one ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- The delayed cutoff is exactly the native cutoff throughout the native left
collar because the patch has not yet turned on. -/
theorem delayed_eq_native_on_left {θ : ℝ}
    (hθ : θ ∈ Icc (1 / 6 : ℝ) (3 / 10 : ℝ)) :
    delayedProfile θ = GaussianTailFlat.profile θ := by
  have hp : patchProfile θ = 0 := patchProfile_zero_left (by linarith [hθ.2])
  unfold delayedProfile
  rw [hp]
  ring

/-- The old right shutdown is erased exactly. -/
theorem delayed_one_on_native_right {θ : ℝ}
    (hθ : θ ∈ Icc (7 / 10 : ℝ) (5 / 6 : ℝ)) :
    delayedProfile θ = 1 := by
  have hp := patch_one_on_native_right hθ
  unfold delayedProfile
  rw [hp]
  ring

/-- The combined profile is one on the full delayed plateau. -/
theorem delayedProfile_one {θ : ℝ}
    (hθ : θ ∈ Icc (3 / 10 : ℝ) (49 / 40 : ℝ)) :
    delayedProfile θ = 1 := by
  by_cases hnative : θ ≤ (7 / 10 : ℝ)
  · have hn := nativeProfile_one ⟨hθ.1, hnative⟩
    unfold delayedProfile
    rw [hn]
    ring
  · have hp := patchProfile_one ⟨by linarith, hθ.2⟩
    unfold delayedProfile
    rw [hp]
    ring

/-- The left support endpoint is unchanged. -/
theorem delayedProfile_zero_left {θ : ℝ} (hθ : θ ≤ (1 / 6 : ℝ)) :
    delayedProfile θ = 0 := by
  have hn : GaussianTailFlat.profile θ = 0 := nativeProfile_zero_left (θ := θ) hθ
  have hp : patchProfile θ = 0 := patchProfile_zero_left (θ := θ) (by linarith [hθ])
  unfold delayedProfile
  rw [hn, hp]
  ring

/-- The delayed profile shuts down by normalized time 3/2. -/
theorem delayedProfile_zero_right {θ : ℝ} (hθ : (3 / 2 : ℝ) ≤ θ) :
    delayedProfile θ = 0 := by
  have hn : GaussianTailFlat.profile θ = 0 :=
    nativeProfile_zero_right (θ := θ) (by linarith [hθ])
  have hp : patchProfile θ = 0 := patchProfile_zero_right (θ := θ) hθ
  unfold delayedProfile
  rw [hn, hp]
  ring

/-- Exact extra squared Gaussian distance obtained by moving the right collar
from distance 1/5 to distance 29/40 from the midpoint. -/
theorem gaussian_gain_square :
    ((29 / 40 : ℝ) ^ 2 - (1 / 5 : ℝ) ^ 2) = 777 / 1600 := by
  norm_num

/-- Scaling the slot radius by 3/2 scales the slot length by exactly 3/2. -/
theorem slotLength_three_halves (r0 h : ℝ) (n : ℕ) :
    ChartScales.slotLength (3 * r0 / 2) h n =
      3 * ChartScales.slotLength r0 h n / 2 := by
  unfold ChartScales.slotLength
  ring

/-- Direct wrapper around the pinned common-cover theorem for the 3/2 rectangle. -/
theorem separated_bandGeometry_three_halves
    (B : TorusInverse.Plane ≃L[ℝ] TorusInverse.Plane) (h : ℝ) (n gap : ℕ)
    (center : TorusInverse.Plane) {r r0 R : ℝ}
    (hr : r < R) (hr0 : 3 * r0 / 2 < R)
    (hsmall : ‖(B : TorusInverse.Plane →L[ℝ] TorusInverse.Plane)‖ * R < 1 / 2) :
    WaveEnvelopeTransport.Separated (CommonCoverClass.bandGeometry B h n gap center) r
      (3 * ChartScales.slotLength r0 h n / 2) := by
  rw [← slotLength_three_halves]
  exact WaveEnvelopeTransport.separated_bandGeometry B h n gap center hr hr0 hsmall

end NavierStokes.V560DelayedRightCutoff
