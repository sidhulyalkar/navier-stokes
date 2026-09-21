import NavierStokes.V510StrictScheduleSeparation
import NavierStokes.SmoothCutoffs
import NavierStokes.SolenoidalDiagonal

/-!
# v5.11: deterministic stage-two cutoff separation

The paired v5.11 construction already proves that the minimal strict and
doubling schedules can be selected from identical local admissibility data and
are strictly separated at stage one. Schedule separation alone does not imply
that the physical cut fields differ: the underlying raw stage could vanish
where the cutoff profiles differ.

This module sharpens the geometry without assuming anything about the unknown
transition profile of the smooth cutoff.

Because every positive-stage least local scale is independent of the stage-zero
floor, choose one common floor above the least local scales at stages one and
two. Then the first three recursive values are forced to be

  strict:   B, B+1, B+2
  doubling: B, 2B, 4B.

For B >= 2 this gives 2*(B+2) <= 4B. At the explicit radius

  q* = 1 / (2 * aStrict 2)

the strict cutoff is exactly one while the doubling cutoff is exactly zero.
No positivity property in the transition collar is needed.

The final theorem isolates the remaining P2b obligation exactly: if the raw
stage is nonzero at a point with q=q*, then the two cut stages are genuinely
different there. This is still not a force-norm comparison.
-/

noncomputable section

namespace NavierStokes.V511StageTwoCutoffSeparation

open V590CanonicalDiagonalScale
open V510MinimalStrictSchedule
open V510StrictScheduleSeparation

/-- If the common floor dominates the first two positive-stage local scales,
the two recursive selectors have explicit values through stage two. -/
theorem first_three_schedule_values
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ)
    (hBtwo : 2 ≤ B)
    (hB1 : leastLocalScale C p g hg 0 1 < B)
    (hB2 : leastLocalScale C p g hg 0 2 < B) :
    minimalStrictSchedule C p g hg B 0 = B ∧
    canonicalSchedule C p g hg B 0 = B ∧
    minimalStrictSchedule C p g hg B 1 = B + 1 ∧
    canonicalSchedule C p g hg B 1 = 2 * B ∧
    minimalStrictSchedule C p g hg B 2 = B + 2 ∧
    canonicalSchedule C p g hg B 2 = 4 * B := by
  have hB1one : 1 ≤ B := by omega
  have hzero : leastLocalScale C p g hg B 0 = B := by
    rw [leastLocalScale_zero_eq_max_one C p g hg B]
    exact max_eq_right hB1one
  have hone :
      leastLocalScale C p g hg B 1 =
        leastLocalScale C p g hg 0 1 := by
    exact leastLocalScale_floor_independent_of_pos
      C p g hg (B := B) (B' := 0) (j := 1) (by omega)
  have htwo :
      leastLocalScale C p g hg B 2 =
        leastLocalScale C p g hg 0 2 := by
    exact leastLocalScale_floor_independent_of_pos
      C p g hg (B := B) (B' := 0) (j := 2) (by omega)
  have hl1 : leastLocalScale C p g hg B 1 ≤ B := by
    rw [hone]
    omega
  have hl2 : leastLocalScale C p g hg B 2 ≤ B := by
    rw [htwo]
    omega

  have hs0 : minimalStrictSchedule C p g hg B 0 = B := by
    unfold minimalStrictSchedule
    simp [strictEnvelope, hzero, max_eq_right hB1one]
  have hd0 : canonicalSchedule C p g hg B 0 = B := by
    unfold canonicalSchedule
    simp [DiagonalScale.doublingEnvelope, hzero, max_eq_right hB1one]

  have hs1 : minimalStrictSchedule C p g hg B 1 = B + 1 := by
    unfold minimalStrictSchedule
    change
      max (leastLocalScale C p g hg B 1)
          (max 1 (leastLocalScale C p g hg B 0) + 1) = B + 1
    rw [hzero, max_eq_right hB1one]
    exact max_eq_right (by omega)

  have hd1 : canonicalSchedule C p g hg B 1 = 2 * B := by
    unfold canonicalSchedule
    change
      max (leastLocalScale C p g hg B 1)
          (2 * max 1 (leastLocalScale C p g hg B 0)) = 2 * B
    rw [hzero, max_eq_right hB1one]
    exact max_eq_right (by omega)

  have hs2 : minimalStrictSchedule C p g hg B 2 = B + 2 := by
    unfold minimalStrictSchedule at hs1 ⊢
    change
      max (leastLocalScale C p g hg B 2)
          (strictEnvelope (leastLocalScale C p g hg B) 1 + 1) = B + 2
    have hs1' :
        strictEnvelope (leastLocalScale C p g hg B) 1 = B + 1 := hs1
    rw [hs1']
    exact max_eq_right (by omega)

  have hd2 : canonicalSchedule C p g hg B 2 = 4 * B := by
    unfold canonicalSchedule at hd1 ⊢
    change
      max (leastLocalScale C p g hg B 2)
          (2 * DiagonalScale.doublingEnvelope
            (leastLocalScale C p g hg B) 1) = 4 * B
    have hd1' :
        DiagonalScale.doublingEnvelope
          (leastLocalScale C p g hg B) 1 = 2 * B := hd1
    rw [hd1']
    ring_nf
    exact max_eq_right (by omega)

  exact ⟨hs0, hd0, hs1, hd1, hs2, hd2⟩

/-- One common floor can dominate any requested lower floor and the first two
positive-stage local scales. -/
theorem exists_floor_first_three_schedule_values
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ B : ℕ,
      lower ≤ B ∧
      2 ≤ B ∧
      minimalStrictSchedule C p g hg B 0 = B ∧
      canonicalSchedule C p g hg B 0 = B ∧
      minimalStrictSchedule C p g hg B 1 = B + 1 ∧
      canonicalSchedule C p g hg B 1 = 2 * B ∧
      minimalStrictSchedule C p g hg B 2 = B + 2 ∧
      canonicalSchedule C p g hg B 2 = 4 * B := by
  let l1 := leastLocalScale C p g hg 0 1
  let l2 := leastLocalScale C p g hg 0 2
  let B := max lower (max 2 (max (l1 + 1) (l2 + 1)))
  have hlower : lower ≤ B := le_max_left _ _
  have hBtwo : 2 ≤ B := by
    exact (le_max_left 2 (max (l1 + 1) (l2 + 1))).trans
      (le_max_right lower (max 2 (max (l1 + 1) (l2 + 1))))
  have hB1 : leastLocalScale C p g hg 0 1 < B := by
    have hle : l1 + 1 ≤ B := by
      exact (le_max_left (l1 + 1) (l2 + 1)).trans
        ((le_max_right 2 (max (l1 + 1) (l2 + 1))).trans
          (le_max_right lower (max 2 (max (l1 + 1) (l2 + 1)))))
    simpa only [l1] using (Nat.lt_of_succ_le hle)
  have hB2 : leastLocalScale C p g hg 0 2 < B := by
    have hle : l2 + 1 ≤ B := by
      exact (le_max_right (l1 + 1) (l2 + 1)).trans
        ((le_max_right 2 (max (l1 + 1) (l2 + 1))).trans
          (le_max_right lower (max 2 (max (l1 + 1) (l2 + 1)))))
    simpa only [l2] using (Nat.lt_of_succ_le hle)
  obtain ⟨hs0, hd0, hs1, hd1, hs2, hd2⟩ :=
    first_three_schedule_values C p g hg B hBtwo hB1 hB2
  exact ⟨B, hlower, hBtwo, hs0, hd0, hs1, hd1, hs2, hd2⟩

/-- If the doubling scale is at least twice the strict scale, the midpoint of
the strict plateau is already outside the doubling support. -/
theorem scaledCutoffs_plateau_vs_zero
    {aStrict aDouble : ℕ}
    (hsPos : 0 < aStrict)
    (hRatio : 2 * aStrict ≤ aDouble) :
    let qStar : ℝ := 1 / (2 * (aStrict : ℝ))
    SmoothCutoffs.scaledCutoff (aStrict : ℝ) qStar = 1 ∧
      SmoothCutoffs.scaledCutoff (aDouble : ℝ) qStar = 0 := by
  dsimp only
  have hsR : (0 : ℝ) < aStrict := by exact_mod_cast hsPos
  have hdPos : 0 < aDouble := by omega
  have hdR : (0 : ℝ) < aDouble := by exact_mod_cast hdPos
  have hprod :
      (aStrict : ℝ) * (1 / (2 * (aStrict : ℝ))) = 1 / 2 := by
    field_simp [ne_of_gt hsR]
  constructor
  · apply SmoothCutoffs.scaledCutoff_one_of_abs_le
    rw [hprod, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · apply SmoothCutoffs.scaledCutoff_zero_of_inv_le hdR
    have hRatioR : (2 : ℝ) * (aStrict : ℝ) ≤ (aDouble : ℝ) := by
      exact_mod_cast hRatio
    exact one_div_le_one_div_of_le
      (mul_pos (by norm_num) hsR) hRatioR

/-- The explicit stage-two schedules always satisfy the factor-two scale
separation needed by the plateau-vs-zero lemma. -/
theorem stage_two_cutoffs_plateau_vs_zero
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ)
    (hBtwo : 2 ≤ B)
    (hB1 : leastLocalScale C p g hg 0 1 < B)
    (hB2 : leastLocalScale C p g hg 0 2 < B) :
    let aStrict := minimalStrictSchedule C p g hg B
    let aDouble := canonicalSchedule C p g hg B
    let qStar : ℝ := 1 / (2 * (aStrict 2 : ℝ))
    SmoothCutoffs.scaledCutoff (aStrict 2 : ℝ) qStar = 1 ∧
      SmoothCutoffs.scaledCutoff (aDouble 2 : ℝ) qStar = 0 := by
  dsimp only
  obtain ⟨_, _, _, _, hs2, hd2⟩ :=
    first_three_schedule_values C p g hg B hBtwo hB1 hB2
  have hsPos : 0 < minimalStrictSchedule C p g hg B 2 := by
    rw [hs2]
    omega
  have hRatio :
      2 * minimalStrictSchedule C p g hg B 2 ≤
        canonicalSchedule C p g hg B 2 := by
    rw [hs2, hd2]
    omega
  exact scaledCutoffs_plateau_vs_zero hsPos hRatio

/-- Conditional P2b bridge. At the explicit plateau-vs-zero radius, any
nonzero raw stage forces the two cut stages to be genuinely different. -/
theorem cutStages_ne_of_raw_ne_at_plateau_zero
    {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {aStrict aDouble : ℕ → ℕ} {q : X → ℝ} {A : ℕ → X → V}
    {j : ℕ} {x : X}
    (hsPos : 0 < aStrict j)
    (hRatio : 2 * aStrict j ≤ aDouble j)
    (hq : q x = 1 / (2 * (aStrict j : ℝ)))
    (hA : A j x ≠ 0) :
    SolenoidalDiagonal.cutStage (fun k => (aDouble k : ℝ)) q A j x ≠
      SolenoidalDiagonal.cutStage (fun k => (aStrict k : ℝ)) q A j x := by
  obtain ⟨hsCut, hdCut⟩ :=
    scaledCutoffs_plateau_vs_zero hsPos hRatio
  intro heq
  simp only [SolenoidalDiagonal.cutStage, hq, hsCut, hdCut,
    zero_smul, one_smul] at heq
  exact hA heq.symm


/-- Projection form of the P2c gate. It is enough to certify one nonzero
continuous-linear observable of the raw stage at the explicit comparison
point; full raw-stage nonvanishing then follows automatically. This lets the
source audit target a distinguished component/Fourier/angular observable
instead of proving a vector-valued noncancellation statement directly. -/
theorem cutStages_ne_of_raw_projection_ne_at_plateau_zero
    {X V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {aStrict aDouble : ℕ → ℕ} {q : X → ℝ} {A : ℕ → X → V}
    {j : ℕ} {x : X}
    (π : V →L[ℝ] W)
    (hsPos : 0 < aStrict j)
    (hRatio : 2 * aStrict j ≤ aDouble j)
    (hq : q x = 1 / (2 * (aStrict j : ℝ)))
    (hπ : π (A j x) ≠ 0) :
    SolenoidalDiagonal.cutStage (fun k => (aDouble k : ℝ)) q A j x ≠
      SolenoidalDiagonal.cutStage (fun k => (aStrict k : ℝ)) q A j x := by
  apply cutStages_ne_of_raw_ne_at_plateau_zero hsPos hRatio hq
  intro hzero
  apply hπ
  rw [hzero]
  exact map_zero π


/-- Interior plateau-vs-zero comparison. The stronger scale ratio puts the
strict cutoff strictly inside its constant-one region and the doubling cutoff
strictly inside its constant-zero region. -/
theorem scaledCutoffs_interior_plateau_vs_zero
    {aStrict aDouble : ℕ}
    (hsPos : 0 < aStrict)
    (hRatio : 5 * aStrict < 2 * aDouble) :
    let qStar : ℝ := (2 / 5 : ℝ) / (aStrict : ℝ)
    SmoothCutoffs.scaledCutoff (aStrict : ℝ) qStar = 1 ∧
      SmoothCutoffs.scaledCutoff (aDouble : ℝ) qStar = 0 ∧
      SmoothCutoffs.scaledCutoff (aStrict : ℝ) =ᶠ[𝓝 qStar] (fun _ => 1) ∧
      SmoothCutoffs.scaledCutoff (aDouble : ℝ) =ᶠ[𝓝 qStar] (fun _ => 0) := by
  dsimp only
  have hsR : (0 : ℝ) < aStrict := by exact_mod_cast hsPos
  have hdPos : 0 < aDouble := by omega
  have hdR : (0 : ℝ) < aDouble := by exact_mod_cast hdPos
  have hsProd :
      (aStrict : ℝ) * ((2 / 5 : ℝ) / (aStrict : ℝ)) = 2 / 5 := by
    field_simp [ne_of_gt hsR]
  have hRatioR :
      (5 : ℝ) * (aStrict : ℝ) < 2 * (aDouble : ℝ) := by
    exact_mod_cast hRatio
  have hdProd :
      1 < (aDouble : ℝ) * ((2 / 5 : ℝ) / (aStrict : ℝ)) := by
    have heq :
        (aDouble : ℝ) * ((2 / 5 : ℝ) / (aStrict : ℝ)) =
          (2 * (aDouble : ℝ)) / (5 * (aStrict : ℝ)) := by
      field_simp [ne_of_gt hsR]
      <;> ring
    rw [heq]
    exact (lt_div_iff₀ (mul_pos (by norm_num) hsR)).2 hRatioR
  have hsAbs :
      |(aStrict : ℝ) * ((2 / 5 : ℝ) / (aStrict : ℝ))| < 1 / 2 := by
    rw [hsProd, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5)]
    norm_num
  have hdAbs :
      1 < |(aDouble : ℝ) * ((2 / 5 : ℝ) / (aStrict : ℝ))| := by
    rw [abs_of_pos]
    · exact hdProd
    · exact mul_pos hdR (div_pos (by norm_num) hsR)
  exact ⟨
    SmoothCutoffs.scaledCutoff_one_of_abs_le hsAbs.le,
    SmoothCutoffs.scaledCutoff_zero_of_one_le_abs hdAbs.le,
    SmoothCutoffs.scaledCutoff_eventually_one hsAbs,
    SmoothCutoffs.scaledCutoff_eventually_zero hdAbs⟩

/-- With floor at least four, the explicit stage-two schedules satisfy the
strong interior separation ratio. -/
theorem stage_two_cutoffs_interior_plateau_vs_zero
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ)
    (hBfour : 4 ≤ B)
    (hB1 : leastLocalScale C p g hg 0 1 < B)
    (hB2 : leastLocalScale C p g hg 0 2 < B) :
    let aStrict := minimalStrictSchedule C p g hg B
    let aDouble := canonicalSchedule C p g hg B
    let qStar : ℝ := (2 / 5 : ℝ) / (aStrict 2 : ℝ)
    SmoothCutoffs.scaledCutoff (aStrict 2 : ℝ) qStar = 1 ∧
      SmoothCutoffs.scaledCutoff (aDouble 2 : ℝ) qStar = 0 ∧
      SmoothCutoffs.scaledCutoff (aStrict 2 : ℝ) =ᶠ[𝓝 qStar] (fun _ => 1) ∧
      SmoothCutoffs.scaledCutoff (aDouble 2 : ℝ) =ᶠ[𝓝 qStar] (fun _ => 0) := by
  dsimp only
  have hBtwo : 2 ≤ B := by omega
  obtain ⟨_, _, _, _, hs2, hd2⟩ :=
    first_three_schedule_values C p g hg B hBtwo hB1 hB2
  have hsPos : 0 < minimalStrictSchedule C p g hg B 2 := by
    rw [hs2]
    omega
  have hRatio :
      5 * minimalStrictSchedule C p g hg B 2 <
        2 * canonicalSchedule C p g hg B 2 := by
    rw [hs2, hd2]
    omega
  exact scaledCutoffs_interior_plateau_vs_zero hsPos hRatio

/-- At the interior comparison point, every cut-stage jet is exactly the raw
stage jet for the strict schedule and exactly zero for the doubling schedule. -/
theorem cutStage_jets_interior_plateau_vs_zero
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {aStrict aDouble : ℕ → ℕ} {q : X → ℝ} {A : ℕ → X → V}
    {j : ℕ} {x : X}
    (hqcont : ContinuousAt q x)
    (hsPos : 0 < aStrict j)
    (hRatio : 5 * aStrict j < 2 * aDouble j)
    (hq : q x = (2 / 5 : ℝ) / (aStrict j : ℝ))
    (m : ℕ) :
    iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage (fun k => (aDouble k : ℝ)) q A j) x = 0 ∧
      iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage (fun k => (aStrict k : ℝ)) q A j) x =
          iteratedFDeriv ℝ m (A j) x := by
  obtain ⟨_, _, hsEv, hdEv⟩ :=
    scaledCutoffs_interior_plateau_vs_zero hsPos hRatio
  have hqt :
      Tendsto q (𝓝 x) (𝓝 ((2 / 5 : ℝ) / (aStrict j : ℝ))) := by
    simpa only [hq] using hqcont
  have hsComp :
      (fun y => SmoothCutoffs.scaledCutoff (aStrict j : ℝ) (q y))
        =ᶠ[𝓝 x] (fun _ => 1) :=
    hsEv.comp_tendsto hqt
  have hdComp :
      (fun y => SmoothCutoffs.scaledCutoff (aDouble j : ℝ) (q y))
        =ᶠ[𝓝 x] (fun _ => 0) :=
    hdEv.comp_tendsto hqt
  have hsStage :
      SolenoidalDiagonal.cutStage (fun k => (aStrict k : ℝ)) q A j
        =ᶠ[𝓝 x] A j := by
    filter_upwards [hsComp] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, one_smul]
  have hdStage :
      SolenoidalDiagonal.cutStage (fun k => (aDouble k : ℝ)) q A j
        =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hdComp] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, zero_smul]
  constructor
  · have hd :=
      (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hdStage m).self_of_nhds
    simpa using hd
  · exact
      (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hsStage m).self_of_nhds

/-- Jet form of P2c. Any nonzero raw-stage jet at the interior comparison
point forces the corresponding strict and doubling cut-stage jets to differ. -/
theorem cutStage_jets_ne_of_raw_jet_ne_at_interior_plateau_zero
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {aStrict aDouble : ℕ → ℕ} {q : X → ℝ} {A : ℕ → X → V}
    {j : ℕ} {x : X}
    (hqcont : ContinuousAt q x)
    (hsPos : 0 < aStrict j)
    (hRatio : 5 * aStrict j < 2 * aDouble j)
    (hq : q x = (2 / 5 : ℝ) / (aStrict j : ℝ))
    (m : ℕ)
    (hjet : iteratedFDeriv ℝ m (A j) x ≠ 0) :
    iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage (fun k => (aDouble k : ℝ)) q A j) x ≠
      iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage (fun k => (aStrict k : ℝ)) q A j) x := by
  obtain ⟨hd, hs⟩ :=
    cutStage_jets_interior_plateau_vs_zero
      hqcont hsPos hRatio hq m
  rw [hd, hs]
  exact fun he => hjet he.symm

end NavierStokes.V511StageTwoCutoffSeparation
