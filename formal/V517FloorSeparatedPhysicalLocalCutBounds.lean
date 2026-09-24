import NavierStokes.CutStageEstimates
import NavierStokes.V517FloorSeparatedFiniteCutBounds

/-!
# v5.17: physical local-q bounds for floor-separated schedules

Lift the finite common-data comparison through the pinned physical local-q
support and smooth zero-extension argument.  The two canonical schedules use
the same raw fields and analytic constants, but start at floors B and 3B.

Both schedules therefore have physical positive-stage cut bounds and smooth
locally finite sums on preterminal spacetime, while retaining the strict
stage-zero interior separation used by v5.16.
-/

noncomputable section

namespace NavierStokes.V517FloorSeparatedPhysicalLocalCutBounds

open Set Function Filter ProblemStatement
open V517FloorSeparatedFiniteCutBounds
open scoped Topology ContDiff BigOperators

variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

theorem exists_floor_separated_physical_local_cut_bounds
    {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A : ∀ i, ℕ → SpaceTime → W i}
    (hA : ∀ i j, 1 ≤ j →
      ContDiffOn ℝ ∞ (A i j) (CutStageEstimates.physicalSublevel h qbig))
    (g L : ℕ → ℝ) (C p : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, CutStageEstimates.RawStageBounds
      (PhysicalWaveSum.physicalQ h) (A i) g L (C i) (p i)
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ Bsmall Blarge : ℕ, ∃ aSmall aLarge : ℕ → ℕ,
      lower ≤ Bsmall ∧
      1 ≤ Bsmall ∧
      Blarge = 3 * Bsmall ∧
      (∀ j, 0 < aSmall j) ∧
      (∀ j, 0 < aLarge j) ∧
      StrictMono aSmall ∧
      StrictMono aLarge ∧
      Tendsto (fun j => (aSmall j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aLarge j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aSmall j ≤ aSmall (j + 1)) ∧
      (∀ j, 2 * aLarge j ≤ aLarge (j + 1)) ∧
      (∀ j, 1 / (aSmall j : ℝ) < qbig) ∧
      (∀ j, 1 / (aLarge j : ℝ) < qbig) ∧
      aSmall 0 = Bsmall ∧
      aLarge 0 = Blarge ∧
      5 * aSmall 0 < 2 * aLarge 0 ∧
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) < qbig ∧
      ∀ i,
        (DiagonalJetBounds.CutStageBounds (fun j => (aSmall j : ℝ))
          (PhysicalWaveSum.physicalQ h)
          (CutStageEstimates.positiveStages (A i))
          (fun j => g j / 2) (CutStageEstimates.cutLoss L) S ∧
        ContDiffOn ℝ ∞
          (SolenoidalDiagonal.potentialSum (fun j => (aSmall j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages (A i)))
          PhysicalWaveSum.preterminal) ∧
        (DiagonalJetBounds.CutStageBounds (fun j => (aLarge j : ℝ))
          (PhysicalWaveSum.physicalQ h)
          (CutStageEstimates.positiveStages (A i))
          (fun j => g j / 2) (CutStageEstimates.cutLoss L) S ∧
        ContDiffOn ℝ ∞
          (SolenoidalDiagonal.potentialSum (fun j => (aLarge j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages (A i)))
          PhysicalWaveSum.preterminal) := by
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h)
      PhysicalWaveSum.preterminal :=
    fun w hw =>
      (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt
  have hU := CutStageEstimates.physicalSublevel_open hh hh1 qbig
  choose Bq hBq hbq using CutStageEstimates.physicalQ_jet_bound hh hh1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hqbig

  obtain ⟨Bsmall, Blarge, aSmall, aLarge,
      hBLower, hBOne, hBLarge,
      hsPos, hlPos, hsMono, hlMono,
      hsTop, hlTop, hsGrowth, hlGrowth,
      hs0, hl0, hRatio, hsLocal, hlLocal⟩ :=
    exists_floor_separated_finite_cut_bounds hU
      (S := S ∩ CutStageEstimates.physicalSublevel h qbig)
      (fun _ hw => hw.2)
      (hq.mono inter_subset_left)
      (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1)
      Bq (fun k w hw hq1 => hbq k w hw.2.1 hq1)
      hA g L C p hraw hg (max lower (n + 1))

  have hLower : lower ≤ Bsmall :=
    (le_max_left lower (n + 1)).trans hBLower
  have hnB : n + 1 ≤ Bsmall :=
    (le_max_right lower (n + 1)).trans hBLower

  have hsRecip : ∀ j, 1 / (aSmall j : ℝ) < qbig := by
    intro j
    have h0j : aSmall 0 ≤ aSmall j :=
      hsMono.monotone (Nat.zero_le j)
    have hBaj : Bsmall ≤ aSmall j := by simpa only [hs0] using h0j
    have hnaj : n + 1 ≤ aSmall j := hnB.trans hBaj
    have hle : 1 / (aSmall j : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast hnaj)
    exact hle.trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

  have hlRecip : ∀ j, 1 / (aLarge j : ℝ) < qbig := by
    intro j
    have h0j : aLarge 0 ≤ aLarge j :=
      hlMono.monotone (Nat.zero_le j)
    have hBsmallLarge : Bsmall ≤ Blarge := by
      rw [hBLarge]
      omega
    have hBaj : Blarge ≤ aLarge j := by simpa only [hl0] using h0j
    have hnaj : n + 1 ≤ aLarge j :=
      hnB.trans (hBsmallLarge.trans hBaj)
    have hle : 1 / (aLarge j : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast hnaj)
    exact hle.trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

  have hqStar :
      (2 / 5 : ℝ) / (aSmall 0 : ℝ) < qbig := by
    have hs0pos : (0 : ℝ) < aSmall 0 := by exact_mod_cast hsPos 0
    have hfrac :
        (2 / 5 : ℝ) / (aSmall 0 : ℝ) <
          1 / (aSmall 0 : ℝ) := by
      apply div_lt_div_of_pos_right (by norm_num) hs0pos
    exact hfrac.trans (hsRecip 0)

  have extendOne :
      ∀ (a : ℕ → ℕ),
        (∀ j, 0 < a j) →
        Tendsto (fun j => (a j : ℝ)) atTop atTop →
        (∀ j, 1 / (a j : ℝ) < qbig) →
        (∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
          (PhysicalWaveSum.physicalQ h) (A i)
          (fun j => g j / 2) (CutStageEstimates.cutLoss L)
          (S ∩ CutStageEstimates.physicalSublevel h qbig)) →
        ∀ i,
          DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages (A i))
            (fun j => g j / 2) (CutStageEstimates.cutLoss L) S ∧
          ContDiffOn ℝ ∞
            (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
              (PhysicalWaveSum.physicalQ h)
              (CutStageEstimates.positiveStages (A i)))
            PhysicalWaveSum.preterminal := by
    intro a hapos hatop hrecip hlocal i
    have hgap : ∀ j, 1 < (a j : ℝ) * qbig := by
      intro j
      have hp : (0 : ℝ) < a j := by exact_mod_cast hapos j
      simpa only [mul_comm] using (div_lt_iff₀ hp).mp (hrecip j)
    constructor
    · intro j hj m hm w hw
      by_cases hu : w ∈ CutStageEstimates.physicalSublevel h qbig
      · exact CutStageEstimates.positiveStages_cut_bounds (hlocal i)
          j hj m hm w ⟨hw, hu⟩
      · have hlarge : qbig ≤ PhysicalWaveSum.physicalQ h w :=
          le_of_not_gt (fun hsmall => hu ⟨hS hw, hsmall⟩)
        have hp : (0 : ℝ) < a j := by exact_mod_cast hapos j
        have hz := CutStageEstimates.cut_product_eventually_zero
          (PhysicalWaveSum.physicalQ_smoothAt hh hh1 (hS hw)).continuousAt
          (CutStageEstimates.positiveStages (A i) j) (a j)
          ((hgap j).trans_le (mul_le_mul_of_nonneg_left hlarge hp.le))
        have hjz :=
          (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hz m).self_of_nhds
        change ‖iteratedFDeriv ℝ m
          (fun z => SmoothCutoffs.scaledCutoff (a j)
            (PhysicalWaveSum.physicalQ h z) •
            CutStageEstimates.positiveStages (A i) j z) w‖ ≤ _
        rw [hjz, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        exact mul_nonneg (by positivity)
          (Real.rpow_nonneg
            (PhysicalWaveSum.physicalQ_pos hh hh1 (hS hw)).le _)
    · have hstage : ∀ j, ContDiffOn ℝ ∞
          (SolenoidalDiagonal.cutStage (fun j => (a j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages (A i)) j)
          PhysicalWaveSum.preterminal := by
        intro j
        exact CutStageEstimates.cut_product_smooth_of_sublevel
          PhysicalWaveSum.preterminal_open hq
          (CutStageEstimates.positiveStages_smooth (hA i) j)
          (by change (0 : ℝ) < (a j : ℝ); exact_mod_cast hapos j)
          (hgap j)
      intro w hw
      have hloc := SolenoidalDiagonal.eventually_zero_tail hatop
        (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).continuousAt
        (PhysicalWaveSum.physicalQ_pos hh hh1 hw)
        (CutStageEstimates.positiveStages (A i))
      exact (DiagonalJetBounds.tsum_jet_identity hloc
        (fun j =>
          (hstage j).contDiffAt
            (PhysicalWaveSum.preterminal_open.mem_nhds hw))).1.contDiffWithinAt

  have hsExtended := extendOne aSmall hsPos hsTop hsRecip hsLocal
  have hlExtended := extendOne aLarge hlPos hlTop hlRecip hlLocal

  exact ⟨Bsmall, Blarge, aSmall, aLarge,
    hLower, hBOne, hBLarge,
    hsPos, hlPos, hsMono, hlMono, hsTop, hlTop,
    hsGrowth, hlGrowth, hsRecip, hlRecip,
    hs0, hl0, hRatio, hqStar,
    fun i => ⟨hsExtended i, hlExtended i⟩⟩

end NavierStokes.V517FloorSeparatedPhysicalLocalCutBounds
