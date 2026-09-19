import NavierStokes.CutStageEstimates
import NavierStokes.V511PairedFiniteCutBounds

/-!
# v5.11: paired physical local cutoff bounds

This extends the paired strict-vs-doubling construction through the physical
local-`q` validity region and the source's smooth zero-extension argument.

The two schedules are produced by one call to
`V511PairedFiniteCutBounds.exists_paired_finite_cut_bounds`, so the raw stage
fields and the aggregated cutoff constants are shared.  The only fork remains
the recursive envelope:

* minimal strict growth;
* source-style factor-two doubling growth.

Both schedules obey the same `qbig` support floor, both yield the same type of
physical positive-stage cutoff bounds, and both produce smooth diagonal sums on
preterminal spacetime.

No residual or force ordering is asserted here.
-/

noncomputable section

namespace NavierStokes.V511PairedPhysicalLocalCutBounds

open Set Function Filter
open V511PairedFiniteCutBounds
open scoped Topology ContDiff BigOperators

variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Paired physical local-q cutoff schedules from identical analytic data.
Both schedules satisfy the source-compatible local support and smooth
zero-extension conclusions; they agree at stage zero and are strictly
separated at stage one. -/
theorem exists_paired_physical_local_cut_bounds {h qbig : ℝ}
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
    ∃ aStrict aDouble : ℕ → ℕ,
      lower ≤ aStrict 0 ∧
      lower ≤ aDouble 0 ∧
      (∀ j, 0 < aStrict j) ∧
      (∀ j, 0 < aDouble j) ∧
      StrictMono aStrict ∧
      StrictMono aDouble ∧
      Tendsto (fun j => (aStrict j : ℝ)) atTop atTop ∧
      Tendsto (fun j => (aDouble j : ℝ)) atTop atTop ∧
      (∀ j, 2 * aDouble j ≤ aDouble (j + 1)) ∧
      (∀ j, 1 / (aStrict j : ℝ) < qbig) ∧
      (∀ j, 1 / (aDouble j : ℝ) < qbig) ∧
      aStrict 0 = aDouble 0 ∧
      aStrict 1 < aDouble 1 ∧
      (∀ j, aStrict j ≤ aDouble j) ∧
      ∀ i,
        (DiagonalJetBounds.CutStageBounds (fun j => (aStrict j : ℝ))
          (PhysicalWaveSum.physicalQ h)
          (CutStageEstimates.positiveStages (A i))
          (fun j => g j / 2) (CutStageEstimates.cutLoss L) S ∧
        ContDiffOn ℝ ∞
          (SolenoidalDiagonal.potentialSum (fun j => (aStrict j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages (A i)))
          PhysicalWaveSum.preterminal) ∧
        (DiagonalJetBounds.CutStageBounds (fun j => (aDouble j : ℝ))
          (PhysicalWaveSum.physicalQ h)
          (CutStageEstimates.positiveStages (A i))
          (fun j => g j / 2) (CutStageEstimates.cutLoss L) S ∧
        ContDiffOn ℝ ∞
          (SolenoidalDiagonal.potentialSum (fun j => (aDouble j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages (A i)))
          PhysicalWaveSum.preterminal) := by
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h)
      PhysicalWaveSum.preterminal :=
    fun w hw =>
      (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt
  have hU := CutStageEstimates.physicalSublevel_open hh hh1 qbig
  choose B hB hb using CutStageEstimates.physicalQ_jet_bound hh hh1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hqbig
  obtain ⟨aStrict, aDouble,
      hsLower, hdLower,
      hsPos, hdPos,
      hsMono, hdMono,
      hsTop, hdTop,
      hdGrowth,
      hEq0, hLt1, hOrder,
      hsLocal, hdLocal⟩ :=
    exists_paired_finite_cut_bounds hU
      (S := S ∩ CutStageEstimates.physicalSublevel h qbig)
      (fun _ hw => hw.2)
      (hq.mono inter_subset_left)
      (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1)
      B (fun k w hw hq1 => hb k w hw.2.1 hq1)
      hA g L C p hraw hg (max lower (n + 1))

  have hrecipStrict : ∀ j, 1 / (aStrict j : ℝ) < qbig := by
    intro j
    have haj : n + 1 ≤ aStrict j :=
      ((le_max_right lower (n + 1)).trans hsLower).trans
        (hsMono.monotone (Nat.zero_le j))
    have hle : 1 / (aStrict j : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast haj)
    exact hle.trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

  have hrecipDouble : ∀ j, 1 / (aDouble j : ℝ) < qbig := by
    intro j
    have haj : n + 1 ≤ aDouble j :=
      ((le_max_right lower (n + 1)).trans hdLower).trans
        (hdMono.monotone (Nat.zero_le j))
    have hle : 1 / (aDouble j : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast haj)
    exact hle.trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

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

  have hsExtended := extendOne aStrict hsPos hsTop hrecipStrict hsLocal
  have hdExtended := extendOne aDouble hdPos hdTop hrecipDouble hdLocal

  refine ⟨aStrict, aDouble,
    (le_max_left lower (n + 1)).trans hsLower,
    (le_max_left lower (n + 1)).trans hdLower,
    hsPos, hdPos, hsMono, hdMono, hsTop, hdTop, hdGrowth,
    hrecipStrict, hrecipDouble, hEq0, hLt1, hOrder, ?_⟩
  intro i
  exact ⟨hsExtended i, hdExtended i⟩

end NavierStokes.V511PairedPhysicalLocalCutBounds
