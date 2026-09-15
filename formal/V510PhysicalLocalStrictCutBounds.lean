import NavierStokes.CutStageEstimates
import NavierStokes.V510FiniteStrictCutBounds

/-!
# v5.10: physical local strict cut bounds

This mirrors the pinned source theorem
`CutStageEstimates.exists_physical_local_diagonal_cut_bounds` while removing
only the factor-two growth field from the selected schedule.

The source's local-q support requirement is gain-independent: choose `n` with
`1/(n+1) < qbig`, raise the initial floor to `max lower (n+1)`, and then use
monotonicity of the selected schedule to keep every cutoff strictly inside the
raw stage's valid `q < qbig` region. Smooth zero extension outside that region
uses positivity and the support gap, not factor-two growth.

No force-norm claim is made here.
-/

noncomputable section

namespace NavierStokes.V510PhysicalLocalStrictCutBounds

open Set Function Filter ProblemStatement
open V510FiniteStrictCutBounds
open scoped Topology ContDiff BigOperators

variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Exact physical local-q source interface with factor-two schedule growth
removed. -/
theorem exists_physical_local_strict_cut_bounds {h qbig : ℝ}
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
    ∃ a : ℕ → ℕ,
      lower ≤ a 0 ∧
      (∀ j, 0 < a j) ∧
      StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      ∀ i,
        DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
          (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages (A i))
          (fun j => g j / 2) (CutStageEstimates.cutLoss L) S ∧
        ContDiffOn ℝ ∞
          (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
            (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages (A i)))
          PhysicalWaveSum.preterminal := by
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h)
      PhysicalWaveSum.preterminal :=
    fun w hw =>
      (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt
  have hU := CutStageEstimates.physicalSublevel_open hh hh1 qbig
  choose B hB hb using CutStageEstimates.physicalQ_jet_bound hh hh1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hqbig
  obtain ⟨a, halower, hapos, hamono, hatop, hab⟩ :=
    exists_finite_strict_cut_bounds hU
      (S := S ∩ CutStageEstimates.physicalSublevel h qbig)
      (fun _ hw => hw.2)
      (hq.mono inter_subset_left)
      (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1)
      B (fun k w hw hq1 => hb k w hw.2.1 hq1)
      hA g L C p hraw hg (max lower (n + 1))
  have hrecip : ∀ j, 1 / (a j : ℝ) < qbig := by
    intro j
    have haj : n + 1 ≤ a j :=
      ((le_max_right lower (n + 1)).trans halower).trans
        (hamono.monotone (Nat.zero_le j))
    have hle : 1 / (a j : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast haj)
    exact hle.trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
  have hgap : ∀ j, 1 < (a j : ℝ) * qbig := by
    intro j
    have hp : (0 : ℝ) < a j := by exact_mod_cast hapos j
    simpa only [mul_comm] using (div_lt_iff₀ hp).mp (hrecip j)
  refine ⟨a, (le_max_left lower (n + 1)).trans halower,
    hapos, hamono, hatop, hrecip, fun i => ⟨?_, ?_⟩⟩
  · intro j hj m hm w hw
    by_cases hu : w ∈ CutStageEstimates.physicalSublevel h qbig
    · exact CutStageEstimates.positiveStages_cut_bounds (hab i)
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

end NavierStokes.V510PhysicalLocalStrictCutBounds
