import NavierStokes.V580ActualBoostedCandidate

/-!
# v5.8 actual witness assembled from the boosted finite-stage certificate

This file checks the downstream consumer boundary.  It feeds the boosted
finite-stage record for the literal actual fields into the same
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` theorem used
by `ActualCandidateAssembly.witness`.

All support, endpoint-extension and axis-zero-germ inputs are the pinned source
proofs.  The physical stage sequences are unchanged.

A successful compile means the existing mixed-diagonal/candidate assembly can
consume the stronger gain certificate without reverting to the published gain.
It does not prove the selected schedule is strictly smaller and does not prove
a smaller final forcing norm.
-/

noncomputable section

namespace NavierStokes.V580ActualBoostedWitness

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

/-- The same literal actual candidate witness can be assembled while using the
v5.8 boosted finite-stage certificate as the quantitative input. -/
theorem witness (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualCandidateAssembly.Witness B N0 hN :=
  GermCandidateAssembly.exists_candidate_witness_of_finite_stages
    certificate modulation upper B
    (ActualCandidateConstruction.qbig_pos B N0)
    (ActualCandidateAssembly.initialPotential B N0)
    (ActualCandidateAssembly.positivePotential B N0 hN)
    (ActualCandidateAssembly.directData B N0 hN)
    (ActualCandidateAssembly.initialPressure B N0)
    (ActualCandidateAssembly.positivePressure B N0 hN)
    (V580ActualBoostedCandidate.estimates B N0 hN)
    (ActualCandidateAssembly.initialPotential_support B N0)
    (ActualCandidateAssembly.positivePotential_support B N0 hN)
    (ActualCandidateAssembly.directStages_support B N0 hN)
    (ActualCandidateAssembly.initialPressure_support B N0)
    (ActualCandidateAssembly.positivePressure_support B N0 hN)
    (ActualCandidateAssembly.endpoints B N0 hN).potential
    (ActualCandidateAssembly.endpoints B N0 hN).direct
    (ActualCandidateAssembly.endpoints B N0 hN).pressure
    (ActualCandidateAssembly.initialPotential_axisZeroOn B N0)
    (ActualCandidateAssembly.positivePotential_axisZeroOn B N0 hN)

/-- The pinned closed parameter choice therefore reaches the ordinary candidate
statement through the boosted quantitative certificate. -/
theorem selected_candidate : ProblemStatement.candidateStatement := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ :=
    witness ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry
  exact ⟨_, _, forcing, hc⟩

end NavierStokes.V580ActualBoostedWitness
