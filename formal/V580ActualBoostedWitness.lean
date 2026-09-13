import NavierStokes.V580ActualBoostedCandidate

/-!
# v5.8 witness assembled from the boosted finite-stage certificate

This file checks the downstream consumer boundary.  It feeds the boosted
finite-stage record for the exact literal stage families into the same
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` theorem used
by `ActualCandidateAssembly.witness`.

All support, endpoint-extension and axis-zero-germ inputs are the pinned source
proofs.  The physical stage sequences are unchanged.

Important claim boundary: `ActualCandidateAssembly.Witness` existentially
quantifies the integer diagonal schedule.  Therefore a successful compile does
not identify the newly assembled final sums (or force) with a previously chosen
source witness.  It shows that the same literal stage construction admits an
assembled candidate through the stronger quantitative certificate.  It does
not prove that the selected schedule is strictly smaller and does not prove a
smaller final forcing norm.
-/

noncomputable section

namespace NavierStokes.V580ActualBoostedWitness

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

/-- The exact literal stage families admit a candidate witness when the v5.8
boosted finite-stage certificate is used as the quantitative input.  The
existential schedule produced here need not equal the schedule produced by the
source witness theorem. -/
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
statement through the boosted quantitative certificate.  This is an existence
statement; it does not compare the resulting force with the source witness. -/
theorem selected_candidate : ProblemStatement.candidateStatement := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ :=
    witness ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry
  exact ⟨_, _, forcing, hc⟩

end NavierStokes.V580ActualBoostedWitness
