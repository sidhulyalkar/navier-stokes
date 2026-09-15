# Current research status

Last updated: 2026-09-14 (America/Los_Angeles)

This file is the canonical short status page. Historical findings remain in versioned `FINDINGS_V5_*` documents, but active claims should be checked here first.

## Reproducibility lock

- Upstream source: `openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`
- Lean: `leanprover/lean4:v4.34.0-rc2`
- The OpenAI result under study is a smooth **forced** finite-time singularity construction for the forced Navier–Stokes problem. This repository does not claim an unforced Navier–Stokes singularity.

## Research objective

Determine which forcing/localization mechanisms in the pinned construction are structurally necessary, which are proof architecture, and whether any removable mechanism leads to a quantitatively smaller final force.

Milestone ladder:

| Milestone | Status | Meaning |
|---|---|---|
| M0 | complete | reproduce and source-lock the reference construction |
| M1 | advanced | trace final force/residual mechanisms to source-level atoms |
| M2 | active | prove mechanisms unnecessary or unavoidable |
| M3 | open | construct a singular witness with strictly smaller forcing in a stated norm |
| M4 | open | singular family with force norm tending to zero |
| M5 | open | stable limiting construction |
| M6 | open | unforced `f = 0` singular construction |

## Qualified formal results

### v5.9: canonical cutoff-scale comparison

Source-locked Lean establishes a deterministic least-admissible local integer scale and canonical schedule comparison. Increasing the certified gain cannot worsen the canonical cutoff schedule.

The strict crossing criterion is also formalized: strict local scale improvement occurs exactly when a smaller integer becomes admissible under the stronger gain, and an explicit condition determines when that improvement survives the recursive envelope.

A constant-cancelling comparison theorem removes dependence on opaque multiplicative cutoff constants. A stronger gain can certify a smaller integer scale by comparing reciprocal power budgets directly against an already-admissible weak scale.

Qualified audit: `34784849248`.

### v5.10: factor-two schedule growth is unnecessary for the numerical selector

The source uses

```text
a(n+1) = max(local(n+1), 2*a(n)).
```

v5.10 defines the weaker strict envelope

```text
s(0)   = max(1, local(0))
s(n+1) = max(local(n+1), s(n)+1).
```

Lean proves that the new schedule:

- dominates every local admissible scale;
- is positive and strictly monotone;
- tends to infinity;
- has reciprocal scale tending to zero;
- preserves all numerical local admissibility inequalities; and
- is pointwise no larger than the source doubling envelope.

Qualified audit: `34785230674`.

### v5.10: finite heterogeneous cut bounds survive without factor-two growth

The source's finite-family cutoff estimates for heterogeneous potential/direct/pressure-style components have been rebuilt using the minimal strict schedule. The analytic cutoff-bound layer therefore does not require `2*a(j) <= a(j+1)`.

Qualified audit: `34785248912`.

## Active qualification

`formal/V510PhysicalLocalStrictCutBounds.lean` extends the same deletion through the actual local-`q` validity region and smooth zero-extension argument. A dedicated pinned CI gate is running before this result is promoted.

If it qualifies, the next sequence is:

```text
local-q strict cut bounds
        ↓
three-component mixed schedule
        ↓
vanishing mixed residual jets
        ↓
parallel final-candidate theorem without factor-two growth
        ↓
quantitative collar/force comparison
```

Source audit already shows that the residual theorem and final force assembly consume `Tendsto`, positivity/monotonicity, support separation, smooth sums, extension data and residual vanishing; the factor-two witness is carried by the existing API but is not visibly used by those final calls. This is evidence for the v5.10 hypothesis, not yet an end-to-end theorem.

## Blocked / non-promoted experiment

### v5.8 common physical gain slack

The pinned exponent ledger exposes a candidate common positive-stage margin

```text
h * (3/5 - kappa) = 59999/100000 * h,
```

with `kappa = 1/100000`.

Several low-level gain/slack theorems qualified, but the attempted literal `StageEstimates`/actual-candidate adapter did **not** qualify. Audit `34784642131` failed while reconstructing the exact pinned source interface, including a nonexistent `CycleAnalyticInvariant.residual_jetRate` projection and record-field identity mismatches.

Therefore the project must not describe the full boosted actual candidate as proved. The source-visible gain slack remains an interesting quantitative lead, but v5.10 is the cleaner active M2 lane.

## Claim boundary

Established here:

- source-locked mechanism attribution for several force/residual channels;
- canonical schedule monotonicity and strict crossing criteria;
- constant-cancelling cutoff-scale comparison;
- a formally qualified minimal strict schedule that removes factor-two growth from the numerical selector;
- formally qualified finite heterogeneous cutoff bounds using that weaker schedule.

Not established:

- end-to-end singular candidate with factor-two growth removed;
- any ordering of the old and new final forcing fields in a standard norm;
- any strictly smaller final force norm;
- any force norm tending to zero;
- any unforced Navier–Stokes singularity.

## Active GitHub tracks

- Issue #15: factor-two diagonal schedule growth elimination, primary active lane.
- Issue #14: quantitative force-size bridge, resumes once a genuinely changed singular witness is source-locked.
- Issue #13: v5.8 common gain slack, retained as a blocked/secondary experiment until its literal adapter is repaired or replaced.
