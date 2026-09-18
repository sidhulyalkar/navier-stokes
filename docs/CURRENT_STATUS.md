# Current research status

Last updated: 2026-09-17 (America/Los_Angeles)

This is the canonical short status page. Historical `FINDINGS_V5_*` files remain useful audit trails, but active claims should be checked here first.

## Reproducibility lock

- Upstream: `openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`
- Lean: `leanprover/lean4:v4.34.0-rc2`
- Reference result: smooth **forced** finite-time Navier–Stokes singularity construction. This repository does not claim unforced Navier–Stokes blowup.

## Milestones

| Milestone | Status | Meaning |
|---|---|---|
| M0 | complete | reproduce/source-lock reference construction |
| M1 | advanced | source-level force/residual attribution |
| M2 | active | prove mechanisms unnecessary or unavoidable |
| M3 | open | singular witness with strictly smaller forcing in a stated norm |
| M4 | open | singular family with force norm tending to zero |
| M5 | open | stable limiting construction |
| M6 | open | unforced `f=0` singular construction |

## Qualified formal results

### v5.9 canonical schedule comparison

Source-locked Lean establishes:

- deterministic least-admissible local integer cutoff scales;
- canonical schedule monotonicity under stronger gain;
- strict integer-threshold crossing criteria;
- a criterion for local strictness to survive the source doubling envelope; and
- constant-cancelling scale relaxation without assigning numerical values to opaque multiplicative constants.

Qualified audit: `34784849248`.

### v5.10 factor-two growth deletion

The source schedule enforces

```text
a(n+1) = max(local(n+1), 2*a(n)).
```

v5.10 uses the weaker minimal strict envelope

```text
s(0)   = max(1, local(0))
s(n+1) = max(local(n+1), s(n)+1).
```

Three layers are now qualified:

1. **Numerical selector**: positive, strictly monotone, divergent, reciprocal tends to zero, preserves all local admissibility, pointwise no larger than the source doubling envelope. Audit `34785230674`.
2. **Finite heterogeneous cutoff bounds**: the source-style analytic cutoff-bound theorem survives using the weaker schedule. Audit `34785248912`.
3. **Physical local-q support and smooth zero extension**: the gain-independent support floor, positive-stage cut bounds, and smooth preterminal extension survive without factor-two growth. Audit `34936977665`.

Next chain:

```text
mixed three-component strict schedule
        ↓
vanishing mixed residual jets
        ↓
parallel final singular-candidate theorem
        ↓
old-vs-new collar residual comparison
        ↓
standard force-norm comparison
```

Source audit strongly suggests the residual/final layers consume `Tendsto`, monotonicity, support separation, smooth sums, extension data, residual vanishing, angular divergence, and blowup, not the factor-two witness. This is evidence, not yet an end-to-end theorem.

## Blocked secondary experiment

The pinned exponent ledger exposes a candidate common positive-stage margin

```text
h * (3/5-kappa) = 59999/100000 * h,
kappa = 1/100000.
```

Several low-level v5.8 statements qualified, but the literal boosted `StageEstimates`/actual-candidate adapter did not. Audit `34784642131` failed on incorrect pinned-source interface assumptions, including a nonexistent residual projection and unresolved record-field identities.

Do not describe the full boosted actual candidate as proved.

## Claim boundary

Established:

- canonical schedule comparison and strict-crossing infrastructure;
- constant-cancelling cutoff-scale comparison;
- factor-two growth is unnecessary through the numerical selector, finite heterogeneous cutoff estimates, and physical local-q zero-extension layer.

Not established:

- end-to-end final singular candidate without factor-two growth;
- smaller final force in any standard norm;
- force norm tending to zero;
- unforced Navier–Stokes singularity.

## Active GitHub tracks

- **#15** factor-two schedule growth elimination, primary lane.
- **#14** quantitative force-size bridge after a genuinely changed physical witness is qualified.
- **#13** common gain slack, blocked/secondary until its literal source adapter is redesigned.
