# Current research status

Last updated: 2026-09-18 (America/Los_Angeles)

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

Six layers are now qualified:

1. **Numerical selector**: positive, strictly monotone, divergent, reciprocal tends to zero, preserves all local admissibility, pointwise no larger than the source doubling envelope. Audit `34785230674`.
2. **Finite heterogeneous cutoff bounds**: the source-style analytic cutoff-bound theorem survives using the weaker schedule. Audit `34785248912`.
3. **Physical local-q support and smooth zero extension**: the gain-independent support floor, positive-stage cut bounds, and smooth preterminal extension survive without factor-two growth. Audit `34936977665`.
4. **Mixed three-component schedule**: the same potential/direct/pressure families admit one common strict schedule with the same common loss and smooth full sums, without factor-two growth. Audit `34937994783`.
5. **Mixed residual vanishing**: the physical mixed residual still has vanishing joint jets using the weaker schedule. Audit `34938088599`.
6. **Final singular-candidate replay**: the pinned final candidate proof has been replayed with the same finite-stage fields and downstream force constructor while omitting the factor-two schedule-growth certificate. Audit `35299948373`.

### v5.10 strict selector separation

Source-locked Lean proves that positive-stage least local scales are independent of the stage-zero floor. More strongly, for **any requested initial floor** `lower`, there exists a common admissible `B >= lower` such that

```text
minimalStrictSchedule(..., B, 0) = canonicalSchedule(..., B, 0)
minimalStrictSchedule(..., B, 1) < canonicalSchedule(..., B, 1).
```

Qualified audit: `35372821347`.

Thus the selector change can produce genuinely different localization geometry while accommodating an arbitrary gain-independent support floor. This is an existence result in the chosen floor; it does **not** prove strict separation for the source/default `lower = 1`.

Next chain:

```text
paired strict/doubling schedules from identical Kall/Pall and raw fields
        ↓
exact collar-residual difference
        ↓
source-compatible residual/force observable
        ↓
standard force-norm comparison
```

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
- factor-two growth is unnecessary through the numerical selector, finite heterogeneous cutoff estimates, physical local-q zero extension, mixed three-component schedule, mixed residual vanishing, and the final forced singular-candidate assembly;
- for any required initial floor, a common admissible floor can be chosen so the minimal strict and doubling selectors are genuinely separated at stage 1.

Not established:

- strict separation for the source/default `lower = 1` schedule;
- any ordering of the paired collar residuals yet;
- smaller final force in any standard norm;
- force norm tending to zero;
- unforced Navier–Stokes singularity.

## Active GitHub tracks

- **#17** paired strict-vs-doubling candidates and collar residual comparison, primary lane.
- **#14** broader quantitative force-size bridge and norm hierarchy.
- **#13** common gain slack, blocked/secondary until its literal source adapter is redesigned.
- **#15** factor-two schedule necessity, closed as completed after the final-candidate replay and strict-separation result.
