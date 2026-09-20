# Current research status

Last updated: 2026-09-20 (America/Los_Angeles)

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
| M2 | advanced/active | prove mechanisms unnecessary or unavoidable |
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

The deletion is source-locked through the full candidate chain:

1. numerical selector: `34785230674`;
2. finite heterogeneous cutoff bounds: `34785248912`;
3. physical local-q support and smooth zero extension: `34936977665`;
4. mixed three-component schedule: `34937994783`;
5. mixed residual vanishing: `34938088599`;
6. final singular-candidate replay: `35299948373`.

The final replay uses the same finite-stage fields and downstream force constructor while omitting the factor-two schedule-growth certificate. This proves factor-two growth is unnecessary for that forced singular-candidate construction. It does **not** order force norms.

### v5.10 strict selector separation

For any requested initial floor `lower`, Lean proves there exists a common admissible `B >= lower` for which

```text
minimalStrictSchedule(..., B, 0) = canonicalSchedule(..., B, 0)
minimalStrictSchedule(..., B, 1) < canonicalSchedule(..., B, 1).
```

Qualified audit: `35372821347`.

Thus deleting doubling can produce genuinely different schedule geometry. This does not by itself imply the physical fields differ.

### v5.11 controlled paired construction

The active v5.11 lane now derives **both** strict and doubling schedules from one shared finite-stage certificate. The two constructions use the same raw potential/direct/pressure fields, gain/loss functions, cutoff constants/log powers, physical support floor, finite background, and finite residual data. Only the recursive schedule rule differs.

Qualified source-locked layers:

- paired finite cutoff bounds: `35373687768`;
- paired physical local-q bounds: `35477742215`;
- paired mixed three-component schedule: `35477742195`;
- paired mixed residual vanishing: `35477742200`;
- literal `MixedCandidateAssembly.StageEstimates` paired adapter: `35478105331`;
- paired cutoff-collar support geometry: `35477647249`.

The paired construction preserves

```text
aStrict(0) = aDouble(0)
aStrict(1) < aDouble(1)
aStrict(j) <= aDouble(j)  for every j
```

while both mixed residuals retain vanishing endpoint jets.

### v5.11 explicit stage-two plateau-vs-zero separation

A stronger geometry theorem is now qualified at audit `35532572140`.

Choose the common floor above the first two positive-stage least local scales and with `B >= 2`. The first values become exactly

```text
strict:   B, B+1, B+2
doubling: B, 2B,  4B
```

so `2*aStrict(2) <= aDouble(2)`. At

```text
q* = 1 / (2*aStrict(2))
```

the pinned cutoff satisfies exactly

```text
scaledCutoff(aStrict(2), q*) = 1
scaledCutoff(aDouble(2), q*) = 0.
```

The same module proves the precise conditional P2b bridge:

```text
raw stage nonzero at x
+ q(x) = q*
=> strict and doubling cut stages differ at x.
```

This removes uncertainty about the scalar cutoff profile. The remaining physical-distinction obligation is a source-backed nonzero actual raw-stage witness at such a point, or another observable proving the paired assembled fields/residuals are nonidentical.

## Active qualification

### Late presingular force bridge

`formal/V511LateForceResidualBridge.lean` proves the intended local identity on the late-time spatial plateau:

```text
CandidateFromLimits.force
= MixedPeriodicAssembly.originalResidual
```

for `3/4 < t < 1` on the spatial plateau.

The first audit failed only by Lean elaboration timeout after the pinned dependency closure built. The theorem was rewritten with explicit local abbreviations and pointwise equality steps. Re-audit `35532300046` is active; do not treat this bridge as qualified until that dedicated run is green.

## Exact current bottlenecks

### P2b: schedule separation is not yet field separation

The pinned source has strong one-way support theorems such as `ActualMeanStageData.innerRadius_le_of_ne`: if an actual coefficient is nonzero, it must lie in the permitted annulus. The current audit has **not** found a theorem guaranteeing that a selected positive-stage field is nonzero at the explicit paired comparison radius.

Therefore do not infer physical field inequality from schedule inequality alone.

A promising indirect route is the source's nonzero leading-stress theorem, but its nontriviality still must be transported through realization data to an actual paired positive-stage field or another physical observable.

### P3: existing cut-stage estimates erase scale dependence

The pinned exact scalar chain rule retains

```text
D^n[cutoff(a*q)] = a^n * cutoff^(n)(a*q).
```

But `CutStageEstimates.cutoff_jet_bound` deliberately replaces the scale power by a scale-uniform `q^{-n}` bound. Consequently the published `CutStageBounds` are excellent existence estimates but cannot order two cutoff schedules quantitatively.

The next quantitative bridge must retain the explicit `a^n` factors through composition and Leibniz estimates on the paired collar.

## Next chain

```text
qualify late-time force = original residual bridge
        ↓
close P2b with a nonzero actual-stage/observable witness
        ↓
derive scale-retaining cutoff + product jet bounds
        ↓
use ResidualCalculus.navierStokesResidual_add_sub
        ↓
compare the exact six residual-difference terms
        ↓
terminal force observable
        ↓
standard force-norm comparison
```

The source-native residual identity already gives

```text
R(u+e,p+q) - R(u,p)
 = temporalDerivative e
 - spatialLaplacian e
 + pressureGradient q
 + spatialDerivative u(e)
 + spatialDerivative e(u)
 + spatialDerivative e(e).
```

No new Navier–Stokes algebra should be invented for P3.

## Blocked secondary experiment

The pinned exponent ledger exposes a candidate common positive-stage margin

```text
h * (3/5-kappa) = 59999/100000 * h,
kappa = 1/100000.
```

Several low-level v5.8 statements qualified, but the literal boosted `StageEstimates`/actual-candidate adapter did not. Audit `34784642131` failed on incorrect pinned-source interface assumptions.

Do not describe the full boosted actual candidate as proved.

## Claim boundary

Established:

- canonical schedule comparison and strict-crossing infrastructure;
- factor-two growth is unnecessary through the final forced singular-candidate assembly;
- strict and doubling schedules can be paired from identical finite-stage data;
- both paired schedules retain the source-compatible cutoff, smoothness, and endpoint-flat residual conclusions;
- the paired scalar cutoffs can be made explicitly plateau-vs-zero separated at stage two.

Not established:

- a source-backed theorem that the paired actual physical fields are nonidentical;
- an ordering of the paired collar residuals;
- a smaller final force in any standard norm;
- force norm tending to zero;
- unforced Navier–Stokes singularity.

## Active GitHub tracks

- **#17** paired strict-vs-doubling candidates and collar residual comparison, primary lane.
- **#14** broader quantitative force-size bridge and norm hierarchy.
- **#13** common gain slack, blocked/secondary until its literal source adapter is redesigned.
- **#15** factor-two schedule necessity, closed/completed.
