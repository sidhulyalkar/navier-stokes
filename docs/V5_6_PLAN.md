# v5.6.0 plan: cutoff residual atlas + one-pulse no-cutoff continuation

## Goal

Replace the broad phrase “remove pulse forcing” with an exact sequence of source-backed counterfactuals.

The v5.5 audit established that the canonical primary is already homogeneous and zero-forcing inside its native pulse interval. v5.6 asks precisely what fails when its temporal localization is removed.

## A. Compile the localization residual

Pinned `LinearWaveBounds.excludedSlotError` gives

```text
E_slot = Dfast(psi) * amplitude + (1-psi) * source.
```

This creates two distinct channels:

1. **cutoff derivative / commutator**: `Dfast(psi) * amplitude`;
2. **uncovered source**: `(1-psi) * source`.

For the primary residual class, `source=0`, so only the cutoff derivative channel remains.

The actual native cutoff is a product of clock and Gaussian-slot localizers. By the product rule, its derivative splits again into clock and slot commutators. Each atom must retain its own support, asymptotic status, source declaration, and evidence level.

## B. Exact `psi=1` counterfactual

In the principal cutoff identity, if the uncut coefficient satisfies

```text
principal = -source
```

then setting `psi=1` yields

```text
excludedSlotError = 0.
```

This is local algebra, not a global PDE result.

The useful question becomes:

> Where does the source stop proving that the uncut coefficient satisfies the same dynamics and geometry?

## C. First obstruction: finite-interval dynamics validity

`PrimaryODE.solution` is represented as an `R -> State` object by a differentiable extension of the finite-interval Volterra solution.

However, `PrimaryODE.solution_hasDerivAt` proves the ODE only when

```text
v in Icc(a,b).
```

For the source primary pulse this native interval is the pulse slot, reparametrized as `Icc(0,L)` in `PrimaryPulseBounds`.

Therefore simply deleting the cutoff and reusing the existing differentiable extension is invalid as a proof of global homogeneous dynamics.

### First v5.6 blocker

```text
DYNAMICS_SCOPE:
prove the same coefficient/frame/kinematic hypotheses on an enlarged interval
and solve the homogeneous ODE there directly.
```

## D. Enlarged-interval candidate

For one pulse label:

1. choose `[a',b']` with `[a,b]` strictly inside it;
2. extend the actual frame/coefficient inputs to `[a',b']`;
3. prove continuity/smoothness and kinematic nondegeneracy there;
4. solve the homogeneous ODE directly on `[a',b']`;
5. use uniqueness to prove agreement with the canonical primary on `[a,b]`;
6. set the temporal slot cutoff to one on the enlarged interval;
7. recompute every remaining residual channel;
8. only after the one-pulse case survives, introduce a second pulse.

## Kill criteria

Kill this lineage if any of the following is source-backed and unavoidable:

- moving-frame or coefficient denominators become singular before reaching a neighboring slot;
- the phase/carrier geometry leaves its admissible domain;
- agreement with the canonical pulse is impossible under homogeneous uniqueness;
- removing localization creates a non-Gaussian residual channel at an unabsorbable order;
- two-pulse nonlinear interactions overwhelm the Gaussian tail separation.

## Promotion criteria

Promote to v5.7 finite-hierarchy analysis only if:

- one pulse has an enlarged source-backed homogeneous interval;
- the principal localization error vanishes there exactly;
- all newly exposed non-principal residuals are enumerated;
- every surviving residual has a valid cancellation or sufficiently strong bound;
- no claim relies on treating a flat error as zero.

## Parallel h-track

Continue the selected-parameter dependency audit, but deprioritize generic axis estimates already generalized upstream to the manuscript `h<=1/100` range. The target is the first genuinely selected downstream theorem that still consumes the tighter `h<=1/1000` regime.

## Claim boundary

v5.6 does not remove the actual OpenAI force and does not construct an unforced singularity. Its intended scientific output is the exact first obstruction or first successful enlarged-interval continuation for a single canonical homogeneous pulse.
