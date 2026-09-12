# v5.6 findings: removing the cutoff moves the problem into dynamics scope

## Executive result

v5.6 converts the first pulse-localization ablation into an exact source-backed counterfactual.

The general excluded-slot residual is

```text
Dfast(psi) * amplitude + (1-psi) * source.
```

For the canonical primary residual class, the source argument is exactly zero. Therefore its excluded-slot residual is only the cutoff-derivative commutator.

If `psi=1` and the underlying uncut coefficient continues to satisfy its principal solve, that particular localization error vanishes exactly.

The source then exposes the first obstruction: the existing primary is constructed from a finite-interval Volterra solution. It is packaged as a differentiable function on all real slot times, but the theorem proving the ODE is scoped to `v in Icc(a,b)`. For the primary pulse, the native control interval is `Icc(0,L)`.

So deleting the cutoff does not produce a source-backed global homogeneous pulse. A new enlarged-interval solve is required.

## 1. Exact localization residual taxonomy

Pinned `LinearWaveBounds.excludedSlotError` has two channels.

### A. Cutoff derivative commutator

```text
Dfast(psi) * amplitude
```

This is present whenever the temporal/fast cutoff changes. For the Gaussian slot cutoff its derivative lies in the source-backed off-plateau region and is Gaussian-small.

### B. Uncovered source

```text
(1-psi) * source
```

This matters for source-driven particular solves. It disappears in the primary residual class because that class passes `source=0` into `excludedSlotError`.

Treating these as distinct atoms matters: a no-cutoff construction can eliminate the commutator while simultaneously changing which source equation must hold globally.

## 2. Product cutoff split

The actual native localization combines a clock window and Gaussian slot cutoff. For

```text
psi = chi_clock * chi_slot
```

the derivative channel splits algebraically as

```text
Dfast(chi_clock) * chi_slot * amplitude
+ chi_clock * Dfast(chi_slot) * amplitude.
```

For a source-driven solve the third atom remains

```text
(1-chi_clock*chi_slot) * source.
```

The v5.6 atlas records these atoms separately with source/support/evidence metadata.

## 3. What `psi=1` actually proves

Under the source solve hypothesis

```text
principal = -source,
```

`LinearWaveBounds.principal_cutoff_of_solve` identifies the post-cutoff principal residual with `excludedSlotError`.

Therefore, if the same uncut coefficient is valid and `psi=1`, then

```text
Dfast(1) * amplitude + (1-1) * source = 0.
```

This is a genuine exact simplification.

But its scope is local to the principal-wave identity. It says nothing by itself about:

- whether the source coefficient/frame remains admissible outside the original slot;
- whether the homogeneous ODE is solved there;
- curl/pressure/remainder channels;
- nonlinear interactions with other pulses;
- spatial/global localization;
- the final full Navier-Stokes residual.

## 4. First one-pulse obstruction

Pinned `PrimaryODE` says the constructed solution is a finite-interval Volterra solution with a differentiable extension.

The extension is an `R -> State` function. However, the source theorem

```text
solution_hasDerivAt
```

requires

```text
v in Icc(a,b).
```

`PrimaryPulseBounds` specializes the primary analysis to `Icc(0,L)`.

Hence:

```text
function defined outside slot      PASS
ODE identity inside native slot    PASS
ODE identity outside native slot   OPEN
```

The first exact blocker is therefore **dynamics scope**, not function existence or seed amplitude.

## 5. Correct next construction

The right next candidate is not “use the old extension without cutoff.” It is:

1. choose a larger interval `[a',b']`;
2. prove the actual frame/coefficient and kinematic hypotheses on that larger interval;
3. solve the homogeneous ODE directly there;
4. prove agreement with the canonical primary on the old interval by uniqueness;
5. remove the temporal cutoff on the enlarged interval;
6. recompute all non-principal residual channels;
7. only after one pulse survives, introduce a second pulse.

This is much harder than deleting a multiplier, but it is now a precise mathematical target.

## 6. Research strategy critique

### What is working

The source compiler is beginning to pay for itself. It corrected two earlier framings:

- the primary pulse did not need a new forcing mechanism inside its slot;
- the fixed-fraction Gaussian-tail condition was already formalized in the source.

The project is now using source identities to kill or redirect hypotheses before investing in large simulations or formalization.

### What remains weak

The automated discovery side is still much more mature as infrastructure than as mathematics. It can rank scaling candidates and encode residual mechanisms, but it has not yet generated a genuinely new profile, stress cone, or singular PDE construction.

Version numbers have also historically moved faster than theorem-level progress. v5.5 introduced release metadata checks; v5.6 continues the rule that each release should contain at least one source-backed scientific narrowing, not just tooling.

### What deserves compute next

The highest-value next computation is a theorem-by-theorem **enlarged-interval feasibility map** for one primary pulse. This should precede any infinite hierarchy, neural search, or expensive numerical campaign.

## Decision

```text
reuse existing differentiable extension as global homogeneous pulse: KILL
solve a new enlarged-interval homogeneous primary: PROMOTE
jump directly to infinite pulse hierarchy: HOLD / DEPRIORITIZE
claim actual force reduction: REJECT
```

## Claim boundary

No actual forcing norm has been reduced. No global no-cutoff pulse has been constructed. No unforced Navier-Stokes singularity has been proved.
