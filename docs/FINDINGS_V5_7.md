# v5.7 findings: force ancestry, native residual atoms, and the 9/10 frontier

## Executive result

v5.7 turns the force-ablation program into a source-locked dependency and residual-attribution problem against

`openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.

Three conclusions now matter most.

First, on the entire pre-singular interval the final smooth force is exactly the activated Navier-Stokes residual:

```text
0 <= t < 1

F(t,x)
  = navierStokesResidual
      (TimeLocalization.activatedVelocity u)
      (TimeLocalization.activatedPressure p)
      t x.
```

Second, the actual correction-cycle residual can be traced past the former `finite_residual_rates` opacity boundary to a first exact native five-channel decomposition:

```text
native residual
  = harmonic source sum
  + mean-good residual
  + excluded base error
  + excluded Gaussian error
  + excluded alias error.
```

Third, the v5.6 cutoff commutator is real but is already routed into the Gaussian excluded channel, which has all-power/flat control. It is therefore not the visible source of the finite primary `7/10` rate. A proof audit found unused linear-remainder slack and source-locked Lean has qualified the global and localized `9/10` remainder theorems, as well as nonlinear initialization propagation at `9/10`.

No force norm has been reduced and no unforced solution is claimed.

## 1. Exact final-force ancestry

The pinned source chain is

```text
ActualCandidateAssembly.Witness
  -> MixedCandidateWitness.exists_candidate_witness_of_finite_stages
  -> CandidateConsequences.mixed_exists_force_with_consequences
  -> MixedPeriodicAssembly.exists_candidate_force
  -> CandidateFromLimits.force.
```

Pinned `CandidateFromLimits.force_eq_activated_residual` gives, for `0 <= t < 1`,

```text
F = residual(activated velocity, activated pressure).
```

Taylor-Borel continuation is therefore a global smooth extension/gluing mechanism. It is not a separate source of pre-singular forcing.

## 2. Exact time-activation decomposition

Pinned `TimeLocalization.activated_residual_formula` proves, for `0 < t < 1`,

```text
R(chi u, chi p)
  = chi R(u,p)
    + chi' u
    + (chi^2-chi) (u dot grad)u.
```

Exactly three source-backed activation channels occur:

1. scaled incoming residual;
2. switch derivative `chi' u`;
3. nonlinear activation defect `(chi^2-chi)(u dot grad)u`.

Pinned `activated_residual_eq_late` proves that for `3/4 < t < 1`,

```text
R(activated u, activated p) = R(u,p).
```

Hence the activation-specific defects disappear arbitrarily close to blowup. Time activation remains relevant to global-in-time force norms, but is not the first terminal-force target.

## 3. Spatial localization remains a separate global layer

`MixedPeriodicAssembly` distinguishes

```text
originalResidual
cutResidual
periodicResidual.
```

The source proves only local/eventual identities:

- `periodicResidual_eventuallyEq_cut` in the periodic inner cube;
- `cutResidual_eventuallyEq_original` on the spatial-cutoff plateau.

These do not remove global spatial-cutoff or periodization cost. Local equality near the singular axis must not be promoted into a global force identity.

## 4. Exact bridge to the diagonal residual

Pinned `MixedDiagonalResidual.residual_eq_originalResidual` is definitional equality for the corresponding diagonal sums. Thus the incoming terminal force is tied exactly to the mixed diagonal residual architecture before spatial localization.

## 5. The former finite-stage opacity boundary has been crossed

`MixedCandidateAssembly.StageEstimates.finite_residual` is an aggregate JetRate obligation. The actual source fills it using

```text
ActualCycleResidualBounds.finite_residual_rates.
```

v5.7 traced that proof into the active-region residual identities instead of treating its imports as mechanisms.

The first exact native residual decomposition is

```text
R_native
  = R_harmonic_source
  + R_mean_good
  + E_base
  + E_gaussian
  + E_alias.
```

More concretely:

- harmonic source sum: the sum of `ActualCycleResidualBounds.source(x,l).oscillation`;
- mean-good term: `state.meanGoodResidual(context)`;
- excluded total: `base + gaussian + aliasError` from `CorrectionState.ExcludedErrors.total`.

The active/exterior split in the proof is regional gluing, not another additive force atom. On the exterior region the residual agrees locally with the final slow-base residual and is controlled by the all-power `GlobalBaseError` machinery.

## 6. Source-backed rate hierarchy of the five native channels

The current proof gives the following hierarchy.

### Harmonic source sum

Published finite gain:

```text
h * (1/2 + sigma).
```

This is the weakest visibly proved native gain among the five channels.

### Mean-good residual

Stronger native gain:

```text
h * (1 + sigma).
```

It is weakened only when combined with the harmonic source term.

### Base excluded error

Controlled to arbitrary requested power through the global-base error family.

### Gaussian excluded error

Controlled to arbitrary requested power / flat all-power scale.

### Alias excluded error

Also controlled to arbitrary requested power / flat all-power scale.

Therefore the harmonic source sum is the weakest *proved* native channel. This does not establish sharpness or norm dominance.

## 7. Reclassification of the v5.6 cutoff commutator

Pinned `CorrectionInitialization` gives the exact linear-primary identity

```text
R_primary,linear
  = R_constructedGood
  + E_cutoff.
```

The `excluded` field is the vector-mode form of `LinearWaveBounds.excludedSlotError`.

The key source connection is that `PrimaryResidualClass.gaussianCoefficients` is built from conjugate-pair `excludedSlotError`, and `ActualInitialization.initialResidualBlock` feeds a block whose harmonic residual subtracts Gaussian and alias coefficients before the finite-rate source is sent to the first particular solve.

So the cutoff-derived excluded field is explicitly represented as a Gaussian subtraction before the finite-rate harmonic source is formed.

### Decision

```text
cutoff commutator
  -> KEEP as an exact-force ablation target
  -> DEMOTE as the visible finite-rate bottleneck.
```

It is nonzero and still matters to a true zero-force objective, but the current proof already controls it in an all-power excluded channel.

## 8. Qualified 7/10 -> 9/10 linear improvement

The pinned `LinearWaveBounds` adapter packages the corrected linear remainder at

```text
alpha + 1/2 - 3*kappa.
```

For the actual primary values used by that local theorem,

```text
alpha = 1/2
kappa = 1/10
```

this yields `7/10`.

A term-by-term proof audit found that the visible primitive estimates support the stronger common target

```text
alpha + 1/2 - kappa
```

under the already-present hypothesis `kappa <= 1/2`:

- slow transport: at least `alpha + 1 - kappa`;
- phase defect: `alpha + 1/2`;
- base derivative: `alpha + 1`;
- pressure gradient: radial branch `alpha + 1/2 - kappa`;
- curl-principal: source class already preserves `alpha + 1/2 - kappa` before an unnecessary extra weakening;
- viscous part: after the epsilon factor, `alpha + 1/2 - kappa`.

Thus at the actual local parameters the sharpened target is

```text
1/2 + 1/2 - 1/10 = 9/10.
```

### Formal status

Source-locked Lean PASS:

- Stage F: improved global linear remainder at `9/10`;
- Stage H: localized retained-good theorem at `9/10`.

This is a real proof sharpening, not a changed PDE construction.

## 9. Nonlinear initialization does not clip 9/10

Pinned `ActualInitialization.zeroMean_residual_uniform` requires

```text
gamma <= 2*alpha - kappa.
```

For the actual initialization values this ceiling is above `9/10`.

Pinned `CorrectionStep.meanStage_residual_uniform` likewise allows the `9/10` target with the actual mean-increment exponent.

### Formal status

Source-locked Lean PASS:

- Stage G: nonlinear residual propagation at `9/10`;
- Stage J: actual initial mean supports the proposed `sigma = 2/5` target.

Still unqualified because of source-wiring failures rather than numerical contradictions:

- Stage I: complete three-gate invariant promotion;
- Stage K: complete actual initial debt promotion;
- Stage L: composition all the way to the literal actual-primary coefficient block.

Those failures must not be advertised as theorem failures of the rate itself.

## 10. Shifted-sigma interpretation

The source correction ledger is

```text
sigma(J) = 1/5 + J/10.
```

Historically `7/10 = 1/2 + sigma(0)`. A `9/10` initial residual numerically corresponds to

```text
1/2 + 2/5 = 9/10 = 1/2 + sigma(2).
```

This suggests a possible two-rung head start, but stronger residual alone is not enough. `CycleAnalyticInvariant` contains additional sigma-dependent fields. Until every field is promoted, correction cycles cannot be skipped.

This route is now secondary to v5.8, where a larger source-visible physical-stage margin was found without changing the analytic state sequence.

## 11. What v5.7 changed strategically

The priority order is now:

1. **Harmonic finite-rate channel:** primary rate-analysis target.
2. **Physical-stage gain bookkeeping:** inspect whether published adapters discard source-visible exponent margin.
3. **Spatial localization / periodization:** retain as independent global force-attribution layer.
4. **Cutoff commutator:** exact-force ablation target, but not current finite-rate bottleneck.
5. **Time activation:** low priority for terminal forcing, still relevant to global force norms.
6. **Taylor-Borel continuation:** low priority for pre-singular force ablation.

This directly motivated the v5.8 program: test whether the *unchanged* physical stages admit a stronger common diagonal gain before changing the analytic correction sequence.

## Kill rules

- imports are not residual terms;
- a JetRate upper bound is not an additive decomposition;
- weakest proved exponent is not automatically a sharp asymptotic bottleneck;
- all-power/flat smallness is not exact zero;
- vanishing endpoint jets do not imply zero residual for `t < 1`;
- local equality on a cutoff plateau is not global equality;
- a stronger residual rate does not by itself prove a stronger full invariant;
- a stronger diagonal gain does not by itself imply a smaller final force norm;
- no correction cycle may be skipped until every invariant field is requalified.

## Claim boundary

v5.7 does **not** reduce an actual force norm, construct a modified singular candidate, prove that the harmonic rate is sharp, or establish unforced Navier-Stokes blowup.

The concrete advance is narrower and stronger: the final-force ancestry is source-locked, the first exact native residual atoms are identified, the cutoff commutator has been correctly reclassified, and the linear/nonlinear proof stack contains formally verified `9/10` slack that motivates the next physical-stage audit.
