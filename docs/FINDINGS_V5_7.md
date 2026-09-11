# v5.7 findings: trace the final force before optimizing it

## Executive result

v5.7 changes the force-ablation program from a hand-written taxonomy into a source-locked dependency problem.

On the pinned OpenAI source

`openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`,

the final smooth force satisfies an exact identity on the entire pre-singular physical interval:

```text
0 <= t < 1

F(t,x)
  = navierStokesResidual
      (TimeLocalization.activatedVelocity u)
      (TimeLocalization.activatedPressure p)
      t x.
```

The Taylor-Borel/gluing construction makes this residual into a global smooth, compact-future-time force. It is not a separate source of forcing on `0 <= t < 1`.

This gives a canonical attribution route:

```text
final smooth force
      ↓ exact on 0 <= t < 1
activated Navier-Stokes residual
      ↓ exact activation identity
incoming periodic residual + activation defects
      ↓ localization / periodization
cut residual
      ↓ local plateau identity
original mixed residual
      ↓ definitional equality for diagonal sums
MixedDiagonalResidual.residual
      ↓ aggregate StageEstimates obligation
finite-prefix residual rate
      ↓ actual producer
ActualCycleResidualBounds.finite_residual_rates
```

The last theorem is the current mechanism-attribution frontier.

## 1. Exact time-activation decomposition

Pinned `TimeLocalization.activated_residual_formula` proves, for `0 < t < 1`,

```text
R(chi u, chi p)
  = chi R(u,p)
    + chi' u
    + (chi^2-chi) (u dot grad)u.
```

So the time switch creates exactly three source-backed channels:

1. the incoming residual multiplied by the switch;
2. the switch-derivative term `chi' u`;
3. the nonlinear activation defect `(chi^2-chi)(u dot grad)u`.

This is stronger than our earlier generic statement that “time localization creates forcing,” because it exposes the exact algebraic atoms.

## 2. Terminal-quarter simplification

Pinned `TimeLocalization.activated_residual_eq_late` proves that for

```text
3/4 < t < 1
```

the activated velocity and pressure agree locally with the incoming fields and therefore

```text
R(activated u, activated p) = R(u,p).
```

Consequently the two activation-specific defects are absent arbitrarily close to the blowup time.

### Research consequence

If the immediate objective is to reduce the force that survives into the singular regime, optimizing the initial time switch is not the first target.

It may still matter for a global norm such as an integral over the whole time interval, but it does not explain the terminal forcing.

## 3. Spatial localization must remain a separate attribution layer

`MixedPeriodicAssembly` gives three distinct residuals:

```text
originalResidual
cutResidual
periodicResidual
```

The source proves:

- `periodicResidual_eventuallyEq_cut` only near points in the periodic inner cube;
- `cutResidual_eventuallyEq_original` only on the spatial-cutoff plateau.

These are local/eventual equalities, not global identities.

Therefore the global cost of spatial cutoff derivatives and periodization remains an open force channel. It is not legitimate to remove this layer from the DAG merely because the fields agree on the interior region containing the singular axis.

## 4. Exact connection to the diagonal residual

Pinned `MixedDiagonalResidual.residual_eq_originalResidual` is definitional equality:

```text
MixedDiagonalResidual.residual a q A B P
  = MixedPeriodicAssembly.originalResidual
      (potentialSum a q A)
      (potentialSum a q B)
      (potentialSum a q P).
```

This is the clean bridge from the final incoming force to the scale-diagonal correction architecture.

## 5. The finite-stage opacity boundary

The final candidate assembly does not carry a list of force atoms.

`MixedCandidateAssembly.StageEstimates` instead contains the aggregate field

```text
finite_residual : forall J m,
  JetRate ...
    (navierStokesResidual
      (MixedDiagonalResidual.uncutVelocity A B J)
      (uncutPrefix P (J+1)))
    m
    (gain J - residualLoss m)
```

The actual iteration fills this field in `ActualStageEstimates.stageEstimates_of_representations` via

```text
ActualCycleResidualBounds.finite_residual_rates.
```

Thus neither the final assembly nor its actual-stage adapter provides the mechanism-level additive split we ultimately need.

### Current frontier

```text
ActualCycleResidualBounds.finite_residual_rates
```

The pinned module imports and uses machinery including:

- `PhysicalResidualJetBounds`;
- `ActualInitialExcluded`;
- `GaugeExcludedBounds`;
- `GlobalBaseError`;
- the correction-cycle invariant and iteration ledger;
- carrier and polar-coverage geometry.

Those dependencies are clues, not force atoms. v5.7 must inspect the proof and intermediate residual identities before promoting any of them into the final-force taxonomy.

## 6. Current priority order

### 1. Finite-prefix residual producer: PROMOTE

Unpack `ActualCycleResidualBounds.finite_residual_rates` until the first exact additive residual identity is reached.

This path remains relevant on `3/4 < t < 1`, so success directly informs the force present near singularity.

### 2. Spatial localization / periodization cost: PROMOTE FOR ATTRIBUTION

Derive a global residual-difference identity or bound outside the plateau and inner cube. Do not assume this cost is dominant.

### 3. Time activation: DEPRIORITIZE FOR TERMINAL FORCE

Its source-specific defects vanish after `t > 3/4`.

### 4. Taylor-Borel continuation: DEPRIORITIZE FOR PRE-SINGULAR ABLATION

It is essential for the globally smooth force witness, but on `0 <= t < 1` the force is already exactly the activated residual.

## 7. Next concrete experiment

Trace the proof of `ActualCycleResidualBounds.finite_residual_rates` declaration-by-declaration and produce a first source-backed residual ledger of the form

```text
finite prefix residual
    = exact identity term A
    + exact identity term B
    + ...
```

or, if the proof never exposes an equality, a dependency ledger of independently bounded contributions:

```text
contribution
  source theorem
  support
  native exponent
  physical stage exponent
  derivative loss
  cancellation partner
  terminal-region status
```

The first contribution that has an independent expression and bound becomes the first legitimate mechanism-level `ForceAtom`.

## Kill rules

- imports are not residual terms;
- a JetRate upper bound is not an additive decomposition;
- vanishing endpoint jets do not imply zero residual for `t<1`;
- local equality on a cutoff plateau is not global equality;
- Gaussian smallness is not exact cancellation;
- no numerical priority score is allowed until comparable source-backed quantities exist.

## Claim boundary

No force norm has been reduced. No modified singular candidate has been constructed. No unforced Navier-Stokes blowup is claimed.

The concrete v5.7 progress is that the final-force ancestry is now source-locked down to one precise theorem frontier, and the terminal-region force has been separated from early-time activation artifacts.
