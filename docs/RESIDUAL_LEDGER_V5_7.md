# v5.7 Exact Residual Ledger

Pinned source: `openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`

This note records the source-backed decomposition reached during v5.7. It deliberately separates the **physical residual definition** from the **harmonic extraction representation**. Conflating those two layers leads to false force atoms.

## 1. Definition-level normalized physical residual

`HarmonicResidual.stateFullResidual` is definitionally the sum of three physical pieces:

1. the real nonlinear differential residual of the state perturbation;
2. `contextVirtual`, the virtual-stress divergence term;
3. the fixed base-error field.

Schematically,

```text
R_state
  = R_differential
  + R_virtual
  + E_base.
```

`HarmonicResidual.nonlinearResidual` itself is `linearResidual + transport(a,a)`.

`contextVirtual` is explicitly

```text
[0,
 -radialDiv(2, virtualTheta),
 -radialDiv(1, virtualAxial)].
```

Gaussian and alias errors do **not** appear as independent summands in this definition.

## 2. Exact harmonic reconstruction of the same residual

`ActualCycleResidualBounds.Invariant.fullResidual_decomposition` reconstructs the same full residual locally as

```text
R_state
  = sum_l R_harmonic(l)
  + R_mean_good
  + E_total,
```

where `CorrectionState.ExcludedErrors.total` is definitionally

```text
E_total = E_base + E_gaussian + E_alias.
```

Thus one can also write

```text
R_state
  = sum_l R_harmonic(l)
  + R_mean_good
  + E_base
  + E_gaussian
  + E_alias.
```

This second equality is an **extraction/reconstruction ledger**, not five independent physical forcing mechanisms.

### Why Gaussian and alias are paired bookkeeping

Inside `HarmonicResidual.LabelData.residualCoefficients`, the Gaussian and alias coefficients are subtracted from each label's harmonic residual before the nonconstant harmonic part is taken. The stored Gaussian/alias error fields are later restored through `ExcludedErrors.total`, with the angular mean equation providing the corresponding mean cancellation.

Therefore an ablation that deletes only the restored Gaussian or alias field is invalid: it breaks the exact reconstruction unless the matching subtraction path is changed too.

The v5.7 machine-readable ledger consequently marks both as:

```text
physical_force_atom = false
independently_ablatable = false
```

## 3. Native exponent ledger

`ActualCycleResidualBounds.Invariant.native_residual` combines the above channels before physical-chart conversion.

The source-backed native gains are structurally different:

| channel | native gain before common weakening | implication |
|---|---:|---|
| harmonic source sum | `h*(1/2 + sigma)` | candidate bottleneck |
| selected mean-good residual | `h*(1 + sigma)` | stronger by `h/2` |
| base error | arbitrary `h*alpha` via `baseError_native` | all-power input |
| Gaussian bookkeeping | arbitrary finite power from `gaussianFlat` | not bottleneck at this ledger |
| alias bookkeeping | arbitrary finite power from `axisFlat` | not bottleneck at this ledger |

The proof weakens the stronger channels to a common target before invoking the physical chart estimate. Consequently the **harmonic residual sum is the unique native exponent bottleneck visible in this source layer**.

This is an exponent statement, not a numerical force-norm ranking.

## 4. Connection to the v5.7 `9/10` initializer audit

The source's existing initializer packages the primary linear-good/residual estimate at `7/10`. The v5.7 source-locked Lean audit has now qualified both:

- the global linear-remainder sharpening;
- the localized retained-good sharpening;

at the stronger target

```text
alpha + 1/2 - kappa.
```

For the actual primary parameters

```text
alpha = 1/2
ChartScales.kappa = 1/10,
```

this is

```text
9/10.
```

This matters because the residual ledger independently identifies the harmonic source as the native `1/2 + sigma` bottleneck. A successful promotion of the *literal* initial invariant from `sigma=1/5` to `sigma=2/5` would therefore improve the channel that actually sets the native residual exponent.

It would not merely improve an unused bookkeeping field.

## 5. Conditional physical-rate consequence

`ActualIterationLedger` gives

```text
sigma(J) = 1/5 + J/10
gain(h,J) = h*J/10 = h*(sigma(J)-1/5)
residualWave(J) = J/10 + 7/10.
```

The existing finite residual proof first obtains a stronger physical-chart residual rate and then weakens it using `gain_le_residualWave`.

If the same literal state can be requalified with

```text
sigma' = sigma + 1/5,
```

and the stronger invariant can be fed to `ResidualChartData.residual_jetRate` with the same physical loss, the candidate improvement is exactly

```text
Delta(native harmonic exponent) = h/5
Delta(physical residual exponent) = h/5.
```

That bridge is **not yet proved**.

## 6. What v5.7 does not claim

The following remain false / unpromoted:

- Gaussian or alias is an independent physical-force mechanism.
- A numerical fraction of the final force has been assigned to any residual atom.
- Two correction cycles have been deleted.
- The final global forcing norm is smaller.
- The spatial localization / periodization cost has been globally quantified.
- The time-activation cost has been removed.
- An unforced Navier-Stokes singularity has been constructed.

## 7. Next exact frontier

The next attribution target is no longer the aggregate theorem `finite_residual_rates`.

It is:

> Bind each per-label harmonic `residualBlock` to the literal correction-stage mechanisms that generated it, then carry any genuine additive split through spatial localization, periodization, time activation, and the final force construction.

Unknown subterms remain `UNKNOWN`; guessed labels are not promoted into the force DAG.
