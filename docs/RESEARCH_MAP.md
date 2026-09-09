# Research map

This document is the live conceptual map of the project. It is organized by mechanisms and decision gates rather than by software versions.

## Reference mechanism

```text
anisotropic concentrating base
        ↓
annular residual / stress demand
        ↓
oscillatory wave families
        ↓
mean covariance realizes stress
        ↓
mean + moment corrections
        ↓
iterative residual improvement
        ↓
flat residual near singular time
        ↓
localization / globalization
        ↓
final smooth force
        ↓
finite-time singular behavior
```

The research program asks which arrows can be replaced, compressed, or generalized.

## Track A: initial-data pulse transfer

### Hypothesis
Late pulse seeding can be replaced by extremely small components already encoded in the true initial data.

### Current evidence
- The source formalization contains a Gaussian envelope theorem for pulse growth/decay in slot time.
- A machine-readable source map exists at `artifacts/v530/pulse_tail_source_map.json`.

### Decision chain

```text
A1 source Gaussian envelope        [SOURCE_EXTRACTED]
          ↓
A2 derive slot length ℓ(k_n)       [OPEN]
          ↓
A3 derive γ_tail interval          [OPEN]
          ↓
A4 bound inverse propagator        [OPEN]
          ↓
A5 derive δ_back interval          [OPEN]
          ↓
A6 compare exponents/coefficients  [OPEN]
          ↓
A7 all-Sobolev/Gevrey summability  [BLOCKED]
          ↓
A8 nonlinear pulse interactions    [BLOCKED]
          ↓
A9 exact unforced residual closure [BLOCKED]
```

### Kill conditions
- certified backward amplification asymptotically dominates tail suppression;
- pulled-back hierarchy fails the required smoothness or energy class;
- nonlinear cross-pulse interactions recreate a non-summable residual.

## Track B: similarity-parameter margin

### Hypothesis
Part of the gap between the elementary `h < 1/6` window and the concrete formalized `h ≤ 1/1000` choice is proof bookkeeping rather than structural necessity.

### Decision chain

```text
B1 cheap balance h < 1/6               [REPRODUCED]
          ↓
B2 manuscript small-h regime            [SOURCE]
          ↓
B3 NaturalAxisData h ≤ 1/1000           [SOURCE_EXTRACTED]
          ↓
B4 enumerate direct consumers           [ACTIVE]
          ↓
B5 build downstream dependency DAG      [OPEN]
          ↓
B6 classify each constraint             [OPEN]
          ↓
B7 relax one local constant at a time   [BLOCKED]
          ↓
B8 determine certified admissible range [BLOCKED]
```

Constraint classes:

- `STRUCTURAL`: changing it breaks a mechanism or theorem in an essential way.
- `SUFFICIENT_CONSTANT`: a convenient quantitative choice with visible slack.
- `INHERITED`: copied from an upstream assumption without independently consuming the margin.
- `UNKNOWN`: source dependence located but mathematical necessity unresolved.

## Track C: forcing decomposition

Before optimizing the actual force, the final residual must be decomposed into mechanism-level contributions.

Target decomposition:

```text
f = f_base
  + f_pulse_seed
  + f_mean
  + f_localization
  + f_exterior
  + f_terminal
```

For each component we want:

- provenance;
- support geometry;
- asymptotic order;
- `L¹_t L²_x`, `L²_t L^{3/2}_x`, and `L∞` observables where meaningful;
- replacement mechanisms;
- exact residual consequences of deletion.

This track remains blocked until the source construction is quantitatively compiled far enough to evaluate the actual fields.

## Track D: stress-cone optimization

The oscillatory families realize a required mean stress through positive coefficients.

For a target stress `T` and covariance columns `H_i`, solve

```text
T = Σ_i a_i H_i,    a_i ≥ 0.
```

The important quantity is not only feasibility but robustness margin. A future evaluator should optimize an interior-cone margin while preserving profile and residual constraints.

Potential payoff:

- identify wave families with more tolerance;
- simplify the correction architecture;
- discover analogous realizable-stress constructions in MHD/Boussinesq/Hall-MHD.

## Track E: cross-PDE mechanism compiler

Once the Navier–Stokes reference is encoded quantitatively, reuse the grammar on neighboring systems.

Priority order:

1. Euler, because the source project already provides an unforced blowup construction and therefore a nearby comparison class.
2. Boussinesq, because coupling can introduce additional amplification/stress channels.
3. MHD, where Maxwell stress supplies a natural second quadratic transport mechanism.
4. Hall-MHD / generalized dissipative systems, where the balance grammar changes more substantially.

## Research resource allocation

Agents should be allocated according to information gain, not only apparent probability of success.

High-value tasks include:

- proving a route impossible;
- locating the first genuinely binding inequality;
- converting a qualitative statement into a source-backed interval;
- finding two apparently different proof steps that are manifestations of the same mechanism.

A useful failure shrinks the hypothesis space. That is progress.
