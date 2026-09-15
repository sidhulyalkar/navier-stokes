# Research map

This is the live conceptual map of the project. It is organized by mechanisms and falsifiable decision gates rather than by release numbers.

For current qualification status and exact CI evidence, see [`CURRENT_STATUS.md`](CURRENT_STATUS.md).

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
diagonal cutoff schedule / localization
        ↓
periodic + temporal/spatial globalization
        ↓
final smooth force
        ↓
finite-time singular behavior
```

The research program asks which arrows are structural, which are sufficient proof architecture, and which can be removed or replaced without losing the singular candidate.

## Track A: pulse continuation / initial-data replacement

### Hypothesis

Part of the explicitly localized pulse mechanism can be replaced by homogeneous continuation or by tiny components already encoded in initial data.

### Established boundary

- The canonical primary pulse solves a homogeneous source-zero two-mode ODE on its native slot.
- The excluded-slot principal error decomposes into cutoff-derivative and uncovered-source channels.
- For the source-zero primary class, the uncovered-source channel disappears.
- Setting the temporal cutoff to one removes that local principal commutator only where the uncut solve identity remains valid.
- The source does not prove that the existing differentiable coefficient extension solves the homogeneous ODE outside the native interval.

### Decision chain

```text
A1 native-slot homogeneous solve                   [SOURCE_LOCKED]
A2 exact cutoff commutator identification          [SOURCE_LOCKED]
A3 enlarged-interval homogeneous continuation      [OPEN]
A4 uniqueness agreement on original slot           [OPEN]
A5 recompute all residual channels with psi = 1    [BLOCKED ON A3]
A6 finite pulse hierarchy / initial-data encoding  [BLOCKED]
A7 all-Sobolev or Gevrey summability               [BLOCKED]
A8 nonlinear cross-pulse closure                   [BLOCKED]
```

### Kill conditions

- no homogeneous continuation compatible with the required geometry/support;
- backward amplification overwhelms any initial-data tail suppression;
- nonlinear interactions recreate a non-summable residual.

## Track B: similarity-parameter margin

### Hypothesis

Part of the gap between broad power-counting windows and the source's small selected parameters is sufficient-constant bookkeeping rather than a structural barrier.

### Current state

Two exact local sufficient bounds were extracted earlier:

```text
h < 99/17002
h < 949/268040
```

They are local sufficient certificates, not global or sharp thresholds.

### Decision chain

```text
B1 cheap balance window                         [REPRODUCED]
B2 source small-h constraints                    [SOURCE_EXTRACTED]
B3 enumerate direct consumers                    [PARTIAL]
B4 classify structural vs sufficient constants  [ACTIVE]
B5 relax one binding inequality at a time        [OPEN]
B6 propagate through downstream dependency DAG   [OPEN]
B7 certify a larger admissible parameter region  [BLOCKED]
```

## Track C: force / residual attribution

### Goal

Trace the final physical forcing back to source-level residual mechanisms without double-counting bookkeeping decompositions.

### Qualified source lineage

For pre-singular times, the final force is the Navier–Stokes residual of the activated/localized candidate. The time-activation identity separates:

```text
chi * incoming residual
+ chi' * velocity
+ (chi^2 - chi) * nonlinear transport
```

Within the normalized finite-stage residual, the meaningful physical decomposition is the nonlinear differential residual plus virtual/base terms. Gaussian and alias pieces appear in an exact harmonic reconstruction as subtraction/restoration bookkeeping and must not be ranked as independent force atoms.

Native exponent ranking identifies the harmonic-source sum as the slowest finite-stage decay channel among the presently isolated terms. This is an exponent bottleneck, not a numerical norm fraction.

### Next quantitative target

Move from exponent attribution to an explicit force-size observable only after the geometry/schedule is fully specified.

Candidate observables:

1. terminal-window weighted `C^m`/`L∞` residual seminorm;
2. terminal-window `L^1_t L^2_x` on one periodic spatial cell;
3. broader force norms only after activation and globalization contributions are controlled.

## Track D: canonical schedule and quantitative gain

### Qualified results

A deterministic least-admissible local integer scale and canonical schedule have been formalized. If a gain certificate improves pointwise, the canonical selected cutoff schedule cannot worsen.

Strict improvement is not automatic. The project now has:

- an exact integer-threshold crossing criterion;
- a sufficient condition for strict local improvement to survive the recursive envelope; and
- a constant-cancelling theorem that compares stronger and weaker power budgets without assigning fake numerical values to existential constants.

### Secondary gain-slack hypothesis

The pinned source exposes a common candidate positive-stage margin

```text
Delta g = h * (3/5 - kappa)
        = 59999/100000 * h
```

at `kappa = 1/100000`.

Low-level slack statements remain interesting, but the attempted literal actual-candidate adapter is not qualified. Treat this as a blocked secondary lane until the exact `StageEstimates` reconstruction is repaired or replaced.

## Track E: factor-two schedule necessity

### Hypothesis

The source condition

```text
2 * a(j) <= a(j+1)
```

is a convenient way to force a positive, strictly increasing, divergent cutoff schedule, but is not structurally required by the final singular candidate.

### Qualified results

The minimal strict envelope

```text
s(0)   = max(1, local(0))
s(j+1) = max(local(j+1), s(j)+1)
```

has been source-locked in Lean and is pointwise no larger than the source doubling envelope. It preserves all numerical local admissibility requirements.

The finite heterogeneous analytic cutoff-bound theorem has also been rebuilt successfully using this weaker schedule.

### Active decision chain

```text
E1 minimal strict numerical selector              [FORMALIZED]
E2 finite heterogeneous cutoff bounds             [FORMALIZED]
E3 local-q support + smooth zero extension        [CI ACTIVE]
E4 mixed three-component schedule                 [OPEN]
E5 mixed residual vanishing                       [SOURCE AUDIT SUPPORTS]
E6 parallel final singular candidate theorem      [OPEN]
E7 old-vs-new collar residual comparison          [BLOCKED ON E6]
E8 standard force-norm comparison                 [BLOCKED ON E7]
```

### Current source-audit evidence

The downstream residual and final assembly proofs audited so far consume:

- positivity / minimum scale;
- strict monotonicity or `Tendsto` of real scales;
- local support separation;
- smooth diagonal sums;
- away-extension data;
- residual vanishing;
- angular divergence; and
- origin blowup.

The factor-two witness is carried by the existing schedule API but is not visibly passed to those final calls. This is strong evidence for the hypothesis, but only E6 would make the deletion end-to-end.

### Kill condition

If any downstream theorem genuinely requires factor-two growth rather than only strict divergence/local finiteness, record the first such theorem and stop claiming the mechanism is removable.

## Track F: stress-cone optimization

For a target stress `T` and covariance columns `H_i`, solve

```text
T = sum_i a_i H_i,    a_i >= 0.
```

The target is not just feasibility but robustness margin. A future evaluator should optimize interior-cone margin while preserving profile, support, and residual constraints.

Potential payoff:

- identify redundant wave families;
- simplify correction architecture;
- expose more stable realizable-stress mechanisms;
- transfer the grammar to neighboring PDEs.

## Track G: cross-PDE mechanism compiler

Once the Navier–Stokes mechanisms are encoded quantitatively, reuse the grammar on neighboring systems.

Priority order:

1. Euler, because the pinned project already provides an unforced comparison construction.
2. Boussinesq, because coupling introduces another amplification/stress channel.
3. MHD, where Maxwell stress supplies a natural quadratic transport mechanism.
4. Hall-MHD and generalized dissipative systems, where the balance grammar changes more substantially.

## Research resource allocation

Prioritize information gain over cosmetic progress.

High-value outcomes include:

- proving a proposed deletion impossible;
- locating the first truly binding theorem or inequality;
- turning an existential comparison into a deterministic/canonical one;
- finding proof fields that are carried through APIs but never consumed downstream;
- separating a real physical field change from a proof-certificate improvement.

A failed branch with a precise mathematical blocker is evidence. A green branch without a clearly stated claim boundary is not.
