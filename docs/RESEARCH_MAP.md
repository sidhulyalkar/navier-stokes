# Research map

This is the live conceptual map of the project. It is organized by mechanisms and falsifiable decision gates rather than release numbers.

For exact qualification status and CI evidence, see [`CURRENT_STATUS.md`](CURRENT_STATUS.md).

## Reference mechanism

```text
anisotropic concentrating base
        ↓
annular residual / stress demand
        ↓
oscillatory wave families
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

The program asks which arrows are structural, which are sufficient proof architecture, and which can be removed or replaced.

## Track A: pulse continuation / initial-data replacement

The canonical primary pulse solves a homogeneous source-zero two-mode ODE on its native slot, and the excluded-slot principal error can be traced to cutoff derivatives for that source-zero class. The source does not prove the existing coefficient extension solves the homogeneous ODE outside the native interval.

```text
native-slot homogeneous solve                 [SOURCE_LOCKED]
cutoff commutator identification              [SOURCE_LOCKED]
enlarged-interval homogeneous continuation    [OPEN]
uniqueness on original slot                   [OPEN]
full residual recomputation with cutoff=1     [BLOCKED]
finite hierarchy / initial-data encoding      [BLOCKED]
```

## Track B: similarity-parameter margin

Exact local sufficient bounds such as `h < 99/17002` and `h < 949/268040` have been extracted, but they are not global sharp thresholds.

```text
source small-h consumers                      [PARTIAL]
structural vs sufficient-constant taxonomy    [ACTIVE]
one-constraint-at-a-time relaxation           [OPEN]
transitive larger admissible region           [BLOCKED]
```

## Track C: force / residual attribution

For pre-singular times, the final force is the Navier–Stokes residual of the activated/localized candidate. Time activation separates incoming residual, switch derivative, and nonlinear activation-defect channels. Gaussian/alias terms in harmonic reconstruction are bookkeeping pairs rather than independent physical force atoms.

Next target: convert source-level attribution into a schedule-sensitive terminal residual/force observable with explicit comparison rules.

## Track D: canonical schedule and gain

Qualified v5.9 results:

- deterministic least-admissible local integer scale;
- canonical schedule monotonicity under stronger gain;
- exact strict integer-threshold crossing criterion;
- condition for strictness to survive the source recursive envelope;
- constant-cancelling scale relaxation that avoids guessed multiplicative constants.

A source-visible candidate common gain slack `59999/100000 * h` remains a secondary lead, but the attempted literal boosted actual-candidate adapter is blocked and is not a promoted result.

## Track E: factor-two schedule necessity

### Hypothesis

The source condition

```text
2 * a(j) <= a(j+1)
```

is convenient proof architecture rather than a structural requirement of the singular candidate.

### Qualified chain

```text
E1 minimal strict numerical selector            [FORMALIZED]
        ↓
E2 finite heterogeneous cutoff bounds           [FORMALIZED]
        ↓
E3 local-q support + smooth zero extension      [FORMALIZED]
        ↓
E4 mixed three-component strict schedule        [NEXT]
        ↓
E5 mixed residual vanishing                     [SOURCE AUDIT SUPPORTS]
        ↓
E6 parallel final singular candidate theorem    [OPEN]
        ↓
E7 old-vs-new collar residual comparison        [BLOCKED]
        ↓
E8 standard force-norm comparison               [BLOCKED]
```

The minimal strict envelope is

```text
s(0)   = max(1, local(0))
s(j+1) = max(local(j+1), s(j)+1).
```

It is positive, strictly monotone, divergent, preserves local numerical admissibility, and is pointwise no larger than the source doubling envelope. The finite analytic cutoff layer and actual local support/zero-extension layer have both been rebuilt with this weaker schedule.

### Kill rule

If any downstream theorem genuinely requires factor-two growth rather than strict divergence/local finiteness, record the first such theorem and stop the deletion claim there.

## Track F: stress-cone optimization

For target stress `T` and covariance columns `H_i`, study

```text
T = sum_i a_i H_i,    a_i >= 0,
```

with emphasis on interior-cone robustness, redundant wave families, and whether the correction architecture can be simplified without changing the target stress class.

## Track G: cross-PDE mechanism compiler

After the Navier–Stokes mechanism grammar is quantitative enough, test transfer to Euler, Boussinesq, MHD, and Hall-MHD. This remains downstream of the current necessity/force-size work.

## Research allocation rule

Prioritize information gain over cosmetic progress. A failed branch that identifies the first genuinely binding theorem is useful evidence. A green branch without a precise claim boundary is not.
