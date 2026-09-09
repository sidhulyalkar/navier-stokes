# v5.4.0 plan: quantitative bottleneck extraction

## Goal

Move from locating source-visible constraints to computing local admissible parameter windows and identifying which subtree actually binds the construction.

## Workstream A: local small-h certificates

1. Rewrite source theorems in normalized inequality form.
2. Remove inherited `SmallParameters.h_le` where possible and replace it with an explicit local hypothesis.
3. Solve the normalized inequality for a sufficient local upper bound on `h` with other source constants frozen.
4. Record the proof path and claim boundary.
5. Rank constraints by the minimum locally sufficient window along the transitive path.

The first certificate is `NaturalEntrance.base_source_lower`, for which a direct source-formula estimate gives a sufficient local window of approximately `h < 0.00582` when `j <= 0.001`, compared with the global formalization choice `h <= 0.001`.

## Workstream B: matching/stress-cone bottleneck

- Extract the complete theorem statement and every numerical margin in `MatchingConeBounds`.
- Express cone positivity / strict interior margin as explicit inequalities in `h`, `j`, and any frozen profile constants.
- Solve conservative and exact-enough local bounds separately.
- Prefer a validated strict margin over a merely feasible nonnegative cone.

## Workstream C: activation + transition margins

Repeat the same procedure for `ActivationContinuation` and `TransitionRamp`.

## Workstream D: bottleneck intersection

For a proof path with local sufficient intervals

    0 < h < H_1, ..., 0 < h < H_m,

the current certified path window is

    0 < h < min_i H_i.

Do not interpret this minimum as sharp unless the inequalities themselves are proved necessary.

## Workstream E: pulse lineage continuation

In parallel, keep the pulse-transfer problem in the corrected dyadic-stage coordinate:

    source tail: exp(-C n^2)  [conditional on actual tail geometry]
    backward propagator: unknown

The next pulse deliverable is a source-derived upper bound for the backward map in `n`.

## Stop conditions

- Never upgrade a local sufficient bound to a global construction bound without tracing all transitive consumers.
- Never call a sufficient constant sharp without an obstruction/necessity argument.
- Kill a relaxation lineage if a downstream certified bound is strictly smaller than the proposed window and cannot be improved.
