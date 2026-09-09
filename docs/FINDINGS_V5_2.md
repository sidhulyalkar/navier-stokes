# Findings v5.2.0

## 1. Constraint provenance is now a first-class object

The cheap scaling calculation permits `0 < h < 1/6`, while the manuscript-level construction is recorded with `0 < h < 1/100`. The released Lean formalization uses an even more concrete `SmallParameters` structure with `0 < h` and `h <= 1/1000` in `NavierStokes/NaturalAxisData.lean` at source commit `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.

This is **not** evidence that `1/1000` is sharp. The formalization comments that it is a concrete range permitted by the manuscript's smallness order. The next research question is to trace which downstream inequalities consume this margin and determine how much of it is convenience versus structure.

## 2. The initial-data pulse route is now fail-closed

The v5.1 toy criterion

`|a_n(0)| ~ exp(-c k_n^gamma + d k_n^delta)`

is useful only after the source construction supplies quantitative bounds on `gamma` and a new backward-propagator analysis supplies bounds on `delta`. v5.2 therefore stores each exponent as an interval with an evidence state.

- If `gamma_lower > delta_upper`, suppression wins at exponent level.
- If `gamma_upper < delta_lower`, backward amplification wins.
- If intervals overlap, the verdict remains `OPEN` and coefficients/subleading terms must be resolved.
- If either interval is unknown, the verdict remains `OPEN`.

No numerical pulse-transfer exponents are claimed in v5.2.

## 3. Best current research lineages

The structural evaluator still promotes three routes for deeper work:

1. `R5_UNFORCED_SHOOTING`: transfer pulse seeding into initial data and replace spatial cutoff with a global decaying construction.
2. `R1_INITIAL_DATA_PULSES`: preserve more of the source construction while eliminating pulse seed forcing and the zero-initial-data temporal cutoff.
3. `R8_PROFILE_PLUS_GLOBAL`: redesign the annular balance itself while also removing localization/initial-data forcing. This is higher-risk but may eliminate more machinery.

Promotion is only a prioritization label. None of these routes currently discharges the exact unforced residual obligation.

## 4. Immediate blocker

The next release should extract a quantitative pulse-tail ledger from the actual Section 7 / Lean wave machinery and pair it with a mathematically explicit backward-propagator problem. In parallel, build a theorem-by-theorem `h` dependency graph beginning at `NaturalAxisData.SmallParameters` and ending at the final candidate assembly.
