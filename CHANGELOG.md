# Changelog

## v5.3.0

- Add source-locked Gaussian pulse-envelope extraction and source-backed stage/carrier/slot scaling.
- Correct the v5.1 toy `exp(-c*k^gamma)` pulse-tail coordinate to the source-natural conditional `exp(-C*n^2) = exp(-Theta((log k)^2))` form.
- Add an executable `h`-constraint dependency graph with `NUMERIC`, `DERIVED_WEAK`, `INHERITED`, and `UNKNOWN` consumer classes.
- Seed the first source-visible small-`h` bottleneck map for `NaturalAxisData`, `NaturalEntrance`, `MatchingConeBounds`, `ActivationContinuation`, and `TransitionRamp`.
- Add project overview, research map, and machine-readable research status artifacts for public-facing research UX.
- Add tests for the new dependency and scale-conversion machinery.

## v5.2.0

- Make GitHub the canonical research ledger and add CI.
- Add an evidence-aware constraint provenance ledger for the similarity parameter `h`.
- Separate the cheap `h < 1/6` scaling window, manuscript-level `h < 1/100` regime, and the formalization's concrete `h <= 1/1000` small-parameter window.
- Add fail-closed pulse-transfer exponent interval comparison.
- Add a source-extraction contract for the Section 7 pulse-tail / backward-propagator question.

## v5.1.0

- Compile the published construction into a structural residual atlas.
- Add forcing-ablation routes, scaling search, proof obligations, and initial-data transfer toy criterion.
