# Changelog

## v5.6.0

- Compile `LinearWaveBounds.excludedSlotError` into a machine-readable cutoff residual atlas.
- Separate the exact cutoff-derivative channel `Dfast(psi)*amplitude` from uncovered-source channel `(1-psi)*source`.
- Specialize the primary residual class to `source=0`, eliminating the uncovered-source channel.
- Split the actual product cutoff into clock-derivative and Gaussian-slot derivative commutators.
- Add the exact `psi=1` principal-wave counterfactual: the localization error vanishes wherever the uncut solve identity remains valid.
- Identify the first one-pulse no-cutoff obstruction: `PrimaryODE.solution` is globally represented by a differentiable extension, but its ODE identity is source-proved only on the native finite interval.
- Promote a new enlarged-interval homogeneous primary candidate and defer multi-pulse summability until that single-pulse gate is passed.
- Advance CLI/artifact generation and release metadata to v5.6.0 with fresh CI required.

## v5.5.0

- Audit the pulse construction at the source level and separate **homogeneous pulse amplification** from **cutoff localization**.
- Record that `PrimaryODE.primary` uses a nonzero Gaussian entry seed and zero in-slot forcing.
- Promote the slot-cutoff tail geometry from conditional to source-backed: cutoff derivatives satisfy `L/5 <= |v-L/2| <= L/3`.
- Add the cutoff commutator identity `(∂-A)(χx)=χ'x` and the homogeneous-ODE uniqueness obstruction to exact temporal compactness.
- Pivot the forcing-ablation route toward globally present Gaussian-small tails and exact residual recomputation.
- Add exact rational local `h` certificates: `99/17002` and `949/268040`.
- Add `UPSTREAM_WATCH.json` after OpenAI upstream introduced a broader manuscript-range axis parameter layer while retaining tighter selected `SmallParameters`.
- Repair stale release metadata and make the CLI generate v5.5 artifacts rather than hard-coded v5.2 output.
- Add CI tests for release-version/source-lock consistency.

## v5.4.0

- Add a source-derived sufficient local window for `NaturalEntrance.base_source_lower`, approximately `h < 0.00582284` at `j <= 0.001`.
- Add a conservative sufficient local window for `MatchingConeBounds.shape_axis_lower`, approximately `h < 0.00354052`.
- Identify `shape_axis_lower` as the tighter of those two local certificates, without claiming it is the global bottleneck.
- Add local-relaxation tests and machine-readable certificates.

## v5.3.0

- Add source-locked Gaussian pulse-envelope extraction and source-backed stage/carrier/slot scaling.
- Correct the v5.1 toy `exp(-c*k^gamma)` pulse-tail coordinate to the source-natural `exp(-C*n^2) = exp(-Theta((log k)^2))` form.
- Add an executable `h`-constraint dependency graph with `NUMERIC`, `DERIVED_WEAK`, `INHERITED`, and `UNKNOWN` consumer classes.
- Seed the first source-visible small-`h` bottleneck map for `NaturalAxisData`, `NaturalEntrance`, `MatchingConeBounds`, `ActivationContinuation`, and `TransitionRamp`.
- Add project overview, research map, and machine-readable research status artifacts.

## v5.2.0

- Make GitHub the canonical research ledger and add CI.
- Add an evidence-aware constraint provenance ledger for the similarity parameter `h`.
- Separate the cheap `h < 1/6` scaling window, manuscript-level `h < 1/100` regime, and the formalization's concrete `h <= 1/1000` small-parameter window.
- Add fail-closed pulse-transfer exponent interval comparison.
- Add a source-extraction contract for the pulse-tail / propagation question.

## v5.1.0

- Compile the published construction into a structural residual atlas.
- Add forcing-ablation routes, scaling search, proof obligations, and initial-data transfer toy criterion.
