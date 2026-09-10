# v5.5.0 plan: selected-parameter bottleneck + localization-free pulse hierarchy

## Goal

Produce two decision-grade objects:

1. a transitive explanation of which **selected** construction requirements still keep `h <= 1/1000` even though broader manuscript-range axis results now exist;
2. a precise forcing-ablation test for replacing cutoff-localized pulses with globally present homogeneous Gaussian-small tails.

## Workstream A: selected-parameter proof-path bottleneck

The upstream audit changes the interpretation of the `h` program. Current OpenAI source contains a broader `NaturalAxisRange.Parameters` layer (`h <= 1/100`, `j <= 1/20`) while `NaturalAxisData.SmallParameters` remains tighter (`h <= 1/1000`).

Therefore:

- do not treat every use of `SmallParameters.h_le` as evidence that `1/1000` is structurally required;
- classify consumers as `PRINTED_RANGE`, `SELECTED_PARAMETER`, `LOCAL_SUFFICIENT`, `DOWNSTREAM_REQUIRED`, or `UNKNOWN`;
- prioritize declarations on the actual selected path into profile choice, matching/stress cone, activation, wave estimates, correction cycles, and candidate assembly;
- use exact rational arithmetic for project-derived sufficient thresholds;
- migrate the source lock only in a dedicated replay release.

Current project-derived local sufficient certificates at pinned source `8937a8f...`:

- `NaturalEntrance.base_source_lower`: `h < 99/17002 ≈ 0.00582284437`;
- `MatchingConeBounds.shape_axis_lower`: `h < 949/268040 ≈ 0.00354051634`.

The matching-cone certificate is the tighter of these two only. It is not yet a full-path bottleneck.

### Immediate A-gates

- `TransitionRamp.L_pos_parameterInterval` is non-binding at the relevant scale: its elementary positivity condition is vastly weaker than `1/1000`.
- broad axis bounds already generalized upstream to the manuscript `1/100` scale should be marked `UPSTREAM_GENERALIZED`, not rederived repeatedly.
- a useful v5.6 target is the first downstream selected theorem whose hypotheses or proof margin genuinely fail when replacing `1/1000` by `1/100`.

## Workstream B: localization-free pulse hierarchy

### Source-backed facts

Pinned source now establishes:

1. `PrimaryODE.primarySeed(a,P,p) = (P(p,a), 0)`.
2. `PrimaryODE.primary` evolves this seed with physical forcing identically zero inside its slot.
3. `PrimaryPulseBounds.cutoffPulse` multiplies that homogeneous primary by `GaussianTailFlat.slotCutoff`.
4. cutoff derivatives satisfy

   `L/5 <= |v-L/2| <= L/3`.

5. the reference envelope on this off-plateau region is exponentially small in slot length.
6. the actual scaled slot length has a uniform `Theta(S)` lower bound with `S=n^2`.
7. Gaussian `exp(-c n^2)` decay absorbs every fixed real power of the dyadic `Q=2^-n` scale.

Thus the old fixed-fraction-tail condition is discharged.

### Structural obstruction

For a homogeneous linear pulse

`x' = A(v)x`

and temporal cutoff

`y = chi(v)x`,

the product rule gives

`y' - A(v)y = chi'(v)x`.

So nonconstant temporal localization creates a source/commutator even when the underlying pulse is exactly homogeneous.

Moreover, uniqueness of the homogeneous ODE implies that a nonzero pulse cannot be identically zero on an earlier interval and then appear later without a source or a change of equation.

### Decision

Kill the lineage:

`exact temporal compactness + nonzero homogeneous pulse + zero source`.

Promote instead:

`globally present Gaussian-small pre/post-slot tails`.

### Next B-obligations

1. Enumerate every residual term caused by the Gaussian slot cutoff and padded clock cutoff in the actual physical pulse.
2. Remove the temporal cutoffs symbolically and recompute the residual difference.
3. Determine whether the uncut homogeneous primary is defined through adjacent slots in the actual moving-frame geometry; if not, identify the first domain/coefficient obstruction.
4. Construct a global extension candidate for one pulse label and bound its pre/post-slot tail.
5. Superpose a finite family and measure/prove cross-slot and cross-frequency interaction growth.
6. Only then study the infinite hierarchy and all-Sobolev/Gevrey summability.
7. Recompute the full Navier-Stokes residual. Small tails never count as zero residual.

## v5.5 success criteria

This release is successful if it:

- makes the amplification/localization distinction machine-readable;
- records the cutoff commutator and uniqueness obstruction;
- upgrades fixed-fraction Gaussian tail geometry from conditional to source-backed;
- records current upstream changes without silently changing the source lock;
- repairs release/CLI version drift;
- leaves the unforced claim explicitly false.

## Claim boundary

Nothing in v5.5 proves that the published forcing can be removed, that the uncut hierarchy is globally well-defined, or that unforced Navier-Stokes develops a singularity. The new result is a sharper decomposition of what is already homogeneous and where forcing/localization genuinely enters.
