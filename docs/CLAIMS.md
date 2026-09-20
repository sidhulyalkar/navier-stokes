# Scientific claim boundary

This repository studies which mechanisms in the pinned 2026 **forced** Navier–Stokes singularity construction are structurally necessary. It does not claim an unforced Navier–Stokes blowup proof.

For the freshest project state, read [`CURRENT_STATUS.md`](CURRENT_STATUS.md).

## Established by this codebase

- The pinned source construction has been encoded as a source-anchored dependency/residual atlas.
- The final force/residual lineage has been traced far enough to separate mixed residual, localization/activation, and extension layers.
- Canonical local integer cutoff scales and schedules are formally comparable under stronger gain certificates.
- Strict cutoff-scale improvement has a source-locked threshold criterion.
- A constant-cancelling theorem compares stronger and weaker cutoff requirements without inventing opaque multiplicative constants.
- Factor-two schedule growth is formally unnecessary through the **final forced singular-candidate assembly**. The weaker minimal `+1` strict envelope survives numerical selection, finite cutoff bounds, physical local-`q` zero extension, mixed schedule construction, mixed residual vanishing, and final candidate replay.
- For any requested initial cutoff floor, one can choose a common admissible floor above it where the minimal strict and doubling selectors agree at stage 0 and are strictly separated at stage 1.
- v5.11 constructs **paired** strict and doubling schedules from identical raw potential/direct/pressure fields, gain/loss functions, aggregated cutoff constants/log powers, support floor, finite background, and finite residual data.
- Both paired schedules satisfy the required physical local-`q` cut bounds, smooth mixed sums, and endpoint-flat mixed residual conclusions.
- The paired selector geometry can be sharpened deterministically through stage 2. With a sufficiently large common admissible floor `B >= 2`,
  `aStrict(2)=B+2` and `aDouble(2)=4B`; at `q*=1/(2*aStrict(2))`, the strict scalar cutoff is exactly one and the doubling scalar cutoff exactly zero.
- Conditional on a raw stage being nonzero at that explicit comparison point, the corresponding strict and doubling cut stages are formally different there.

## Active but not yet established end-to-end

- A source-backed nonzero actual positive-stage witness at the explicit strict-vs-doubling comparison radius, or another theorem proving the paired assembled physical fields/residuals are nonidentical.
- The late-time force-to-original-residual bridge on the spatial plateau is implemented and under dedicated source-locked re-audit after an elaboration-timeout repair.
- A scale-retaining cutoff/product jet estimate that keeps the exact `a^n` factors instead of replacing them by the source's scale-uniform `q^{-n}` loss.
- A quantitative ordering of paired collar residuals or final forcing fields.
- Promoting the source-visible `59999/100000 * h` common stage-gain slack into a fully qualified literal actual-candidate certificate.

## Not established

- No independent re-proof of every theorem in the upstream OpenAI formalization.
- No theorem says the source/default `lower = 1` selectors differ; strict-separation theorems choose a common admissible floor.
- No theorem yet proves that the two paired **actual physical fields** are unequal.
- No quantitative proof that any modified witness has smaller forcing in `L¹_t L²_x`, `L²_t L^{3/2}_x`, `L∞`, or another standard norm.
- No family with force norm tending to zero.
- No unforced Navier–Stokes singularity.
- No proof of structural stability of the published singular solution.

## Interpretation rule

A stronger exponent, smaller admissible cutoff integer, pointwise smaller schedule, or even an explicitly different **scalar cutoff** is not automatically a smaller force. The physical cut field is `χ(a_j q) A_j`: field separation additionally requires nontrivial raw data where the cutoffs differ, and force comparison requires the resulting Navier–Stokes residual difference to be controlled after localization, activation, gluing, and extension.

The source's published `CutStageBounds` deliberately erase explicit schedule dependence by replacing cutoff scale powers `a^n` with `q^{-n}`. A force-reduction claim therefore requires a new scale-retaining comparison rather than reinterpreting those scale-uniform existence estimates.
