# Scientific claim boundary

This repository studies which mechanisms in the pinned 2026 **forced** Navier–Stokes singularity construction are structurally necessary. It does not claim an unforced Navier–Stokes blowup proof.

For the freshest project state, read [`CURRENT_STATUS.md`](CURRENT_STATUS.md).

## Established by this codebase

- The pinned source construction has been encoded as a source-anchored dependency/residual atlas.
- The reference anisotropic exponents satisfy the leading power-counting identities implemented in the project.
- The final force/residual lineage has been traced through the mixed diagonal residual, periodic assembly, activation/localization, and final force construction far enough to distinguish physical residual terms from bookkeeping decompositions.
- The canonical local integer cutoff scale and schedule are formally comparable under stronger gain certificates.
- Strict cutoff-scale improvement has a source-locked threshold criterion rather than being inferred from exponent improvement alone.
- A constant-cancelling theorem compares stronger and weaker cutoff requirements without inventing values for existential multiplicative constants.
- Factor-two schedule growth is formally unnecessary for the numerical diagonal selector: the minimal `+1` strict envelope remains positive, strictly monotone, tends to infinity, preserves local admissibility, and is pointwise no larger than the source doubling envelope.
- The finite heterogeneous cutoff-bound layer also formally survives with this weaker schedule.

## Active but not yet established end-to-end

- Removing factor-two schedule growth from the local-`q` zero-extension, mixed schedule, residual, and final singular-candidate pipeline.
- Translating a changed cutoff schedule into a quantitative ordering of collar residuals or final forcing fields.
- Promoting the source-visible `59999/100000 * h` common stage-gain slack into a fully qualified literal actual-candidate certificate.

## Not established

- No independent re-proof of every theorem in the upstream OpenAI formalization.
- No end-to-end singular witness has yet been qualified with factor-two schedule growth removed.
- No quantitative proof that any modified witness has smaller forcing in `L¹_t L²_x`, `L²_t L^{3/2}_x`, `L∞`, or another standard norm.
- No family with force norm tending to zero.
- No unforced Navier–Stokes singularity.
- No proof of structural stability of the published singular solution.

## Interpretation rule

A stronger exponent, smaller admissible cutoff integer, or pointwise smaller cutoff schedule is **not** automatically a smaller force. The cutoff field is `χ(a_j q) A_j`; changing `a_j` moves the transition collar and changes both cutoff derivatives and the size/location of the uncut field. A force-reduction claim requires a direct norm comparison after all activation, localization, gluing, and extension terms are accounted for.
