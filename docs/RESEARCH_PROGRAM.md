# v5 research program: from one singularity to a mechanism laboratory

## Program A: forcing survival / forcing removal

The scientific object is not a scalar `lambda*f` alone.  We track a family

    (u_lambda, p_lambda, f_lambda)

and require the exact residual

    R_lambda = dt u_lambda + (u_lambda.grad)u_lambda - nu Delta u_lambda + grad p_lambda - f_lambda

to remain zero (or to be rigorously enclosed and corrected) while the singularity observables persist.

### A0 Reference lock
Freeze the public paper, Lean repository commit, theorem statements, and a machine-readable decomposition of the construction.

### A1 Scaling reproduction
Reproduce core exponents, energy budget, Reynolds-number scalings, and support geometry.  This release implements the first part.

### A2 Residual atlas
Represent every leading and correction residual by `(region, channel, tau-order, spatial profile, provenance)`.

### A3 Forcing decomposition
Decompose the final smooth force by source: base-profile mismatch, pulse seeding, mean correction, localization/exterior matching, and terminal extension.

### A4 Homotopy
Continue profile parameters while reducing each forcing family separately.  Do not conflate failure of Newton continuation with non-existence.

### A5 Initial-geometry transfer
Search for a short pre-singular unforced interval whose terminal data lands inside the forced construction's admissible manifold.  This is a genuine shooting/controllability question, not algebraic force deletion.

### A6 Rigorous promotion
Validated numerics or analytic bounds establish continuation neighborhoods; Lean formalizes only statements whose hypotheses and constants are frozen.

## Program B: automated blowup-mechanism discovery

The search language has six layers:

1. **Scaling grammar**: isotropic/anisotropic similarity exponents and field amplitudes.
2. **Geometry grammar**: symmetry, support, core/annulus/exterior decomposition.
3. **Balance grammar**: which PDE terms share leading order in each region.
4. **Stress grammar**: oscillatory families and their realizable mean quadratic stresses.
5. **Correction grammar**: jets in powers/logs of time-to-singularity and reserved support intervals.
6. **Proof grammar**: every candidate emits explicit obligations rather than prose confidence.

### Agent topology
Use many independent lineages.  A lineage owns a mechanism hypothesis and cannot import another lineage's conclusion until a scheduled cross-pollination round.  Dedicated red-team agents try to kill each candidate using scaling, conservation laws, sign constraints, support/smoothness failures, and known regularity criteria.

### Promotion metric
No single pretty numerical trajectory can dominate.  Promotion uses bottleneck scoring over scaling consistency, residual improvement, stress-cone margin, continuation depth, and formalization readiness.

### Research labels
`EXPLORATORY -> REPRODUCED -> CONVERGED -> VALIDATED_BOUND -> FORMALIZED`

The lab must fail closed.  A candidate with a fatal invariant violation receives score `-inf` regardless of novelty.
