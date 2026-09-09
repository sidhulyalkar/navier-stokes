# v5.1.0 - OpenAI Construction Compiler

## What this release actually does

v5.1 turns the published proof architecture into a machine-readable residual atlas and then runs fail-closed ablations against that structure. It also implements an executable anisotropic power-counting filter for nearby similarity scalings.

It **does not** numerically reconstruct OpenAI's analytic profiles, compute the true force field, or reduce its norm. Those are v5.2+ tasks.

## Highest-value insight from the first ablation pass

The most promising forcing reduction is not `f -> lambda f`. The structural atlas separates three conceptually different sources of forcing exposure:

1. **Pulse seeding:** the published physical description explicitly seeds each pulse with an exponentially small external force before background shear amplifies it.
2. **Spatial/temporal localization:** cutoff derivatives enter the exact final residual `f = R(u,p)`; the temporal cutoff enforces the special zero-initial-data theorem.
3. **Residual closure:** the final force is the exact residual of the localized field. Removing it requires an exact zero-residual construction, not a small-norm estimate alone.

This suggests a concrete unforced research route: allow nonzero smooth initial data, encode the pulse hierarchy in that data (or produce it endogenously), and replace compact cutoff globalization by a globally decaying construction. The hard mathematical question is whether the entire scheduled hierarchy can survive from the initial slice without losing the stress-cone/correction structure.

## v5.2 target: quantitative construction extraction

1. Encode the actual leading profiles and parameters from Sections 4 and Appendices A-C.
2. Reproduce the admissible stress-cone inequalities numerically/symbolically on the published profile domain.
3. Encode the pulse ODE/amplitude system from Section 7 and verify growth-then-decay envelopes.
4. Build a quantitative forcing observable interface around the localized fields of Section 10.
5. Run continuation over only source-justified free parameters, preserving all hard inequalities.
6. Promote no forcing-reduction claim until the actual residual and norms are evaluated on the source construction.

## v5.3 target: initial-data pulse transfer

Represent each late pulse as a backwards-propagated tiny initial perturbation candidate. Test whether its required initial magnitude remains summable/smooth and whether cross-scale interactions stay inside the correction budget. This is where the "remove the force" question becomes an actual dynamical shooting problem.
