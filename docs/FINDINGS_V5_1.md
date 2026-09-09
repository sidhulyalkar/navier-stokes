# v5.1 findings and next attacks

## Finding 1: initial-data transfer is the cleanest first forcing-ablation target

The published physical description says an exponentially small external force seeds each pulse. Section 7 sharpens the mechanism: the leading covariance pulse is a homogeneous zero-source amplitude solution with a specified nonzero initial amplitude on its local pulse interval; temporal localization occurs in exponentially small tails. This makes the first unforced experiment precise: pull every desired local pulse state back to the true t=0 slice and ask whether the resulting infinite hierarchy is smooth and summable.

A generic asymptotic model is

    a_n(0) ~ exp(-c k_n^gamma + d k_n^delta),

where the first term is pulse-tail suppression and the second is the cost of backward evolution. The hierarchy beats every fixed Sobolev weight if gamma > delta, or at equal exponents if c > d. The source values of these exponents/coefficient bounds have **not** yet been extracted.

## Finding 2: elementary scaling leaves a large unexplored h-margin

Power counting of time derivative, radial transport, radial diffusion, axial transport, axial diffusion, and dominant-component energy yields

    beta_r = 1/2,
    alpha_r = 1/2,
    alpha_t = 1 - beta_z,
    1/3 < beta_z < 1/2.

Writing beta_z = 1/2 - h gives the cheap interval

    0 < h < 1/6.

The published construction chooses 0 < h < 1/100. Therefore the tight small-h requirement does not come from the elementary balance/energy constraints alone. v5.2 should identify which profile, admissible-cone, support, derivative-loss, or correction estimates consume this margin. That is a high-information experiment even if no extension is possible.

## Finding 3: naive force deletion fails for two different reasons

1. Setting the final residual force to zero without changing the fields simply violates the PDE unless R(u,p)=0 identically.
2. Removing the pulse seed while retaining the wave-stress mechanism leaves no way to create the required nonzero leading pulse amplitudes from globally zero pulse data.

These should be attacked separately. Initial-data transfer addresses the second. Exact/global residual closure addresses the first.

## v5.2 experiment order

1. Extract the Section 4/App. A-C profile parameterization and admissible stress-cone inequalities.
2. Build an h-constraint ledger and locate the first theorem/estimate that forces h below 1/100.
3. Extract the Section 7 pulse envelope, activation scale, frequency scale, and cutoff-tail exponent.
4. Derive a backward propagator bound for each pulse family through the pre-activation background.
5. Test all-Sobolev summability of the pulled-back initial hierarchy.
6. Only then attempt quantitative force-norm continuation on the actual construction.
