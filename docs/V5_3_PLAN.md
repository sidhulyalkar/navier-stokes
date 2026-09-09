# v5.3.0 plan: source-extracted pulse bounds + h dependency graph

## Goal

Move one layer closer to a genuine mathematical obstruction/result by replacing qualitative source annotations with quantitative, source-locked inequalities.

## Workstream A: pulse-tail extraction

- Enumerate the exact Lean declarations used to obtain Gaussian/exponential smallness of pulse tails.
- Normalize each bound into a common schema: scale variable, frequency variable, exponent, coefficient, derivative order, support/interval assumptions.
- Produce a certified interval for the suppression exponent only when the source supports it.

## Workstream B: backward propagator

- Identify the homogeneous linear amplitude dynamics on a pulse interval.
- Separate forward amplification from the question of pulling a prescribed activation state back toward `t=0`.
- Establish operator-norm upper/lower bounds for the inverse map or prove that the route is ill-posed in the required function class.
- Feed only proved/bounded exponent intervals into the transfer evaluator.

## Workstream C: h dependency graph

- Start from `NaturalAxisData.SmallParameters.h_le`.
- Search all downstream lemmas consuming `h_le`, `h_lt_half`, or derived numerical margins.
- Record whether each bound is structural, inherited, or merely a convenient sufficient constant.
- Attempt local relaxation with tests/formal proof obligations before changing the global parameter window.

## Stop conditions

Kill the initial-data pulse route if certified backward amplification dominates certified tail suppression. Hold it if the exponents overlap without coefficient control. Promote it to nonlinear compatibility work only after all-Sobolev summability is established.
