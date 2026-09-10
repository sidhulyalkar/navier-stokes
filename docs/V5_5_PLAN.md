# v5.5.0 plan: transitive bottleneck + backward pulse propagator

## Goal

Convert the local v5.4 certificates into two decision-grade objects:

1. a transitive `h` bottleneck along the actual proof path;
2. a stage-`n` backward pulse-transfer bound directly comparable with the source-backed Gaussian tail scale.

## Workstream A: proof-path bottleneck

For each direct numerical consumer of the small-`h` assumption:

- extract the literal target inequality from the pinned Lean source;
- eliminate the inherited `h <= 1/1000` assumption wherever possible;
- derive a source-backed sufficient local upper bound `h < H_i`;
- label each bound `DERIVED_LOCAL`, `FORMALIZED_GENERALIZED`, `INHERITED_ONLY`, or `OPEN`;
- build the transitive dependency path to the final candidate and compute the active certified bottleneck `min_i H_i` only over comparable proven/sufficient constraints.

The current extracted ordering is:

- `NaturalEntrance.base_source_lower`: `H_entrance ~ 0.00582`;
- `MatchingConeBounds.shape_axis_lower`: `H_shape ~ 0.0035405`.

The latter is the current local bottleneck, but this is not yet the full proof-path bottleneck.

## Workstream B: backward pulse propagator

Use the source-native stage coordinate `n`, not the obsolete v5.1 toy `k^gamma` coordinate.

Pinned source gives:

- `Q_n = 2^-n`;
- `epsilon_n = Q_n^h = 2^(-n h)`;
- carrier `k_n` satisfies `1 <= epsilon_n k_n^2 <= 4`;
- slot length `ell_n = Theta(n^2)`;
- under a fixed-fraction tail-region condition, Gaussian envelope suppression is `exp(-Theta(n^2))`, equivalently `exp(-Theta((log k_n)^2))`.

Next derive a source-backed operator bound for the homogeneous pulse evolution before activation:

`a_n(t_activation) = U_n(t_activation, 0) a_n(0)`.

The critical object is the inverse cost `||U_n(t_activation,0)^(-1)||` in stage `n`.

### Decision rule

- If inverse growth is `exp(o(n^2))`, Gaussian tail suppression wins at leading scale.
- If inverse growth is `exp(omega(n^2))`, the initial-data pulse route is killed at this level.
- If inverse growth is `exp(Theta(n^2))`, coefficients and lower-order terms become decisive.
- If no rigorous operator estimate is available, status remains `OPEN`.

## Claim boundary

v5.5 will not infer full unforced Navier-Stokes blowup from pulse summability or a widened local `h` window. Every theorem-level upgrade requires exact residual closure and downstream proof obligations.
