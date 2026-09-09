# Findings v5.3.0

## 1. The pulse-transfer comparison should be formulated in dyadic stage, not an assumed power of carrier frequency

The pinned OpenAI source gives:

- `Q_n = 2^{-n}` from `SlotColoring.dyadicQ`;
- `epsilon_n = Q_n^h = 2^{-nh}` from `ChartScales.epsilon`;
- `1 <= epsilon_n k_n^2 <= 4` for the actual integer carrier;
- `ell_n = Theta(n^2)` from `ChartScales.slotLength_bounds`;
- a Gaussian slot-time envelope `exp(-c Delta_t^2/(2 ell_n))` under the hypotheses in `GaussianEnvelope.gaussian_envelope_bounds`.

Therefore

    2^(nh/2) <= k_n <= 2*2^(nh/2),

so for fixed `h>0`,

    n = Theta(log k_n)

and

    ell_n = Theta((log k_n)^2).

If the actual Gaussian tail is evaluated a uniform positive fraction of a slot away from its midpoint, then `|Delta_t| >= a ell_n` and the upper envelope is

    exp(-C ell_n) = exp(-Theta(n^2)) = exp(-Theta((log k_n)^2)).

This corrects the v5.1 toy model `exp(-c k^gamma)`. The toy model remains useful as an abstract comparison pattern, but it is not the source-natural frequency coordinate for this part of the construction.

### What remains open

The fixed-fraction condition must be proved for the actual cutoff/tail region used by the pulse hierarchy. More importantly, the backward propagator must now be bounded in the same stage coordinate. The decisive comparison becomes roughly

    tail suppression: exp(-C n^2)
    versus
    backward amplification: ?

rather than a guessed `gamma_tail` versus `delta_back` power law in `k`.

## 2. The `h <= 1/1000` assumption has both real numerical consumers and weak inherited consumers

A source scan from `NaturalAxisData.SmallParameters.h_le` shows two qualitatively different uses.

### Direct numerical consumers

Examples include:

- explicit `D`, `A`, `L`, and `W` margins in `NaturalAxisData.lean`;
- entrance estimates in `NaturalEntrance.lean`;
- matching-cone estimates in `MatchingConeBounds.lean`;
- activation-continuation estimates in `ActivationContinuation.lean`;
- transition-ramp estimates in `TransitionRamp.lean`.

These are high-priority because changing `h` changes a quantitative margin in the proof.

### Weak derived consumers

Other source-visible uses derive only statements such as

    h < 1/2

from `h <= 1/1000`, for example in `NaturalCore.lean` and `ConstructedSlowBase.height_lt_half`.

Those consumers do not by themselves explain the small formalization window. They are proof plumbing unless a deeper downstream theorem needs their stronger provenance.

## 3. The next bottleneck experiments are sharper

### Pulse lineage

1. Prove the actual tail/cutoff region has uniform fractional slot separation, or replace that condition by the exact source geometry.
2. Extract the actual homogeneous pulse propagator before activation.
3. Bound its inverse in dyadic stage `n`.
4. Compare the bound directly against `exp(-C n^2)`.
5. Only if suppression wins, test all-Sobolev/Gevrey summability and nonlinear cross-pulse interactions.

### Small-h lineage

1. Extract complete target inequalities for `MatchingConeBounds`, `NaturalEntrance`, `ActivationContinuation`, and `TransitionRamp`.
2. Solve each inequality symbolically for the largest locally admissible `h` with all other constants frozen.
3. Build a transitive declaration graph to the final candidate.
4. Identify the minimum along that path as a candidate bottleneck.
5. Relax one bottleneck at a time and require the relevant Lean subtree to remain provable.

## Claim boundary

v5.3 does not prove an unforced Navier-Stokes singularity, does not reduce the actual published force, and does not prove that `h <= 1/1000` can be relaxed. It improves the coordinates and dependency structure in which those questions should be attacked.
