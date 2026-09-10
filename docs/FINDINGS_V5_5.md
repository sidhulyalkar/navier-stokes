# v5.5 findings: the forcing question moved to localization

## Executive result

The strongest v5.5 conclusion is a **research pivot**, not an unforced singularity result.

The pinned Lean source already constructs the canonical primary slot pulse as a homogeneous zero-forcing two-mode ODE solution. The pulse is initialized at the slot entrance by the nonzero Gaussian amplitude `P(a)`. The physical pulse is then localized by Gaussian/native clock cutoffs.

This changes the highest-value forcing-ablation question from

> Can the growing pulse be generated without forcing?

into

> Can the homogeneous pulse hierarchy be left globally present, with Gaussian-small tails outside its active slots, while retaining smoothness, interaction control, and exact Navier-Stokes residual closure?

## 1. Source-backed pulse decomposition

At pinned source commit `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`:

- `PrimaryODE.primarySeed` initializes the two-mode state as `(P(a), 0)`.
- `PrimaryODE.primary` calls the ODE solver with physical forcing `(fun _ => 0)`.
- `PrimaryODE.homogeneous_forward_bound` controls the corresponding homogeneous evolution.
- `PrimaryPulseBounds.cutoffPulse` multiplies the homogeneous primary by `GaussianTailFlat.slotCutoff`.

So pulse amplification and pulse localization must be treated as separate mechanisms.

## 2. The old fixed-fraction tail assumption is discharged

`GaussianTailFlat.slotCutoff_deriv_support` places cutoff derivatives in

`L/5 <= |v-L/2| <= L/3`.

`GaussianTailFlat.reference_envelope_off_plateau` then bounds the envelope there by an exponential of the form

`exp(-c L)`

with positive source-defined coefficient when the reference parameters are positive.

The actual scaling machinery supplies slot length proportional to `S=n^2`, and `GaussianTailFlat.gaussian_beats_Q_power` formalizes that `poly(S) exp(-cS)` is bounded by every fixed real power of `Q=2^-n`.

Therefore the cutoff-error tail is source-backed Gaussian-small in the dyadic stage coordinate. The unresolved issue is not whether the cutoff derivative lies far enough from the midpoint.

## 3. Structural localization obstruction

For a homogeneous linear pulse

`x' = A(v)x`

and a scalar cutoff `y=chi x`, exact differentiation gives

`y' - Ay = chi' x`.

Thus a nonconstant temporal cutoff generally creates a nonzero source even if `x` itself is perfectly homogeneous.

There is a second obstruction. On a connected interval where the homogeneous linear ODE has uniqueness, a solution that vanishes on an earlier open interval is identically zero. A nontrivial homogeneous pulse therefore cannot have exact compact temporal support.

This kills one tempting lineage:

`zero source + exact temporal compactness + same nontrivial homogeneous pulse`.

It does **not** kill unforced pulse-based constructions. It forces them into a different architecture with globally present small tails or a different nonlinear mechanism.

## 4. What the next unforced experiment should actually do

A useful candidate should start with one label and remove only the temporal localization layer.

1. Keep the source-backed homogeneous primary unchanged on the central slot.
2. Extend its coefficient/frame evolution into neighboring regions as far as the source definitions permit.
3. Compute the exact difference between the cutoff and uncut residuals.
4. Measure/prove tail size where the old cutoff derivative lived.
5. Add a second pulse and inspect cross interactions.
6. Increase to a finite hierarchy with explicit stage separation.
7. Attempt all-order summability only after the finite-family interaction law is understood.

The first failure point is scientifically valuable: coefficient domain, moving-frame geometry, support collision, nonlinear cross term, divergence repair, pressure, or residual closure.

## 5. Parameter-window audit changed because upstream changed

The reproducibility source lock remains `8937a8f...`.

On 2026-09-10, upstream `openai/NavierStokesAndEuler` main was observed at `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, whose parent is the pinned commit. The current tree adds a `NaturalAxisRange.Parameters` layer for the broader printed/manuscript range

`h <= 1/100`, `j <= 1/20`,

while `NaturalAxisData.SmallParameters` still selects the tighter `h <= 1/1000` regime.

This means generic axis positivity/range lemmas are no longer the best place to spend effort. The sharper question is where the **selected full construction** still needs the tighter range.

The project keeps two exact conservative local certificates from the pinned source:

- `NaturalEntrance.base_source_lower`: `h < 99/17002`;
- `MatchingConeBounds.shape_axis_lower`: `h < 949/268040`.

These do not prove a wider full construction.

## 6. Engineering audit

The audit found two release-governance defects:

- `RELEASE_VALIDATION.json` still reported v5.2 test results on later branches;
- the CLI still emitted a hard-coded v5.2 report.

v5.5 fixes both. Fresh CI must validate v5.5 itself, and release metadata is now checked against the package version.

## Decision table

| Lineage | Decision | Reason |
| --- | --- | --- |
| Create canonical primary without in-slot forcing | SOURCE-BACKED | The source already does this |
| Prove cutoff errors are Gaussian-small | SOURCE-BACKED | Explicit cutoff support + Gaussian tail lemmas |
| Keep exact temporal compactness while removing source | KILL | Cutoff commutator + homogeneous uniqueness |
| Globally present Gaussian-small pulse tails | PROMOTE | Avoids the compact-support obstruction; interaction closure remains open |
| Claim unforced Navier-Stokes blowup | REJECT | Exact full residual closure and global construction are absent |
| Re-prove broad axis positivity at `h<=1/100` | DEPRIORITIZE | Current upstream already contains a broader manuscript-range layer |

## v5.6 target

The next release should implement a **cutoff residual atlas**. For each temporal/spacetime cutoff, record:

`field -> cutoff -> derivative channel -> exact residual term -> support -> Gaussian order -> cancellation partner -> downstream consumer`.

Then attempt a one-pulse no-cutoff extension and let the first exact obstruction determine the next research direction.
