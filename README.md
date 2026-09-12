# Navier–Stokes Mechanism Lab

A reproducible research program for studying **which pieces of the 2026 forced Navier–Stokes singularity construction are structurally necessary**, and for turning singularity proofs into a reusable search language for nonlinear PDEs.

This repository is not a claim of an unforced Navier–Stokes blowup proof. It is a fail-closed laboratory for generating, testing, killing, and formally tracking mechanisms.

## The two research questions

### 1. What survives if the forcing is weakened or removed?

The source audit now separates three mechanisms that were previously easy to blur together:

```text
tiny nonzero pulse entry seed
        ↓
homogeneous zero-forcing primary evolution on its native slot
        ↓
temporal / clock localization
        ↓
explicit cutoff residual channels
        ↓
correction + flatness machinery
```

Pinned `LinearWaveBounds.excludedSlotError` gives the exact local identity

```text
E_slot = Dfast(psi) * amplitude + (1-psi) * source.
```

For the primary residual class `source=0`, so only the cutoff-derivative commutator remains. Setting `psi=1` therefore removes this **specific principal localization error** exactly, provided the uncut coefficient still satisfies its solve identity.

The first obstruction is now precise: `PrimaryODE.solution` is represented by a differentiable extension to all real slot times, but the source proves the ODE identity only on the native finite interval `Icc(a,b)`, instantiated as `Icc(0,L)` for the primary pulse. Reusing that extension after deleting the cutoff is therefore not a source-backed global homogeneous solution.

Current promoted experiment:

```text
extend one pulse's actual frame/coefficient dynamics to a larger interval
        ↓
solve the homogeneous ODE there directly
        ↓
prove agreement on the original slot by uniqueness
        ↓
set temporal cutoff to one
        ↓
recompute every remaining residual channel
        ↓
only then test two pulses and a finite hierarchy
```

### 2. Can blowup mechanisms themselves become searchable objects?

The lab encodes candidates as interacting layers:

```text
scaling → geometry → PDE balance → stress realization
        → pulse dynamics → localization → corrections
        → residual closure → proof obligations
```

v5.6 adds a counterfactual cutoff-residual atlas so an agent cannot say “remove the cutoff” without inheriting the exact support, source, solve, and domain obligations that operation exposes.

## Current research frontier

### Cutoff residual lineage

Source-backed facts:

- canonical primary pulse is initialized by `primarySeed = (P(a), 0)`;
- its native-slot ODE uses zero physical forcing;
- slot-cutoff derivative support lies in `L/5 <= |v-L/2| <= L/3`;
- Gaussian decay there beats every fixed power of the dyadic stage scale;
- the general excluded-slot error has two channels: cutoff derivative and uncovered source;
- the primary source-zero specialization removes the uncovered-source channel;
- `psi=1` removes the principal localization error locally under the solve hypothesis;
- the existing differentiable extension is **not** proven to satisfy that homogeneous ODE outside the native interval.

The next theorem-sized target is therefore an **enlarged-interval one-pulse continuation**, not an infinite pulse hierarchy.

### Similarity-parameter lineage

Elementary power counting gives the broad window

```text
0 < h < 1/6.
```

Two conservative source-derived local certificates from the pinned construction are exact rationals:

```text
NaturalEntrance.base_source_lower:        h < 99/17002  ≈ 0.00582284
MatchingConeBounds.shape_axis_lower:      h < 949/268040 ≈ 0.00354052
```

These are sufficient local bounds only, not sharp or global thresholds.

An upstream check on 2026-09-10 found that OpenAI's current Lean tree separates a broader printed/manuscript axis range (`h <= 1/100`, `j <= 1/20`) from the tighter selected `SmallParameters` range (`h <= 1/1000`). The reproducibility lock remains pinned while the delta is tracked in `UPSTREAM_WATCH.json`.

## Evidence ladder

```text
EXPLORATORY
    ↓
SOURCE_EXTRACTED / REPRODUCED
    ↓
VALIDATED_BOUND
    ↓
FORMALIZED
```

`PROMOTE`, `HOLD`, and `KILL` are research-allocation labels, not theorem statuses.

See [`docs/CLAIMS.md`](docs/CLAIMS.md) and [`docs/RESEARCH_GOVERNANCE.md`](docs/RESEARCH_GOVERNANCE.md).

## Project map

- [`docs/PROJECT_OVERVIEW.md`](docs/PROJECT_OVERVIEW.md): concise technical tour.
- [`docs/RESEARCH_MAP.md`](docs/RESEARCH_MAP.md): mechanism graph and active decision gates.
- [`docs/FINDINGS_V5_6.md`](docs/FINDINGS_V5_6.md): latest source audit and first no-cutoff obstruction.
- [`docs/V5_6_PLAN.md`](docs/V5_6_PLAN.md): current release gates.
- [`UPSTREAM_WATCH.json`](UPSTREAM_WATCH.json): upstream changes observed without mutating the reproducibility lock.
- [`artifacts/`](artifacts/): machine-readable evidence and experiment outputs.

## Repository workflow

- `main`: stable, reproducible research checkpoints.
- `research/vX.Y.Z-*`: active hypothesis lineages.
- pull requests: scientific release boundaries with explicit claims/non-claims.
- issues: independent research questions and falsification tracks.

Current active branch: `research/v5.6.0-cutoff-residual-atlas`.

## Run locally

```bash
python -m pip install -e .
pytest -q
blowup-lab --out artifacts/local
```

The code is designed to fail closed: unknown constants remain unknown, missing proof mechanisms cannot be silently ignored, attractive numerical behavior cannot override fatal mathematical invariants, and release metadata is checked for version drift.
