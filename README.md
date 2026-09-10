# Navier–Stokes Mechanism Lab

A reproducible research program for studying **which pieces of the 2026 forced Navier–Stokes singularity construction are structurally necessary**, and for turning singularity proofs into a reusable search language for nonlinear PDEs.

This repository is not a claim of an unforced Navier–Stokes blowup proof. It is a fail-closed laboratory for generating, testing, killing, and formally tracking mechanisms.

## The two research questions

### 1. What survives if the forcing is weakened or removed?

The current source audit has sharpened this question substantially.

The canonical primary pulse inside one slot is already constructed as a **homogeneous zero-forcing two-mode ODE solution**. Its nonzero entry seed is the small Gaussian envelope value `P(a)`. The physical construction then multiplies that homogeneous pulse by temporal/spacetime cutoffs.

So the frontier is no longer “can forcing create the growing pulse?” It is:

```text
source-backed tiny entry seed
        ↓
homogeneous primary evolution inside a slot
        ↓
current construction: multiply by slot / clock cutoffs
        ↓
cutoff derivatives create localized residual/source terms
        ↓
new target: remove the cutoffs and keep globally present tiny tails
        ↓
control all cross-slot / cross-frequency interactions
        ↓
prove one smooth global initial datum contains the hierarchy
        ↓
exact unforced residual closure
```

There is an elementary structural obstruction to keeping both exact temporal compactness and zero forcing. For `x' = A(v)x` and `y = chi(v)x`,

```text
y' - A(v)y = chi'(v)x.
```

Moreover, uniqueness of the homogeneous linear ODE means a nonzero homogeneous pulse cannot vanish on an earlier time interval and then spontaneously appear. A successful unforced replacement therefore has to abandon exact temporal compactness or abandon this mechanism class.

### 2. Can blowup mechanisms themselves become searchable objects?

The lab encodes candidates as interacting layers:

```text
scaling → geometry → PDE balance → stress realization
        → pulse dynamics → localization → corrections
        → residual closure → proof obligations
```

The long-range goal is a mechanism compiler that can transfer ideas across Navier–Stokes, Euler, MHD, Hall-MHD, Boussinesq, and related nonlinear PDEs.

## Current research frontier

### Pulse localization lineage

Pinned Lean source establishes all of the following:

- the reference pulse has Gaussian growth/decay around the slot midpoint;
- the canonical primary is initialized by `primarySeed = (P(a), 0)`;
- the canonical primary solves the slot ODE with zero forcing;
- derivatives of the Gaussian slot cutoff live in the explicit region `L/5 <= |v-L/2| <= L/3`;
- the envelope is exponentially small there;
- Gaussian decay in the stage scale `S=n^2` beats every fixed real power of the dyadic scale `Q=2^-n`.

The next hard problem is global extension: can the homogeneous pulses remain present outside their assigned slots, with Gaussian-small tails, without destroying support geometry, nonlinear interaction bounds, summability, or exact residual closure?

### Similarity-parameter lineage

Elementary power counting gives the broad window

```text
0 < h < 1/6.
```

Two conservative source-derived local certificates from the pinned construction are now exact rationals:

```text
NaturalEntrance.base_source_lower:        h < 99/17002  ≈ 0.00582284
MatchingConeBounds.shape_axis_lower:      h < 949/268040 ≈ 0.00354052
```

These are sufficient local bounds only, not sharp or global thresholds.

An upstream check on 2026-09-10 found that OpenAI's current Lean tree now explicitly separates a broader printed/manuscript axis range (`h <= 1/100`, `j <= 1/20`) from the tighter selected `SmallParameters` range (`h <= 1/1000`). We therefore keep the original source lock for reproducibility and track upstream changes separately in `UPSTREAM_WATCH.json`.

The useful question is now: **which selected downstream construction requirements still consume the extra factor of ten?**

## Evidence ladder

Every result carries an evidence state:

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
- [`docs/FINDINGS_V5_5.md`](docs/FINDINGS_V5_5.md): current audit and research pivot.
- [`docs/V5_5_PLAN.md`](docs/V5_5_PLAN.md): active release plan.
- [`UPSTREAM_WATCH.json`](UPSTREAM_WATCH.json): upstream changes observed without mutating the reproducibility lock.
- [`artifacts/`](artifacts/): machine-readable evidence and experiment outputs.

## Repository workflow

- `main`: stable, reproducible research checkpoints.
- `research/vX.Y.Z-*`: active hypothesis lineages.
- pull requests: scientific release boundaries with explicit claims/non-claims.
- issues: independent research questions and falsification tracks.

Current active branch: `research/v5.5.0-path-bottleneck-pulse-propagator`.

## Run locally

```bash
python -m pip install -e .
pytest -q
blowup-lab --out artifacts/local
```

The code is designed to fail closed: unknown constants remain unknown, missing proof mechanisms cannot be silently ignored, attractive numerical behavior cannot override fatal mathematical invariants, and release metadata is checked for version drift.
