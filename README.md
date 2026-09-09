# Navier–Stokes Mechanism Lab

A reproducible research program for studying **which pieces of the 2026 forced Navier–Stokes singularity construction are structurally necessary**, and for turning singularity proofs into a reusable search language for nonlinear PDEs.

This repository is not a claim of an unforced Navier–Stokes blowup proof. It is a fail-closed laboratory for generating, testing, killing, and formally tracking mechanisms.

## The two research questions

### 1. What survives if the forcing is weakened or removed?

We treat the published construction as a reference specimen and ask which ingredients can be replaced by intrinsic dynamics or encoded into smooth initial data.

Current highest-value route:

```text
late pulse seeding by force
        ↓
source-backed Gaussian pulse tails
        ↓
pull desired pulse states back to t = 0
        ↓
compare tail suppression vs backward amplification
        ↓
all-Sobolev / Gevrey summability
        ↓
nonlinear compatibility
        ↓
exact unforced residual closure
```

### 2. Can blowup mechanisms themselves become searchable objects?

The lab encodes a candidate as interacting layers:

```text
scaling → geometry → PDE balance → stress realization
        → corrections → residual closure → proof obligations
```

The long-range goal is a mechanism compiler that can transfer ideas across Navier–Stokes, Euler, MHD, Hall-MHD, Boussinesq, and related nonlinear PDEs.

## Current research frontier

### Pulse-transfer lineage

The OpenAI Lean source already formalizes a Gaussian envelope of the form

```text
exp(-C (t-t*)² / (2ℓ)) ≤ envelope(t) ≤ exp(-c (t-t*)² / (2ℓ)).
```

The unresolved step is to convert the slot scale `ℓ` into the pulse hierarchy/frequency variable and rigorously bound the cost of propagating a desired activation state backward to the true initial slice.

The decisive asymptotic comparison is

```text
|a_n(0)| ≲ exp(-c k_n^γ_tail + d k_n^δ_back).
```

No numerical values for `γ_tail` or `δ_back` are claimed until source-backed bounds exist.

### Similarity-parameter lineage

Elementary power counting gives the broad window

```text
0 < h < 1/6.
```

The manuscript works in a much smaller regime and the released Lean implementation uses a concrete `h ≤ 1/1000` small-parameter choice. The project is tracing theorem-by-theorem where that margin is actually consumed.

This can produce a useful result even if the final theorem cannot be extended: a precise map of which mechanism is responsible for each quantitative restriction.

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

`PROMOTE`, `HOLD`, and `KILL` are **research-allocation labels**, not theorem statuses.

See [`docs/CLAIMS.md`](docs/CLAIMS.md) and [`docs/RESEARCH_GOVERNANCE.md`](docs/RESEARCH_GOVERNANCE.md).

## Project map

- [`docs/PROJECT_OVERVIEW.md`](docs/PROJECT_OVERVIEW.md) — the fastest technical tour of the project.
- [`docs/RESEARCH_MAP.md`](docs/RESEARCH_MAP.md) — mechanism graph, active lineages, and decision gates.
- [`docs/RESEARCH_PROGRAM.md`](docs/RESEARCH_PROGRAM.md) — long-range research architecture.
- [`docs/FINDINGS_V5_2.md`](docs/FINDINGS_V5_2.md) — latest stable findings.
- [`docs/V5_3_PLAN.md`](docs/V5_3_PLAN.md) — current source-extraction plan.
- [`artifacts/`](artifacts/) — compact machine-readable evidence and experiment outputs.

## Repository workflow

- `main`: stable, reproducible research checkpoints.
- `research/vX.Y.Z-*`: active hypothesis lineages.
- Pull requests: scientific release boundaries with explicit claims/non-claims.
- Issues: independent research questions and falsification tracks.

Current active branch: `research/v5.3.0-source-extraction`.

## Run locally

```bash
python -m pip install -e .
pytest -q
blowup-lab --out artifacts/local
```

The code is intentionally designed to fail closed: unknown constants remain unknown, missing proof mechanisms cannot be silently ignored, and attractive numerical behavior cannot override a fatal mathematical invariant failure.
