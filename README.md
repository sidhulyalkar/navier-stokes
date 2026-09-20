# Navier–Stokes Mechanism Lab

A reproducible research program for studying **which mechanisms in the 2026 forced Navier–Stokes singularity construction are structurally necessary**, and whether removing proof/localization machinery can be turned into a genuinely smaller-forcing construction.

This repository is **not** a claim of an unforced Navier–Stokes blowup proof. It is a fail-closed mechanism laboratory: promoted claims are tied to a pinned source revision, explicit theorem boundary, and reproducible audit.

## Reproducibility lock

```text
openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538
leanprover/lean4:v4.34.0-rc2
```

The reference result under study is a smooth **forced** finite-time singularity construction.

## Current frontier

### v5.10: factor-two schedule growth is removable

The source diagonal selector uses

```text
a(n+1) = max(local(n+1), 2*a(n)).
```

The project replaces this with

```text
s(0)   = max(1, local(0))
s(n+1) = max(local(n+1), s(n)+1).
```

Source-locked Lean now carries the weaker selector through numerical admissibility, finite heterogeneous cutoff bounds, physical local-q support and smooth zero extension, the common potential/direct/pressure schedule, vanishing mixed residual jets, and the final forced singular-candidate replay.

The factor-two growth certificate is therefore unnecessary for this candidate construction. This is an **M2 mechanism-elimination result**, not a force-norm reduction.

See [docs/CURRENT_STATUS.md](docs/CURRENT_STATUS.md) for exact audit IDs.

### v5.11: pair the old and new constructions

The active lane removes a major comparison confound. Instead of independently choosing two existential schedules, v5.11 derives strict and doubling schedules from the **same** raw potential/direct/pressure stage families, gain/loss functions, aggregated cutoff constants/log powers, physical support floor, finite background, and finite residual data.

Both schedules satisfy the source-compatible local cutoff estimates, smooth mixed sums, and endpoint-flat residual conclusions. They obey

```text
aStrict(0) = aDouble(0)
aStrict(1) < aDouble(1)
aStrict(j) <= aDouble(j)
```

for the paired selection.

A stronger stage-two theorem chooses a common admissible `B >= 2` so

```text
strict:   B, B+1, B+2
doubling: B, 2B,  4B.
```

At

```text
q* = 1 / (2*aStrict(2))
```

the pinned scalar cutoff is **exactly 1** for the strict schedule and **exactly 0** for the doubling schedule.

That proves the localization functions can differ maximally at an explicit radius. It still does **not** prove the actual physical fields differ there: the raw positive-stage field could vanish at that point. Closing that nonvanishing/observable gap is the current P2b target.

## Why the force comparison is still open

The source's exact scalar chain rule retains the cutoff scale:

```text
D^n[cutoff(a*q)] = a^n * cutoff^(n)(a*q).
```

But the published cut-stage estimate deliberately converts the scale power to a scale-uniform `q^(-n)` loss. That is ideal for proving existence and convergence but erases the information needed to order strict and doubling schedules.

The next quantitative layer therefore needs to preserve explicit `a^n` factors on the paired collar, then feed the resulting field difference through the source-native Navier–Stokes residual identity.

## Claim boundary

Established:

- factor-two schedule growth is unnecessary through the final forced singular candidate;
- strict and doubling schedules can be paired from identical finite-stage data;
- the paired scalar cutoff profiles can be explicitly separated.

Not established:

- that the paired actual physical fields are nonidentical;
- that one paired collar residual is smaller;
- a smaller final force in any standard norm;
- a force norm tending to zero;
- an unforced Navier–Stokes singularity.

## Project map

- [docs/CURRENT_STATUS.md](docs/CURRENT_STATUS.md): canonical current state and exact audit ledger.
- [docs/CLAIMS.md](docs/CLAIMS.md): strict scientific claim boundary.
- [docs/RESEARCH_MAP.md](docs/RESEARCH_MAP.md): mechanism graph and decision gates.
- [docs/PROJECT_OVERVIEW.md](docs/PROJECT_OVERVIEW.md): technical tour.
- [docs/RESEARCH_GOVERNANCE.md](docs/RESEARCH_GOVERNANCE.md): promotion and falsification rules.
- [artifacts/](artifacts/): machine-readable evidence and experiment outputs.

Historical `FINDINGS_V5_*` files are retained as an audit trail, not as the authoritative current status.

## GitHub workflow

- `main`: stable reproducible checkpoints.
- `research/vX.Y.Z-*`: active hypothesis lineages.
- issues: falsifiable research questions and explicit kill rules.
- pull requests: scientific promotion boundaries.
- pinned CI: recompiles formal claims against the exact upstream source and Lean revision.

Primary active lane: issue **#17**, paired strict-vs-doubling candidates and collar residual comparison.

## Run locally

```bash
python -m pip install -e .
pytest -q
blowup-lab --out artifacts/local
```

Unknown constants stay unknown, failed proof obligations stay failed, and a changed estimate is never relabeled as force reduction without a direct physical comparison.
