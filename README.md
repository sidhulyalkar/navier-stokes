# Navier–Stokes Mechanism Lab

A reproducible research program for studying **which mechanisms in the 2026 forced Navier–Stokes singularity construction are structurally necessary**, and whether removable proof/localization machinery can lead to a genuinely smaller forcing construction.

This repository is **not** a claim of an unforced Navier–Stokes blowup proof. It is a fail-closed mechanism laboratory: promoted claims are tied to a pinned source revision, an explicit theorem boundary, and reproducible CI.

## Reproducibility lock

```text
openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538
leanprover/lean4:v4.34.0-rc2
```

The reference result under study is a smooth **forced** finite-time singularity construction.

## Current frontier

### v5.9: canonical cutoff-scale comparison

Source-locked Lean formalizes a deterministic least-admissible local cutoff scale and canonical schedule comparison. Stronger certified gain cannot worsen the canonical schedule. The project also proves:

- an exact criterion for strict integer-scale crossing;
- a criterion for strict improvement to survive the source doubling envelope; and
- a constant-cancelling scale-relaxation theorem that does not assign fake values to existential multiplicative constants.

Qualified audit: `34784849248`.

### v5.10: remove factor-two schedule growth

The source constructs diagonal scales with

```text
a(n+1) = max(local(n+1), 2*a(n)).
```

v5.10 replaces this by

```text
s(0)   = max(1, local(0))
s(n+1) = max(local(n+1), s(n)+1).
```

The following layers are now source-locked and formalized:

1. **Numerical selector:** the weaker schedule stays positive, strictly monotone, divergent, preserves every local admissibility obligation, and is pointwise no larger than the source doubling schedule. Audit `34785230674`.
2. **Finite heterogeneous cutoff bounds:** the source-style analytic cutoff estimate survives unchanged with the weaker schedule. Audit `34785248912`.
3. **Physical local-q support and smooth zero extension:** the actual local validity floor, positive-stage cut bounds, and smooth extension to all preterminal spacetime survive without factor-two growth. Audit `34936977665`.

The next theorem-sized target is the mixed three-component schedule, followed by residual vanishing and a parallel final-candidate theorem.

## Why this matters

The downstream source proofs audited so far consume positivity/monotonicity, divergence of the cutoff scales, support separation, smooth sums, extension data, residual vanishing, angular divergence, and origin blowup. The factor-two certificate is carried through intermediate APIs, but is not visibly consumed by those final calls.

If the chain closes through the final singular candidate, factor-two growth will be identified as removable proof/localization architecture. That would **not** yet imply a smaller force norm.

The cut field is `χ(a_j q) A_j`. Decreasing `a_j` moves and broadens the transition collar while changing cutoff-derivative factors and the uncut field sampled there. A force-size claim requires a direct residual/force comparison.

## Secondary quantitative lane

The pinned exponent ledger exposes a candidate positive-stage margin

```text
h * (3/5 - kappa) = 59999/100000 * h,
kappa = 1/100000.
```

Several low-level statements qualified, but the attempted literal boosted `StageEstimates`/actual-candidate adapter did not compile source-locked. That experiment remains blocked and secondary to v5.10.

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

## Project map

- [`docs/CURRENT_STATUS.md`](docs/CURRENT_STATUS.md): canonical current state and exact audit IDs.
- [`docs/CLAIMS.md`](docs/CLAIMS.md): scientific claim boundary.
- [`docs/RESEARCH_MAP.md`](docs/RESEARCH_MAP.md): mechanism tracks and decision gates.
- [`docs/PROJECT_OVERVIEW.md`](docs/PROJECT_OVERVIEW.md): technical tour.
- [`docs/RESEARCH_GOVERNANCE.md`](docs/RESEARCH_GOVERNANCE.md): promotion and falsification rules.
- [`UPSTREAM_WATCH.json`](UPSTREAM_WATCH.json): observed upstream changes without mutating the reproducibility lock.

Historical `FINDINGS_V5_*` files are an audit trail, not the authoritative current status.

## GitHub workflow

- `main`: stable reproducible checkpoints.
- `research/vX.Y.Z-*`: hypothesis lineages.
- issues: falsifiable research questions and kill rules.
- pull requests: scientific promotion boundaries.
- pinned CI: recompiles promoted formal claims against the exact upstream SHA and Lean version.

Primary active lane: issue **#15**, factor-two diagonal schedule growth elimination.

## Run locally

```bash
python -m pip install -e .
pytest -q
blowup-lab --out artifacts/local
```

The repository is designed to fail closed: unknown constants stay unknown, failed proof obligations stay visible, and stronger estimates are never relabeled as force reduction without a direct physical comparison.
