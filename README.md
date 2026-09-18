# Navier–Stokes Mechanism Lab

A reproducible research program for studying **which mechanisms in the 2026 forced Navier–Stokes singularity construction are structurally necessary**, and whether any removable proof/localization machinery can be converted into a genuinely smaller forcing construction.

This repository is **not** a claim of an unforced Navier–Stokes blowup proof. It is a fail-closed mechanism laboratory: every promoted claim is tied to a pinned source revision, explicit theorem boundary, and reproducible audit.

## Reproducibility lock

```text
openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538
leanprover/lean4:v4.34.0-rc2
```

The reference result under study is a smooth **forced** finite-time singularity construction. The long-term question is how much of that forcing/localization architecture is actually necessary.

## Current frontier

The project has moved from broad mechanism mapping into a concrete M2 elimination experiment.

### v5.9: canonical cutoff-scale comparison

We formalized a deterministic least-admissible local cutoff scale and canonical schedule comparison. Stronger certified gain cannot worsen the canonical schedule. We also proved:

- an exact criterion for strict integer-scale crossing;
- a criterion for that strict improvement to survive the recursive schedule envelope; and
- a constant-cancelling scale-relaxation theorem that does not invent values for existential multiplicative constants.

Pinned audit: `34784849248`.

### v5.10: test whether factor-two schedule growth is unnecessary

The source constructs diagonal scales with

```text
a(n+1) = max(local(n+1), 2*a(n)).
```

We replaced this by the minimal strict envelope

```text
s(0)   = max(1, local(0))
s(n+1) = max(local(n+1), s(n)+1).
```

Source-locked Lean proves that the weaker schedule remains positive, strictly monotone, tends to infinity, preserves all numerical local admissibility requirements, and is pointwise no larger than the source doubling schedule.

Pinned audit: `34785230674`.

The finite heterogeneous cutoff-bound layer also survives without the factor-two condition.

Pinned audit: `34785248912`.

The actual local-`q` validity region and smooth zero-extension layer also survives without factor-two growth (audit `34936977665`). The mixed three-component schedule and mixed residual-vanishing theorem also qualify without factor-two growth (audits `34937994783` and `34938088599`). Finally, the pinned final singular-candidate proof itself has been replayed without the factor-two schedule-growth certificate (audit `35299948373`).

## Why this matters

The final candidate assembly visibly uses positivity/monotonicity, divergence of the cutoff scales, support separation, smooth sums, extension data, residual vanishing, angular divergence, and origin blowup. The source carries a factor-two growth certificate through intermediate APIs, but the downstream calls audited so far do not visibly consume it.

The v5.10 theorem chain now establishes that factor-two schedule growth is unnecessary as a construction rule through the final forced singular candidate. This is an M2 mechanism-elimination result. It does **not** yet establish that the minimal `+1` selector chooses a numerically different schedule on the actual source data, nor does it establish a smaller force norm.

A source-locked strict-separation theorem now shows that for any requested initial floor, one can choose a common admissible floor at least that large for which the minimal strict and canonical doubling selectors already differ at stage 1 (audit `35372821347`). This is an existence theorem in the chosen floor, not a claim that the source/default `lower = 1` schedules differ.

The next target is controlled pairing: generate both schedules from the same aggregated cutoff constants and the same finite-stage fields, then compare the changed transition collar. Changing `a_j` changes both cutoff derivative factors and the position/width of the collar, so a force-size claim still requires a direct comparison of the resulting residual/forcing fields.

## Secondary quantitative lane

The pinned exponent ledger exposes a candidate common positive-stage gain margin

```text
h * (3/5 - kappa) = 59999/100000 * h,
kappa = 1/100000.
```

Several low-level slack/gain statements qualified, but the attempted literal boosted `StageEstimates`/actual-candidate adapter did not compile source-locked. That experiment remains a secondary blocked lane rather than a promoted result.

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

## Project map

- [`docs/CURRENT_STATUS.md`](docs/CURRENT_STATUS.md): canonical current state, qualified audits, active blockers, and milestone ladder.
- [`docs/CLAIMS.md`](docs/CLAIMS.md): strict scientific claim boundary.
- [`docs/RESEARCH_MAP.md`](docs/RESEARCH_MAP.md): mechanism graph and active decision gates.
- [`docs/PROJECT_OVERVIEW.md`](docs/PROJECT_OVERVIEW.md): technical tour.
- [`docs/RESEARCH_GOVERNANCE.md`](docs/RESEARCH_GOVERNANCE.md): promotion and falsification rules.
- [`UPSTREAM_WATCH.json`](UPSTREAM_WATCH.json): observed upstream changes without mutating the reproducibility lock.
- [`artifacts/`](artifacts/): machine-readable evidence and experiment outputs.

Historical `FINDINGS_V5_*` files are retained as an audit trail, not as the authoritative current status.

## GitHub workflow

- `main`: stable reproducible checkpoints.
- `research/vX.Y.Z-*`: active hypothesis lineages.
- issues: falsifiable research questions and explicit kill rules.
- pull requests: scientific promotion boundaries.
- pinned CI workflows: source-lock every formal claim against the exact upstream revision and Lean version.

Primary active lane: issue **#17**, paired strict-vs-doubling candidates and collar residual comparison. Issue #15 is closed as completed.

## Run locally

```bash
python -m pip install -e .
pytest -q
blowup-lab --out artifacts/local
```

The repository is designed to fail closed: unknown constants stay unknown, missing mechanisms cannot be silently ignored, attractive numerics cannot override failed proof obligations, and stronger estimates are never relabeled as force reduction without a direct physical comparison.
