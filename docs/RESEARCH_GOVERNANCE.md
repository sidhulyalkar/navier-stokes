# Research governance

The repository is the canonical ledger for this project.

## Branching

- `main`: stable, reproducible research snapshots only.
- `research/vX.Y.Z-*`: active hypothesis/mechanism work.
- `release/vX.Y.Z`: optional release-hardening branches.

## Required release evidence

Every research release should include:

1. source lock(s) for external papers/formalizations;
2. explicit claims and non-claims;
3. generated experiment artifacts;
4. tests/CI;
5. proof obligations for theorem-level claims;
6. a short findings document containing killed hypotheses as well as promoted ones.

`PROMOTE` means only that a candidate survived the evaluator that produced the label. It never means theorem, validated numerics, or physical truth unless the artifact explicitly upgrades the evidence level.

## Agent policy

Agent-generated conjectures enter as `EXPLORATORY`. They may be upgraded only by reproducible symbolic derivation, rigorous numerical bounds, source-backed theorem extraction, or formal proof. Unknown constants remain unknown.
