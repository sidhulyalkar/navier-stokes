# Navier–Stokes Research Lab v5.2.0

Fail-closed research infrastructure for two coupled programs:

1. **Forcing ablation**: determine which components of the published forced singular construction can be weakened, transferred into initial data, or replaced by intrinsic dynamics.
2. **Automated blowup-mechanism discovery**: encode scaling, residual, stress, correction, and proof structure in a reusable search language for nonlinear PDEs.

## v5.2 focus

- GitHub-backed reproducibility and CI.
- An evidence-aware constraint ledger for the similarity parameter `h`.
- Explicit separation between cheap power-counting windows, manuscript assumptions, and concrete formalization constants.
- Fail-closed interval comparison for the pulse-tail vs backward-propagator exponents needed by the initial-data-transfer route.

## Scientific contract

`PROMOTE` means *survived the evaluator that emitted the label*. It does not mean proved. Unknown constants stay unknown. See `docs/CLAIMS.md` and `docs/RESEARCH_GOVERNANCE.md`.

## Run

```bash
python -m pip install -e . pytest
pytest -q
blowup-lab --out artifacts/v520
```
