# Project overview

## Why this repository exists

OpenAI's 2026 result supplies a concrete, formalized finite-time blowup construction for forced three-dimensional incompressible Navier–Stokes. That changes the research landscape: instead of asking only whether singularity is possible under the Clay formulation, we can ask **which mechanisms in a known singular construction are essential, which are replaceable, and which can be transferred to other PDEs**.

This repository explores that question with a deliberately adversarial workflow.

## Research program A: weaken the forcing

The object under study is a family

```text
(u_λ, p_λ, f_λ)
```

with exact residual

```text
R_λ = ∂ₜu_λ + (u_λ·∇)u_λ - νΔu_λ + ∇p_λ - f_λ.
```

Reducing `f_λ` is meaningful only if residual closure and the singularity observables survive. Simply multiplying the published force by a scalar does not preserve the PDE.

Current leading hypotheses:

1. **Initial-data pulse transfer** — replace externally seeded late pulses with an infinite hierarchy encoded in smooth initial data.
2. **Unforced shooting** — construct earlier unforced dynamics that enter the singular trajectory's admissible manifold.
3. **Profile/globalization redesign** — change the core/annular construction so less corrective forcing is required in the first place.

Each route carries replacement obligations. Removing a mechanism without replacing what it mathematically accomplishes is a hard failure.

## Research program B: mechanism discovery

The project abstracts blowup constructions into reusable components:

| Layer | Question |
|---|---|
| Scaling | Which exponents can coexist at leading order? |
| Geometry | Where are the core, annulus, exterior, and reserved correction regions? |
| Balance | Which PDE terms cancel or dominate in each region? |
| Stress | Which oscillatory families realize the required mean quadratic stress? |
| Corrections | How does each residual defect get pushed to higher order? |
| Proof | What exact obligations remain before theorem status? |

A candidate is useful even when it dies. A failed lineage tells us which constraint or mechanism is actually binding.

## Most interesting current deductions

### 1. The broad scaling window is much larger than the implemented one

Cheap balance plus energy considerations give

```text
β_r = 1/2
α_r = 1/2
α_t = 1 - β_z
1/3 < β_z < 1/2
```

and therefore, with `β_z = 1/2 - h`, the elementary window

```text
0 < h < 1/6.
```

The published construction works in a much smaller regime, and the Lean implementation uses a concrete `h ≤ 1/1000` small-parameter choice. The gap is now a research object rather than a footnote.

### 2. Pulse tails are source-backed Gaussian objects

The Lean source proves a Gaussian-in-slot-time envelope

```text
exp(-C (t-t*)²/(2ℓ)) ≤ E(t) ≤ exp(-c (t-t*)²/(2ℓ)).
```

This makes the initial-data-transfer problem precise. We need to derive how `ℓ` scales with pulse hierarchy/frequency and compare the resulting suppression against the inverse propagator cost.

### 3. The right unforced question is not "set f = 0"

The meaningful question is whether the functions and mechanisms can be **redesigned** so that

```text
∂ₜu + (u·∇)u - νΔu + ∇p = 0
```

while retaining smooth initial data, finite energy before the singular time, and blowup of the required norm. That is an exact residual-closure problem.

## What this project does not claim

- It does not independently certify the full OpenAI proof.
- It does not currently reduce the actual published forcing in a rigorous norm.
- It does not prove an unforced Navier–Stokes singularity.
- It does not treat search-engine `PROMOTE` labels as mathematical evidence.

The value of the project is in turning ambitious conjectures into **small, source-locked, killable research questions**.

## What to read next

1. `RESEARCH_MAP.md` for the active mechanism graph.
2. `FINDINGS_V5_2.md` for the latest stable deductions.
3. `V5_3_PLAN.md` for the current quantitative extraction work.
4. `CLAIMS.md` for the precise evidence boundary.
