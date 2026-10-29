# 597. Entropy chain rule on nonsmooth nonconvex Lipschitz domains

**Area:** Numerical analysis of diffusion and optimal transport

**Status:** ✅ SOLVED

**Last checked:** 2026-10-13

## Problem statement

Let $`\Omega\subset\mathbb R^d`$ be a bounded Lipschitz domain, $`T>0`$, $`V\in C^2(\overline\Omega)`$ and $`\pi=e^{-V}`$. Define

```math
E(\rho)=\int_\Omega(\rho\log\rho-\rho+1+\rho V)\,dx,
```

with $`0\log0=0`$. Consider nonnegative densities $`\rho\in C([0,T];L^1_w(\Omega))`$ of fixed positive mass, and a flux $`F\in L^1((0,T)\times\Omega;\mathbb R^d)`$. Here $`L^1_w`$ carries its weak topology. Assume $`E(\rho(0))<\infty`$ and the continuity equation with no boundary flux, in the precise weak form

```math
\int_0^T\!\int_\Omega(\rho\,\partial_t\varphi+F\cdot\nabla\varphi)\,dx\,dt
=\int_\Omega\rho(T)\varphi(T)\,dx-\int_\Omega\rho(0)\varphi(0)\,dx
```

for every $`\varphi\in C^1([0,T]\times\overline\Omega)`$. Suppose moreover that the kinetic action and Fisher information are finite:

```math
\int_0^T\!\int_\Omega\left(\frac{|F|^2}{\rho}+4\pi\left|\nabla\sqrt{\rho/\pi}\right|^2\right)\,dx\,dt<\infty.
```

The quotient is zero at $`(\rho,F)=(0,0)`$ and infinite when $`\rho=0`$, $`F\ne0`$; the Fisher term requires $`\sqrt{\rho/\pi}\in H^1(\Omega)`$ almost everywhere in time.

Prove or disprove that $`t\mapsto E(\rho(t))`$ is absolutely continuous and satisfies

```math
\frac{d}{dt}E(\rho(t))=\int_\Omega F(t)\cdot\nabla\log(\rho(t)/\pi)\,dx\quad\text{for almost every }t.
```

Interpret the integrand as

```math
(F/\sqrt\rho)\cdot(2\nabla\sqrt\rho+\sqrt\rho\,\nabla V),
```

with $`F/\sqrt\rho=0`$ on $`\{\rho=0\}`$. The stated estimates make this integrable. The target is Proposition A.1 of [1] for general Lipschitz domains, including those that are both nonconvex and nonsmooth, without additional bounds on the density or gradient-approximation assumptions.

## Application

This chain rule identifies limits satisfying an energy-dissipation inequality as solutions of the Fokker–Planck equation. Extending it would support convergence proofs for structure-preserving diffusion schemes on meshes of nonconvex polygonal and polyhedral domains.

## References

1. C. Cancès, L. Monsaingeon and A. Natale, [Discretizing the Fokker–Planck equation with second-order accuracy: a dissipation driven approach](https://doi.org/10.1007/s00211-026-01537-3), *Numerische Mathematik* **158** (2026), 1513–1563. Equations (1.5)–(1.7), Proposition A.1 and the following open-problem statement, pages 1515–1516 and 1556–1557. [Preprint](https://arxiv.org/abs/2410.03367).
2. J.-B. Casteras, M. Flaim and L. Monsaingeon, [Entropy and Fisher information in non-convex domains: one chain to rule them all](https://arxiv.org/abs/2512.05826), 2025. Theorems 3–4 and the concluding discussion of Section 3.

## Status review

**Resolution reviewed 2026-10-13:** [Kaiwen Jin's manuscript](../research/solutions/597-entropy-chain-rule-lipschitz/paper/manuscript.pdf) establishes the full original target. Exact prescribed-flux entropy chain rule with vacuum on every bounded Lipschitz domain under only the original estimates.

**Independent review:** the [complete per-problem audit](../research/solution_reviews/2026-10-13-yui-prs/597-review.md) reconstructs the argument, compares its hypotheses and quantifiers with the original statement, and checks the cited sources and accompanying materials. The review was carried out by independent Codex AI agents during maintainer processing; it does not assert human peer review or Lean verification.

The reviewed submission is [PR #68](https://github.com/MColbrook/AIM/pull/68) at `6af624cf8fca3a9197fbf70ba82938b610e23cb7`. The original problem statement at `c9929805cece044705abaaebe1cebddac1ba11a6` was compared with its unchanged current form. The proof and documented independent audit meet the repository's **Solved** criterion; the original problem page and ID are retained.
