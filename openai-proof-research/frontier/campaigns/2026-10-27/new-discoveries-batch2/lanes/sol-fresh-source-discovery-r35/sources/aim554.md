# 554. Sharp asymptotic constant for rational approximation of fractional inverse powers

**Area:** Rational approximation and numerical analysis

**Status:** ✅ SOLVED

**Last checked:** 2026-10-13

## Problem statement

Fix $`0<a<b<\infty`$ and $`0<\gamma<1`$. Let

```math
E_{n-1,n}(a,b;\gamma)=\inf_{p,q}\max_{x\in[a,b]}\left|x^{-\gamma}-\frac{p(x)}{q(x)}\right|,
```

where $`p,q`$ are real polynomials with $`\deg p\le n-1`$, $`\deg q\le n`$, and $`q`$ has no zeros on $`[a,b]`$.

Put

```math
k=\frac{\sqrt b-\sqrt a}{\sqrt b+\sqrt a},\qquad
K(k)=\int_0^{\pi/2}\frac{d\theta}{\sqrt{1-k^2\sin^2\theta}},\qquad
\mu(k)=\frac{\pi K(\sqrt{1-k^2})}{2K(k)}.
```

Prove or disprove the Braess–Hackbusch conjecture

```math
\lim_{n\to\infty} e^{2n\mu(k)}E_{n-1,n}(a,b;\gamma)
=4(ab)^{-\gamma/2}\sin(\pi\gamma).
```

The interval and exponent are fixed as $`n\to\infty`$. The target is absolute uniform error, with no restriction on poles outside the approximation interval.

## Application

Rational approximations of fractional inverse powers are used to approximate fractional diffusion operators and related matrix functions. A sharp leading constant would turn a known asymptotic convergence rate into a more precise degree-versus-accuracy prediction.

## References

1. D. Braess and W. Hackbusch, [On the approximation of Stieltjes functions by exponential sums and rational functions with applications to partial differential equations](https://doi.org/10.1007/s00211-025-01523-1), *Numerische Mathematik* **158** (2026), 455–490. Conjecture 4.8, equation (4.20); Section 4.1 defines $`\mu`$.
2. [Author-hosted revised preprint](https://files-www.mis.mpg.de/mpi-typo3/preprints/2024/preprint2024_10.pdf), revised November 2025.

## Status review

**Resolution reviewed 2026-10-13:** [Kaiwen Jin's manuscript](../research/solutions/554-stieltjes-rational-asymptotic-constant/paper/main.pdf) establishes the full original target. Affirmative: the exact Stieltjes rational minimax asymptotic constant.

**Independent review:** the [complete per-problem audit](../research/solution_reviews/2026-10-13-yui-prs/554-review.md) reconstructs the argument, compares its hypotheses and quantifiers with the original statement, and checks the cited sources and accompanying materials. The review was carried out by independent Codex AI agents during maintainer processing; it does not assert human peer review or Lean verification.

The reviewed submission is [PR #84](https://github.com/MColbrook/AIM/pull/84) at `5461765e0fc13968ceb5767db690615ffbe1d2e2`. The original problem statement at `c9929805cece044705abaaebe1cebddac1ba11a6` was compared with its unchanged current form. The proof and documented independent audit meet the repository's **Solved** criterion; the original problem page and ID are retained.
