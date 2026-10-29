# 495. Support growth of the information-maximizing binomial prior

**Area:** Statistical inference and information theory

**Status:** 🔵 OPEN

**Last checked:** 2026-09-23

## Problem statement

For each integer $`n\ge1`$, let a parameter $`\Theta\in[0,1]`$ have probability law $`\pi`$, and observe

```math
Y\mid\Theta=\theta\sim\mathop{\mathrm{Binomial}}\nolimits(n,\theta).
```

Write $`b_{n,y}(\theta)=\binom ny\theta^y(1-\theta)^{n-y}`$, using $`0^0=1`$, and $`q_\pi(y)=\int b_{n,y}(\theta)\,\pi(d\theta)`$. Define the mutual information, with natural logarithms, by

```math
I_n(\pi)=\sum_{y=0}^n\int_{[0,1]} b_{n,y}(\theta)
\log\frac{b_{n,y}(\theta)}{q_\pi(y)}\,\pi(d\theta).
```

Terms on events of zero probability contribute zero. Let $`\pi_n^*`$ maximize $`I_n`$ over all Borel probability laws on $`[0,1]`$. This maximizer is known to be unique and finitely supported; put $`K_n=|\mathop{\mathrm{supp}}\nolimits\pi_n^*|`$.

Prove or disprove the binomial case of the optimal-prior scaling conjecture:

```math
\lim_{n\to\infty}\frac{\log K_n}{\log n}=\frac23,
\qquad\text{equivalently }K_n=n^{2/3+o(1)}.
```

The target concerns the exact maximizing law at every $`n`$. A law attaining capacity within a vanishing error, or numerical support counts up to a fixed $`n`$, does not establish it. This logarithmic-exponent assertion does not additionally demand a limiting constant for $`K_n/n^{2/3}`$.

## Application

Here $`Y`$ is the sufficient statistic from $`n`$ independent coin flips with an unknown success probability. The optimizing prior maximizes expected information gained about that probability. The conjecture quantifies how its finite representation grows with the sample size. The same optimization describes a binomial communication channel; its support is the set of distinct input probability levels needed for exact capacity.

## References

1. Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press (2025), §13.3, p.248, equations (13.8)–(13.10) and the following open-problem discussion. [Author manuscript](https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf), dated 16 August 2024; [published book](https://doi.org/10.1017/9781108966351).
2. M. C. Abbott and B. B. Machta, *A Scaling Law From Discrete to Continuous Solutions of Channel Capacity Problems in the Low-Noise Limit*, Journal of Statistical Physics **176** (2019), 214–227. [Article](https://doi.org/10.1007/s10955-019-02296-2), equation (1) and §4, pp.222–223. The binomial discussion uses a Gaussian approximation and numerical evidence.
3. A. Favano, M. Baniasadi, I. Zieder, L. Barletta and A. Dytso, *The Binomial Channel: On Capacity, Optimal Inputs, and Beta-Binomial Approximation*, [arXiv:2607.02683v2](https://arxiv.org/abs/2607.02683v2), 2026 preprint, §VI.B, Corollary 2; §§VI.F–VI.I, Theorems 6 and 8; §VII.

## Status review

**Open in the cited book; no matching later resolution located.** The 2026 preprint gives bounds of orders $`\sqrt{n\log\log n}`$ and $`n`$ for $`K_n`$, leaving the displayed exponent undetermined. These weaker bounds do not justify a Partial label for this limit assertion.

The book's conjectural relation $`\max_\pi I_n(\pi)=\tfrac34\log K_n+o(\log K_n)`$, together with the known capacity asymptotic $`\max_\pi I_n(\pi)=\tfrac12\log n+O(1)`$, yields the exponent $`2/3`$. The 2026 paper's p.5 instead prints $`\Theta(n^{3/4})`$, whereas its numerical discussion plots capacity against log support. That discrepancy is recorded explicitly; neither numerical fit settles the target. The 2019 physical derivation is not treated as a rigorous binomial resolution: the later book explicitly retains this case as open.

The 23 September 2026 review searched later papers and announcements, including indexed arXiv, Zenodo, GitHub and Palomar results. No full-scope proof or counterexample was located; registry searches were not exhaustive exports.
