# 322. Global attraction for Wright-type delayed feedback

**Area:** Population dynamics and nonlinear delayed feedback

**Status:** 🔵 OPEN

**Last checked:** 2026-09-18

## Problem statement

Let $`f\in C^3(\mathbb R,\mathbb R)`$ satisfy $`f(0)=0`$ and $`u f(u)<0`$ for $`u\ne0`$. Assume that $`f`$ is bounded below and has at most one critical point; if a critical point exists, it is a local extremum. At every point with $`f'(u)\ne0`$, require the Schwarzian derivative to satisfy

```math
(Sf)(u)=\frac{f'''(u)}{f'(u)}
-\frac32\left(\frac{f''(u)}{f'(u)}\right)^2<0.
```

Suppose also that $`0<-f'(0)<\pi/2`$. For an arbitrary continuous history $`\phi:[-1,0]\to\mathbb R`$, consider the scalar delay equation

```math
x'(t)=f(x(t-1))\quad(t\ge0),
\qquad x(s)=\phi(s)\quad(-1\le s\le0).
```

**Must every such solution satisfy $`\lim_{t\to\infty}x(t)=0`$?**

This is the strict-parameter version of the generalized Wright conjecture in Liz–Pinto–Robledo–Trofimchuk–Tkachenko, Conjecture 1.2. The slope condition makes the zero equilibrium locally exponentially stable; the question concerns convergence from every history, with no smallness or sign restriction. No uniform convergence rate is requested. The delay is normalized to one: for delay $`\tau>0`$, time rescaling replaces the slope by $`\tau f'(0)`$. Later formulations also include the boundary $`-f'(0)=\pi/2`$; that extension belongs to the same problem family and is not counted separately.

## Application

Delayed density feedback models reproduction responding to an earlier population level. The original paper's Examples 1.4–1.5 transform food-limited growth and growth with a weak Allee effect into this class using logarithmic population coordinates. Attraction to zero then means return to the positive population equilibrium after any positive continuous population history. The conjecture asks whether a local stability calculation suffices to predict recovery even after a large disturbance, under the specified feedback-shape assumptions. Its significance is a general stability criterion across response functions; it does not assert that each illustrative biological model separately remains unresolved.

## References

1. Eduardo Liz, Manuel Pinto, Gonzalo Robledo, Sergei Trofimchuk and Victor Tkachenko, *Wright type delay differential equations with negative Schwarzian*, Discrete and Continuous Dynamical Systems 9(2) (2003), 309–321, [DOI](https://doi.org/10.3934/dcds.2003.9.309); [author manuscript](https://arxiv.org/pdf/math/0111285v2), March 5, 2002, §1, hypotheses (H1)–(H3), Conjecture 1.2, Theorems 1.1 and 1.3, and Examples 1.4–1.5.
2. István Balázs and Gergely Röst, *Hopf bifurcation for Wright-type delay differential equations: The simplest formula, period estimates, and the absence of folds*, Communications in Nonlinear Science and Numerical Simulation 84 (2020), 105188, [DOI](https://doi.org/10.1016/j.cnsns.2020.105188); [accepted manuscript](https://publicatio.bibl.u-szeged.hu/18524/3/31123767.pdf), January 14, 2020, §5 and Corollary 15.
3. Mauro Díaz, Karel Hasík, Jana Kopfová and Sergei Trofimchuk, *Global Stability of Wright-Type Equations with Negative Schwarzian*, SIAM Journal on Applied Dynamical Systems 25(2) (2026), 964–997, [DOI](https://doi.org/10.1137/25M1737298); [author manuscript](https://arxiv.org/pdf/2502.15965v1), February 21, 2025, §1, Conjecture 1, Theorem 1.4 and Corollary 1.7. The numbered locators refer to this manuscript.
4. Jan Bouwe van den Berg and Jonathan Jaquette, *A proof of Wright's conjecture*, Journal of Differential Equations 264(12) (2018), 7412–7462, [DOI](https://doi.org/10.1016/j.jde.2018.02.018); [institutional full text](https://research.vu.nl/ws/portalfiles/portal/119991482/A_proof_of_Wrights_conjecture.pdf), §1, especially Theorem 1.5.
5. Mostafa Adimy, Fabien Crauste, Anatoli Ivanov and Laurent Pujo-Menjouet, *Global stability and periodicity in a delay differential model*, Journal of Mathematical Analysis and Applications 561(1) (2026), 130555, [DOI](https://doi.org/10.1016/j.jmaa.2026.130555); [author manuscript](https://hal.science/hal-05363003v2), April 17, 2026, Eq. (1), §§3–4 and §5, especially Eq. (24) and §§5.3–5.4.
6. Eduardo Liz, *Clark's Equation: A Useful Difference Equation for Population Models, Predictive Control, and Numerical Approximations*, Qualitative Theory of Dynamical Systems 19 (2020), 71, [DOI](https://doi.org/10.1007/s12346-020-00405-1); [author-hosted full text](https://dma.uvigo.es/~eliz/pdf/QTDS2020.pdf), Eq. (1.3), §2.1 and §3. Restates the distinct discrete-time counterexamples of Jiménez López–Parreño (2016).

## Status review

**Literature check:** Open in cited literature; no later resolution located.

**Open in cited literature; no later resolution located as of 2026-09-18.** Searches covered generalized Wright and negative-Schwarzian terminology, author names, proof and counterexample claims, recent years, unrestricted dates, corrections and version histories. The 2025 manuscript published in 2026 explicitly retains the conjecture; Balázs–Röst provide independent specialist corroboration.

The general hypotheses give attraction when $`-f'(0)\le3/2`$. Díaz–Hasík–Kopfová–Trofimchuk extend this to $`-f'(0)\le37/24`$ for decreasing $`f`$, and cover the full range up to $`\pi/2`$ when $`f`$ is decreasing and $`f''(0)=0`$. Their conclusions leave general feedback shapes and the near-critical interval unresolved. The interval-arithmetic computations supporting their partial theorem were not rerun here.

The classical Wright equation, corresponding to $`f(u)=\alpha(e^{-u}-1)`$, was solved by van den Berg–Jaquette. Balázs–Röst rule out subcritical Hopf bifurcations under negative Schwarzian, but that local result does not exclude all distant periodic orbits. Counterexamples obtained after dropping the Schwarzian condition do not refute the stated conjecture. Adimy et al.'s coexisting-orbit constructions instead use $`z'(t)=-z(t)+Q(z(t-1))`$; their numerical examples assume only $`C^1`$ joins and do not establish the required negative-Schwarzian hypothesis. Clark-equation counterexamples concern a discrete recurrence. The [evidence record](../research/expansion-2026-09/candidates/generalized-wright-global-attraction.json) documents the precise scope comparisons and incomplete access to the original Clark paper.

[Entry 286](285-nicholson-local-global-stability.md) concerns Nicholson's particular positive-population equation with instantaneous decay. That term and its parameter-dependent local stability test distinguish it from the pure-delay function class here. [Entry 301](300-carrying-simplex-interior.md) asks for geometric smoothness in competitive population maps. Neither has the same mathematical assertion.

A publication refresh on September 18, 2026 rechecked status and upstream duplicates; see the [batch 4 audit](../research/expansion-2026-09/batch-04-review.md). No matching later resolution was located.
