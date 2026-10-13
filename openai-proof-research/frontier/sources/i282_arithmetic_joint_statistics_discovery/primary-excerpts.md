# I282 — Primary statement notes and exact interfaces

2026-10-12. Statements are paraphrased and formulas use this report's notation. These are source contracts, not audits of the stipulated upstream results. Snapshot filenames and full immutable URLs are also bound in [input-authentication.json](../../experiments/i282_arithmetic_joint_statistics_discovery/input-authentication.json). No long verbatim prose extracts are reproduced.

## Pinned prime-predecessor master D

[Immutable introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/01-introduction.tex), `thm:main`, lines 30–43: for each fixed `k≥1` and bounded continuous real `F` on `[0,1]^k`, uniform ordinary averaging over primes `3≤p≤x` gives the PD(1) expectation of `F` on the ranked normalized logarithms of prime factors of `p−1`, with multiplicity. All real counting endpoints are allowed. This theorem does not assert an error rate or a moving small-factor conditioning.

[Immutable probability section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/08-poisson-dirichlet.tex), `pd:dyad-law`: the same finite-coordinate law holds for `(x,2x]`, normalized by `π(2x)−π(x)`. Its proof fixes the size-biased draw count before the `x` limit, then sends it to infinity. `pd:unseen-mass` has limiting expectation `2^(−d)` at each fixed draw count; it is not a uniform error for `d=d(x)`.

[Immutable determinant section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/03-determinant.tex), `thm:type-II`, lines 37–58: fix positive `δ,C,D_*` and damping `q∈(0,1)`. Both factor scales exceed `x^δ`, their product is comparable to `x`; the first coefficient is the displayed prime-minus-rough proxy with Mellin frequency at most `log^C x`, and the second is rough-supported and bounded by `log^C x`. The bounded first core obeys `F(ph)=F(h)` at every prime in each fixed inert band with exponent between `.1` and `.2`. Sufficiently large fixed band count gives arbitrary requested log saving. This exact invariance is violated by general small-valuation events at the selected cutoff.

[Immutable two-sided section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/06-correlations.tex), `thm:two-sided`, lines 55–77: fixed number of distinct long prime slots, lower bounds `x^ε`, product of upper bounds at most `x^(1−ε)`. The first core is exactly the marked tuple count centered by `Σ1/ℓ`. Active small groups lie at exponents `.27–.36`, big groups at `.39–.46`; their counts are between fixed positive multiples of `loglog x`, harmonic masses lie in a fixed positive compact interval, and big groups are full intervals. The second core satisfies `G(n)=G(n_*)` and a fixed divisor/log power bound. The smooth harmonic correlation saves every prescribed fixed log power. `prop:graph-transfer` does not alone bound each comparison term. `cor:low-main-term` (lines 635–681) and `cor:constant-high` (lines 890–935) require the subsequent endpoint analysis.

[Immutable extraction section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/07-extraction.tex), `thm:interior`, lines 22–30: every fixed nonnegative smooth compact cutoff and every stated interior tuple statistic have centered prime average `o(x/log x)`. Lines 660–702 fix the arrays before `x→∞`, then remove their number and sieve depth in the specified order. No smooth-divisor discrepancy sum is stated.

## Pinned consecutive-integer master J

[Immutable introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/build/sections/introduction.tex), `thm:main`: every fixed `a,b∈(0,1)` has ordinary natural-density joint smoothness law `ρ(1/a)ρ(1/b)` at moving thresholds `n^a,n^b`, through every real endpoint. `cor:comparison` gives half-density ordering.

[Immutable labels section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/build/sections/labels.tex), `prop:mixed`: for fixed integer `J≥2`, bins `(x^(k/J),x^((k+1)/J)]`, and any two independently chosen fixed unit phase vectors, the mixed centered bin-character average tends to zero through integer scales. `lem:labels-marginal` includes fixed progression classes, including nonunits. `lem:labels-short` uses an iterated `x→∞` then `B→∞` limit with its other parameters fixed. Its finite tensor interpolation coefficients depend on fixed `J`; no growing-grid assertion is stated.

[Immutable distribution section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/build/sections/distribution.tex), `eq:distribution-characters` and the finite Fourier inversion immediately following it, lines 12–46, **explicitly factor every pair of fixed functions of the entire two bin-count vectors**. Counts lie in `{0,…,J}`, so reduction modulo `J+1` is injective. Full joint ranked PD follows by fixed-grid approximation and then refinement. I07 §9 already records this deduction.

The relevant companion final statements were also read: S's [introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/sections/00-introduction.tex), `thm:smooth`, gives `x^(1−o(1))` smooth predecessors in `(2x,5x]` for each fixed positive smoothness exponent, explicitly without shrinking-exponent uniformity. `thm:totient` gives infinitely many fibers exceeding `n^(1−ε)` for every fixed `ε>0`. E's [main source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/main.tex), `thm:main`, asserts infinitude of squarefree even-Omega prime predecessors. R008 is already much stronger at that fixed arithmetic mode.

## Authenticated external input G — the exact usable corollary

Gorodetsky, [arXiv:2608.14190v1, §2, Corollary 2.2](https://arxiv.org/html/2608.14190v1#S2), cross-read on [PDF page 4](https://arxiv.org/pdf/2608.14190v1). For *any* random integer `B∈[1,Z]`, `2≤y≤Z`, fixed nonzero shift `a`, and fixed `θ∈(0,1), ε>0`, the model's independent coordinates are zero at primes dividing `a`; otherwise they have the shifted-prime distribution (Q). With `u=log Z/log y`, the bound is

\[
 d_{TV}(\mathcal L((v_q(B))_{q\le y}),Q_{y,a})
 \ll_{a,\theta,\varepsilon}
 u^{-\theta u(1-\varepsilon)}+Z^{-\theta(1-\varepsilon)}
 +\sum_{\substack{d\le Z^\theta\\P^+(d)\le y\\(d,a)=1}}
       (2^{\omega(d)}+\log y)
       |\Pr(d\mid B)-1/\varphi(d)|
 +\sum_{\substack{d\le Z^\theta\\P^+(d)\le y\\(d,a)>1}}
       (2^{\omega(d)}+\log y)\Pr(d\mid B).
\]

I282 uses `a=−1`, so the last sum is empty. The corollary does not assume `B` uniformly samples shifted primes; that specialization requires paying its actual discrepancy sum. PDF p.5 explicitly uses Cauchy and Brun–Titchmarsh to handle the divisor weight. The theorem itself is not an independence statement about an added arbitrary macroscopic mark.

## Other inspected external statement boundaries

Ford, [arXiv:2408.03803v4, §1.2, Theorem 1](https://arxiv.org/html/2408.03803v4): a fixed nonzero shift and smooth-modulus level hypothesis `Z(γ)` give TV error `exp(−αu log u)+log^(−A)x` for any fixed `0<α<γ,A>0`; `Z(1/2)` follows from classical BV with no smoothness restriction needed. This authenticates the existing small-vector marginal and the classical all-modulus range used in P, not independence of the small vector from ranked factors.

Bharadwaj–Rodgers, [arXiv:2402.11884v4, Theorem 7 and Lemma 8](https://arxiv.org/html/2402.11884v4): the nonnegative sequence must satisfy their index, averaged divisibility distribution, multiplicative local density bounds and congruence upper bounds. Full PD needs distribution level one. At positive level `σ`, Lemma 8 identifies factorial intensities only for compact supports with total selected log mass below `σ`. A weighted prime sequence does not inherit the distribution hypothesis merely by boundedness of its weight.

Tao–Teräväinen, [arXiv:2512.01739v2, Theorem 1.8](https://arxiv.org/html/2512.01739v2): one logarithmic-density-one set of ordinary averaging endpoints has joint smoothness error `O(log^(−c)x)` uniformly for `u,v≥1`. The exceptional endpoints remain; the meaningful relative asymptotic requires the product main term to dominate that absolute error. It is not an all-scale arbitrary-small-vector marked theorem.

For the classical upper-bound input in P, Gorodetsky PDF p.5 explicitly uses Brun–Titchmarsh in its divisor-weight passage; Gorodetsky–Grimmelt [v2, §4.1, equation (4.16)](https://arxiv.org/html/2307.13585v2#S4.SS1) also spells out the prime progression upper bound with a fixed power margin. I282 uses the standard form `π(Z;q,b)≤2Z/[φ(q)log(Z/q)]` for `q<Z` and `(b,q)=1`, so `q≤Z^(1/2−δ)` gives the claimed constant-multiple `N/φ(q)` envelope. No stronger uniformity is invoked.
