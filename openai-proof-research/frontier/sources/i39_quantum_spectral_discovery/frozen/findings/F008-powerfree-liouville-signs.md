# F008 — Binary cancellation on polynomial power-free sets

Status: **proved cross-family corollary; independent review accepted after minor clarity corrections**. Assumes upstream families 007 and 020. The periodic-approximation method is classical; literature priority is unestablished.

### Exact input contracts

- **E:** [Ordinary two-point correlations, `cor:affine`, `eq:unp`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/introduction.tex): binary ordinary cancellation along fixed nonproportional positive-slope, nonnegative-intercept affine forms when one original bounded multiplicative factor is uniformly nonpretentious. Liouville satisfies the condition. No growing-coefficient uniformity is supplied.
- **S:** [Squarefree quartics and power-free polynomial values, `cor:separable-products`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/build/sections/01-introduction.tex): for fixed k≥2 and nonzero integer polynomials F_i separable over Q, every nonconstant irreducible factor of degree at most k+2, simultaneous k-power-freeness has the positive Euler-product density below if |Ω_p|<p^k at every prime. Here Ω_p is the union of the individual F_i root sets modulo p^k; shared factors are allowed.

### Statement

Fix \(k\ge2\) and \(F_1,\ldots,F_r\) satisfying S. Declare zero not k-power-free, so every polynomial zero contributes weight zero, and put
\[
w(n)=\prod_i1_{\{F_i(n)\text{ is }k\text{-power-free}\}},
\qquad c=\prod_p(1-|\Omega_p|/p^k)>0.
\]
Let \(L_j(n)=a_jn+b_j\), with fixed integers \(a_j\ge1,b_j\ge0\), \(a_1b_2-a_2b_1\ne0\). If \(f_1,f_2\) are multiplicative and bounded in modulus by one, and an original factor satisfies
\[
\inf_{|t|\le X}\sum_{p\le X}
\frac{1-\Re(f_j(p)\overline{\chi(p)p^{it}})}p\to\infty
\quad\text{for every fixed Dirichlet character }\chi,
\]
then
\[
\sum_{n\le N}w(n)f_1(L_1(n))f_2(L_2(n))=o(N). \tag{4}
\]
For every sign pair \(\epsilon_1,\epsilon_2\in\{-1,1\}\),
\[
\#\{n\le N:w(n)=1,\lambda(L_j(n))=\epsilon_j,\ j=1,2\}
=\tfrac c4N+o(N). \tag{5}
\]
No coprimality between polynomials and forms is required. Family sizes, coefficients, \(k\), and forms are fixed.

### Complete proof and loss of rate

For fixed \(Y\), impose just the conditions at primes \(p\le Y\), giving a periodic majorant \(w_Y\) of period \(Q_Y=\prod_{p\le Y}p^k\) and mean \(c_Y=\prod_{p\le Y}(1-|\Omega_p|/p^k)\). From S and \(w_Y\ge w\),
\[
\lim_{N\to\infty}N^{-1}\sum_{n\le N}|w_Y(n)-w(n)|
=c_Y-c,\qquad c_Y\downarrow c. \tag{6}
\]
For \(a\in\{1,\ldots,Q_Y\}\), write \(n=Q_Ym+a\). Transformed forms have determinant \(Q_Y(a_1b_2-a_2b_1)\ne0\), positive slopes, and nonnegative intercepts. E applies to the same original functions at the integer cutoff M_a=⌊(N−a)/Q_Y⌋. Since M_a/N→1/Q_Y for fixed Y, its o(M_a) error is o(N). The initial \(m=0\) term costs at most one. Summing over finitely many allowed residues proves cancellation with \(w_Y\). Boundedness and (6) give
\[
\limsup_{N\to\infty}N^{-1}
\left|\sum_{n\le N}w(n)f_1(L_1(n))f_2(L_2(n))\right|\le c_Y-c.
\]
Send \(Y\to\infty\), proving (4). With a factor identically one the argument gives one-point Liouville cancellation, using any auxiliary nonproportional form. Expand the sign indicator as
\[
\tfrac14(1+\epsilon_1\lambda(L_1(n)))(1+\epsilon_2\lambda(L_2(n))).
\]
Its constant term has mean \(c\), and the other three terms vanish, proving (5).

**Uniformity:** first \(N\to\infty\) with \(Y\) fixed, then \(Y\to\infty\). Taking \(Y=Y(N)\) requires uniform control of E's constants for coefficients involving \(Q_Y\), plus a quantitative (6). Neither is asserted. Even for Liouville only the conclusion \(o(N)\) is proved; a logarithmic saving is not established.

For example, for every sign pair,
\[
\#\{n\le N:n^4+1\text{ squarefree},
\lambda(n)=\epsilon_1,\lambda(n+1)=\epsilon_2\}
\sim\tfrac N4\prod_{p\equiv1\pmod8}(1-4/p^2).
\]
Indeed \(t^4+1=\Phi_8(t)\) is irreducible, has no roots modulo 4, and has four simple roots modulo an odd prime exactly when \(p\equiv1\pmod8\). Hensel lifting gives the displayed factors. The squarefree density alone appears upstream; the sign-conditioned result is the deduction.

### Novelty status

Periodic approximation is standard. Desjardins's [squarefree–Liouville sieve](https://arxiv.org/html/1610.07440), Theorem 2.9 and Corollaries 2.10/2.12, is a direct precedent, including homogeneous two-variable applications. The new-to-project result is the ordinary **one-variable** combination of assumed binary Elliott and the assumed quartic/power-free range. Do not claim a new abstract sieve method. Fuller comparison with conditional one-variable squarefree–Chowla results remains necessary for priority; the explicit quartic sign distribution was not located in the bounded search.

### General transfer principle

The proof uses the standard principle that a bounded sequence with mean
zero on every fixed arithmetic progression remains orthogonal to any
bounded weight approximable by periodic functions in average absolute
error. Indeed periodic weights reduce to finitely many progressions, and
the weighted-error difference is at most the average absolute approximation
error. Here S supplies the required approximants w_Y with error c_Y−c.
This principle is not claimed as a new theorem.

### Validation

[Independent review](../reviews/powerfree_signs-r1.md) checked both exact
source contracts, residue determinants, order of limits, sign expansion
and the cyclotomic local factors. All required corrections are incorporated.
The parent independently checked the transfer and that t⁴+1 has four
simple roots precisely at odd primes congruent to 1 modulo 8, with no
root modulo 4.

The review's optional million-integer numerical screen tested divisibility
only by prime squares with p≤10⁶. That is **a truncated local sieve, not
an exact squarefree test** for n⁴+1 throughout that range; larger square
divisors are possible. Its numbers are not used as validation of (5).
The proof is analytic and uses the accepted full density theorem. No
proof-assistant verification is claimed.
