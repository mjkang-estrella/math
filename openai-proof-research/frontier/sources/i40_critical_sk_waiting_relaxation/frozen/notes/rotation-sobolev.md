# Supporting note: the Sobolev reformulation of μ(π)=2

Status: correct after independent review and clarification; **equivalent reformulation, not a separate new finding**. Accept upstream family 017 as true.

## Exact input and novelty screen

At revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family 017,
[The irrationality exponent of pi is 2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex),
Theorem 1.1 (`thm:main`), gives: for every ε>0 and every sufficiently
large integer q, |π−p/q| ≥ q^(−2−ε) for all integers p. Its threshold
is not effective. The paper explicitly distinguishes this from bad
approximability. Its section `series.tex` already proves the complete
generalized Flint–Hills convergence criterion; that would be a duplicate,
not a new finding.

The Fourier multiplier argument below is classical for Diophantine
rotations. See Carlos Matheus's [2010 exposition](https://matheuscmss.wordpress.com/2010/03/21/the-local-linearization-problem-of-generalized-interval-exchange-maps/)
and [2014 exposition](https://matheuscmss.wordpress.com/2014/03/17/holder-regularity-of-solutions-of-the-cohomological-equation-for-interval-exchange-transformations/)
of the Roth-type cohomological equation. The infimum of the derivative loss equals μ(α)−1 for any irrational α.
Since μ(1/π)=μ(π), parts (1)–(2) are an equivalent reformulation of the
upstream result, adding no arithmetic information. This is a classical
Fourier argument, recorded for interpretation rather than novelty. Smooth solvability itself
already followed from older finite irrationality bounds for π. The proved
Zeilberger–Zudilin bound 7.103205334137… quoted upstream gave loss
6.103205334137…+δ. The improved loss is the standard translation of the
new irrationality exponent. Parts (2)–(3) are valid for every irrational
rotation and use no new upstream theorem.

## Theorem

Let T=R/Z, α=1/π, and Rα(x)=x+α. Write H^s_0(T) for the distributions
with zero Fourier coefficient at 0 and finite norm
Σ_(k≠0) (1+k²)^s |f̂(k)|². Let L u=u∘Rα−u.

1. For every real s and every δ>0, L has a unique zero-mean inverse
   mapping H^(s+1+δ)_0 to H^s_0, with
   ||L^(−1)f||_(H^s) ≤ Cδ ||f||_(H^(s+1+δ)). The constant is independent of s; no effective
   value is supplied by the upstream proof.
2. For every real s and r<1, there exists a real-valued distribution
   f in H^(s+r)_0 for which Lu=f has no solution u in H^s, even allowing
   an arbitrary constant. In particular, no uniform estimate with a
   loss of r derivatives is possible.
3. An estimate H^(s+1)_0 → H^s_0 holds (for any, equivalently all s)
   if and only if α is badly approximable, equivalently π is badly
   approximable. The upstream theorem does not settle this endpoint.

Thus the infimum admissible uniform Sobolev loss is exactly one derivative;
attainment of the infimum is not asserted.

## Proof

For k≠0 the Fourier multiplier is
d_k=exp(2πikα)−1=exp(2ik)−1, so |d_k|=2|sin k|. The resulting
small-divisor bound also appears inside the upstream Flint–Hills proof. Put ||t||=dist(t,Z). For every real t,
4||t|| ≤ |exp(2πit)−1| ≤ 2π||t||.

For k≥2 let m be the nearest integer to k/π.
Then 1≤m≤k. For sufficiently large k, m exceeds the upstream threshold. Upstream gives
||k/π||=|k−πm|/π ≥ m^(−1−δ)/π ≥ cδ k^(−1−δ).
Absorbing the finitely many remaining positive k into the constant is
legitimate because π is irrational. Negative k follow by symmetry.
Consequently |d_k|≥c′δ |k|^(−1−δ). Define û(0)=0 and
û(k)=f̂(k)/d_k. Termwise comparison of the weighted squares proves (1),
with convergence in H^s and hence distributional satisfaction of Lu=f.
Every distributional solution has these nonzero Fourier coefficients,
which proves uniqueness modulo constants.

Dirichlet's approximation theorem supplies infinitely many k>0 with
||kα||<1/k. Along this sequence |d_k|<2π/k. Testing a single Fourier
mode already shows an inverse estimate with loss r<1 would require
unbounded constants proportional to k^(1−r).

For the stronger fixed-forcing assertion in (2), select a strictly increasing subsequence k_j
of these denominators so large that k_j^(1−r)≥j². Set
f̂(k_j)=(1+k_j²)^(−(s+r)/2)/j, f̂(−k_j)=f̂(k_j), and all other
coefficients zero. Its H^(s+r) norm squared is 2Σ_j j^(−2)<∞.
For any solution, its contribution at k_j to the H^s norm squared is

    (1+k_j²)^(−r) / (j² |d_(k_j)|²)
      ≥ c_r k_j^(2−2r) / j² ≥ c_r j².

Here c_r=2^(−max(r,0))/(4π²) suffices. It therefore cannot belong to H^s. The conjugate-symmetric coefficients
make f real as a distribution. Every Fourier coefficient grows at most
polynomially, so this indeed defines a distribution for arbitrary s,r.

The diagonal multiplier bound with loss exactly one is equivalent to
inf_(k≥1) k|d_k|>0, and hence to inf_(k≥1) k||kα||>0, the usual bad
approximability criterion. Inverting a nonzero irrational number
preserves bad approximability: for rational p/q close to α, p and q
are comparable and
|1/α−q/p|=|α−p/q| q/(|αp|).
Rational approximants not in a fixed neighborhood have a positive
distance and are harmless. Apply the same argument in reverse to obtain
the equivalence with π. This proves (3).

## Why the endpoint is a real gap

An irrational with continued-fraction partial quotients a_n=n+1 has
irrationality exponent two but unbounded partial quotients: denominators
grow at least geometrically, so log(a_(n+1))/log(q_n)→0, while
q_n||q_n α||≤1/a_(n+1)→0. Thus μ=2 alone cannot imply an attained
one-derivative estimate. This is a logical boundary of the input, not a
counterexample concerning π.

## Validation

[Independent review](../reviews/rotation-r1.md) confirmed all mathematical
claims and required the equivalence/novelty clarification now included.
The reciprocal step, fixed-forcing construction and endpoint were checked
line by line. The estimate at loss one is also equivalent to solvability
for all inputs at that loss by the closed graph theorem for the diagonal
multiplier. Finite normalization tests are in
`../experiments/rotation_quadrature.py`; they do not prove asymptotics.

This note is supporting material for F001, not an additional discovery.
