# F001 — Sharp regularity for O(1/N) quadrature along n/π

Status: **proved downstream corollary; independently reviewed and accepted**.
Assumes pinned upstream family 017 as requested. Literature priority is not established.

## Input

[Family 017, `series:generalized`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/series.tex)
states that Σ_(k≥1) k^(−a)|sin k|^(−b) converges exactly when
a>max(1,b), for a,b>0. We use a=2s,b=2.
The upstream generalized series itself is NOT our new result.

## Theorem

For s>1/2 equip H^s(T), T=R/Z, with norm squared
Σ_(k∈Z)(1+k²)^s |f̂(k)|². All such functions have a canonical continuous
representative. Set α=1/π and

    Q_(N,x)(f) = (1/N) Σ_(j=0)^(N−1) f(x+jα),  N≥1.

There exists C_s<∞ with

    sup_x |Q_(N,x)(f) − ∫_T f| ≤ (C_s/N) ||f||_(H^s)

for every N and every f∈H^s if and only if s>1.
In fact, if 1/2<s≤1 and any x is fixed, some real f∈H^s satisfies
sup_N N|Q_(N,x)(f)−∫f|=∞.

This is a sharp regularity threshold for this explicit deterministic
integration rule. The constant is existential; no effective value is
claimed from the upstream theorem.

## Proof

Let d_k=exp(2πikα)−1=exp(2ik)−1; thus |d_k|=2|sin k|.
Set S_s=Σ_(k≠0)(1+k²)^(−s)/|d_k|². The upstream series theorem gives
S_s<∞ exactly when s>1 (for the range s>1/2 under discussion).

For zero-mean f and s>1 the series

    u(x)=Σ_(k≠0) [f̂(k)/d_k] exp(2πikx)

converges absolutely and uniformly, since Cauchy–Schwarz bounds its
coefficient ℓ¹ norm by sqrt(S_s)||f||_(H^s). It therefore defines a
continuous u with u(x+α)−u(x)=f(x), first by Fourier coefficients and
then by equality of continuous functions. Telescoping gives

    Σ_(j=0)^(N−1) f(x+jα) = u(x+Nα)−u(x),

and hence the asserted bound with C_s=2sqrt(S_s). Subtract the mean
for general f; the zero-mean projection does not increase the norm.

For necessity fix x and define the bounded linear functional
A_N(f)=Σ_(j=0)^(N−1) f(x+jα)−N∫f on H^s. Evaluation is bounded
because s>1/2. Its squared norm is exactly

    ||A_N||² = Σ_(k≠0) (1+k²)^(−s)
                 |exp(2πikNα)−1|² / |d_k|².

This follows from the Hilbert-space dual norm of Fourier coefficients;
the factors exp(2πikx) have modulus one. For each fixed N the geometric
sum has modulus at most N, so the dual norm series is finite whenever
s>1/2, even when S_s diverges. For every finite set F of nonzero
frequencies, the Cesàro mean over 1≤N≤M of the corresponding finite
sum tends to 2Σ_(k∈F)(1+k²)^(−s)/|d_k|², since kα is irrational and
the Cesàro mean of exp(2πikNα) is zero. If ||A_N|| were uniformly at
most C, each finite sum Σ_(k∈F)(1+k²)^(−s)/|d_k|² would be ≤C²/2,
forcing S_s<∞. Thus for s≤1
the norms are unbounded. The uniform boundedness principle on H^s then
provides a single f with sup_N |A_N(f)|=∞. Taking real and imaginary
parts shows at least one real f has this property. This establishes both
necessity and the fixed-function failure.

## Novelty and checks

This is a classical Fourier/coboundary transference mechanism with newly
available sharp arithmetic control of an explicit angle; priority in the literature
has not been established. It is not a claim that O(1/N) quadrature was
previously impossible: older finite irrationality estimates give such
rates at much higher smoothness. The new consequence is the exact s>1
threshold, including endpoint failure.

The result does not imply an O(1/N) bound uniformly over arbitrary
continuous functions, bounded variation functions, changing angles, or
an N-dependent class without the stated Sobolev norm constraint.

The endpoint obstruction already holds for every irrational angle: along
convergent denominators q, |exp(2πiqα)−1|<2π/q, and the terms defining
S_s fail to tend to zero when s≤1. Only the positive bound at the specific
angle arbitrarily close to s=1 needs the new upstream input.

Primary literature context: Leonardo Colzani, [Speed of convergence of Weyl
sums over Kronecker sequences](https://doi.org/10.1007/s00605-022-01785-z),
Remark 15, treats classical norm-uniform bounded-remainder methods. The
review distinguishes its metric-in-angle conclusions from our fixed angle.

## Validation

- [Independent review](../reviews/quadrature-r1.md): accepted; checked the
  source, all quantifiers, dual norm, finite-frequency limiting argument,
  and fixed-real-function obstruction. All four clarity suggestions are
  incorporated here.
- Parent independently checked the geometric-series identity, positivity
  argument, and uniform boundedness step.
- `python openai-proof-research/experiments/rotation_quadrature.py` passed
  60 finite duality cases. Maximum duality error was 8.58e-13; maximum
  telescoping error was 3.38e-13. These check signs and normalization only.
- [Supporting Sobolev reformulation](../notes/rotation-sobolev.md) records
  why the related one-derivative infimum is an equivalent restatement of
  μ(π)=2, and is not counted as another finding.

No Lean or other proof-assistant verification is claimed.
