# Excluded full-scope rediscovery: Karp–Zhang Conjecture 3.8

Status: **PUBLIC DUPLICATE, zero credit, no nomination.** The primary source is
Dmitrii Karp and Yi Zhang, arXiv:2305.09029v3, printed p8 Conjecture 3.8,
with Definition 1.1 p2 and the coefficient convention p1. Current arXiv API
still returns v3 (updated 2023-12-09). A cached public registry problem page
and actual proof bodies prove the identical universal endpoint. The cached
settlement predates this lane; its exact original publication/commit timestamp
was not recovered. No current registry head is claimed.

## Literal scope

For every nonnegative nontrivial real sequence (f_n) with interval support and
f_n²≥f_(n-1)f_(n+1) for n≥1, independent of the parameters, put
A_0(u)=0 and A_n(u)=(u)_(3n)/(3n-1)! for n≥1.
For every m≥0 and µ,α,β≥0 the assertion is

    Σ_(k=0)^m f_k f_(m-k) [A_k(µ+α)A_(m-k)(µ+β)
                           −A_k(µ)A_(m-k)(µ+α+β)] ≥0.

These are finite formal coefficients, with no convergence assumption.
Internal zeros cannot be admitted without proof. Zero shifts give equality;
at µ=0, A_n(0)=0 and the assertion is immediate.

## Route 1: direct coefficient/sign variation

Source Lemma 3.1 propagates nonpositivity of the paired Pochhammer difference
backwards in the length index. Applying it three times gives at most one
negative-to-positive change for the reflected triple-step kernel B_k,
1≤k≤floor(m/2), counting the middle once. Its factorial denominator is
positive and does not affect signs. The central term is positive for positive
parameters by strict log-concavity of each rising factorial.

The strongest COMPLETE source adaptation is Theorem 3.6's multiplier-two
proof: sign variation plus a positive total kernel, then Lemma 2.2 weighting.
The sign-variation part extends to multiplier three. Its two-branch binomial
factorization (14) does not: the triple filter has complex conjugate branches.
Checking unit shifts in finitely many degrees is insufficient. The recorded
unit-shift polynomials for m=2,…,12 have nonnegative coefficients, but are
diagnostics only. The exact missing bridge in this route is nonnegativity of
the full unweighted kernel for every m and every real parameter triple.

## Route 2: beta lifting and a full all-degree bridge

The following argument closes that bridge, but is uncredited because an
already-public proof uses the same beta-lifting idea and a different
all-degree homogeneous-polynomial certificate.

For m≥2 let N=3m−2 and define

    P_N(z)=Σ_(0≤j≤N, j≡2 mod3) binom(N,j) z^j(1−z)^(N−j),
    Q_N(z)=z(1−z)P_N(z).

Because N≡1 mod3, Q_N is symmetric under z↦1−z. We prove it is increasing
on [0,1/2]. All coefficients in the displayed sum are positive.

### A complete monotonicity certificate for Q_N

For N<40 the only possibilities are 4,7,10,…,37. Set q=4z(1−z).
Q_N=W_N(q) is a polynomial. check.py constructs W_N exactly, proves the
polynomial substitution identity, and expresses W_N'(q)/q² in the Bernstein
basis on [0,1]. All coefficients are nonnegative after bisecting the interval
for N=10,13 only. exact-certificates.json supplies every rational coefficient;
the Bernstein polynomials binom(d,i)t^i(1−t)^(d−i) are nonnegative. This is
a finite exhaustive proof for this bounded residual list, not evidence for
an unbounded claim. For example W_7'(q)/q²=63(1−q)/64.

Here is an analytic proof covering EVERY integer N≥40 with N≡1 mod3.
Write w=z(1−z), v=1−2z, ω=exp(2πi/3), λ=1−z+ωz. Root filtering gives

    3P_N(z)=1+2 Re(ω λ^N),       |λ|²=1−3w.

Region I, 0≤z≤3/(N+2): differentiating each term of Q_N gives a positive
factor times (j+1)−(N+2)z. Since j≥2, every derivative is nonnegative.

Region II, 3/(N+2)≤z≤1/4: v≥1/2 and t=Nw≥5/2. Indeed
3N(N−1)/(N+2)²≥5/2 for N≥40, equivalently N²−26N−20≥0.
Differentiation of the root filter bounds the error relative to the main
term v in 3Q_N' by

    2|λ|^(N−1)(|λ|+sqrt(3)Nw/v)
      ≤2 exp(−7t/5)(1+7t/2)<1.

We used (N−1)/N≥39/40, sqrt(3)<7/4 and |λ|≤1. The last bound decreases
for t≥5/2 and at 5/2 is (39/2)exp(−7/2)<1. The latter follows from
exp(7/2)>Σ_(k=0)^6 (7/2)^k/k!>39/2. Thus Q_N'>0.

Region III, 1/4≤z≤1/2: 0≤v≤1/2. Put R(v)=Re(1+i sqrt(3)v)^N.
Since N=3m−2, the root filter becomes

    Q_N=(1−v²)[1+(−1)^m 2^(1−N)R(v)]/12.

For v>0, telescoping the difference of conjugate powers gives

    |R|≤(1+3v²)^(N/2),
    |R'|≤3N(N−1)v(1+3v²)^((N−2)/2).

Consequently, with y=(1+3v²)/4≤7/16,

    |(1−v²)R'−2vR|/(2^N v)
      ≤[N(N−1)(1−y)+2y] y^((N−2)/2)
      ≤(N²+2)(2/3)^(N−2)<1.

The last inequality holds at N=40 by exact rational arithmetic and propagates
because the ratio of consecutive bounds is
(2/3)((N+1)²+2)/(N²+2)<1 for N≥40.
Thus dQ_N/dv<0 for v>0, with the centre supplied by continuity. The three
regions cover [0,1/2]. No unproved all-degree positivity bridge remains.

### Beta balancing, all real parameters

For s,t>0, S=s+t, beta moments give the exact identity

    Σ_(k=1)^(m−1) A_k(s)A_(m−k)(t)
      = Γ(S+3m)/((3m−2)! Γ(S)) E[Q_N(Z)],   Z~Beta(s,t).

For verification, the summand j=3k−1 in Q_N has exponents j+1 and N−j+1;
its beta moment has numerator Γ(s+3k)Γ(t+3(m−k)), with common denominator
Γ(S+3m). This checks both factorials and the total gamma shift.

At fixed S, parameterize s=S/2−d,t=S/2+d, 0≤d<S/2. Fold the beta law
onto z∈(0,1/2). Its density, up to normalization, is

    [z(1−z)]^(S/2−1) cosh(d log((1−z)/z)).

For d2>d1≥0 the ratio cosh(d2 L)/cosh(d1 L) increases in L≥0 because
d2 tanh(d2 L)≥d1 tanh(d1 L). Since L decreases in z, the normalized density
ratio decreases in z. A single-crossing argument then shows that expectation
of any increasing function of folded z decreases with d: subtract its value
at the crossing, multiply by the signed density difference, and integrate.
This applies to Q_N. Therefore the unweighted convolution increases when
the parameter pair is balanced. The pairs (µ+α,µ+β) and (µ,µ+α+β) have
the same sum and imbalances |α−β|/2≤(α+β)/2. This proves the full kernel
sum is nonnegative for all positive parameters.

### Weighting closes the literal endpoint

Let B_k be the reflected kernel in Route 1. We now know ΣB_k≥0 and that
B_k has at most one negative-to-positive sign change. Log-concavity with
interval support makes f_k f_(m−k) nondecreasing for k≤m/2. Subtracting
the weight at the sign transition proves Σf_k f_(m−k)B_k≥0. If products
vanish, their positive support is a central interval and the same argument
applies, with zero products omitted. This is exactly source Lemma 2.2;
there is no strict-positivity assumption on the sequence. Degrees m=0,1
vanish. Zero shifts vanish, and µ=0 was handled above. Thus all quantifiers
of Conjecture 3.8 close in ordinary mathematics.

## Why this is not a discovery

The frozen public Problems/karp-zhang-2023-conjecture-3-8.md explicitly
proves Result.result : Result.claim with this exact sequence predicate,
every degree, and all nonnegative real parameters. Its actual Beta.lean
and Result.lean bodies are frozen for source comparison, not edited or run.
The public proof uses homogeneous trisection positivity, beta lifting and
the same sign-variation/Abel weighting. Our Q_N is the same homogeneous
slice up to a positive constant and index change. A different certificate
for that slice does not produce a new source resolution or substantive
new family. No PROOF.md nomination, Lean, manuscript or count is produced.

The fifth-family pivot, Kalmykov–Karp Conjecture 3 (1611.06724v1 p8), is
also excluded: Sokal 2204.01045v1 pp3–4 Theorem 5 and its complete proof
refute its literal strict-parameter scope by compact-uniform limits and
Ki–Kim. This is an actual proof body, not an abstract-based open-status claim.
