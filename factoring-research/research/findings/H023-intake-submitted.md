# H023 — Parent intake and additional baseline comparison

2026-10-08. **Unreviewed**. No experiment or factoring improvement.

The proposer completed all 661 lines of
[H023-cluster-escape.md](H023-cluster-escape.md), SHA256
`c025d0e2c52ad9deb9540a8514cd170c2779e18e02cd60838b65a65b1974eeb3`.
The coordinator read the entire report. It gives a finite ordinary-base
family, polynomial recognition, an irreducibility argument using its two
outside conjugate roots, actual separation failure, a primitive-population
counterexample when H022's geometry premise is removed, and conditional
rectangle optimization. All require independent review.

The primary polynomial-selection chapter was checked by the coordinator:
translations, skewed norms and polynomial rotations are established methods.
The special-family comparison must retain its scope.
[Primary polynomial selection chapter](https://www.joppebos.com/montgomery/book_ch6.pdf).
This source supports the baseline classification, not the new calculations
below or the proposer's family-specific identities.

## Additional parent deduction to audit

Section 8.3's binomial alternative permits a fuller baseline calculation.
This is new parent mathematics supplied for review, not attributed to the
proposer. It is another conditional norm/collection relaxation, not a
factoring theorem.

Write q=m+1, k=d-2, A0=m²+M+1 and N=A0 q^k+1.
For a fixed positive integer s dividing k, put l=k/s and

    F_s(T)=T^l+A0,    L_s(T)=q^s T-1.

The proposer gave Res(F_s,L_s)=(-1)^l N. Restrict to even l and to the
permitted independent subfamily M=1 mod4. Since m is even, A0=2 mod4;
Eisenstein at 2 makes F_s irreducible for l>=2. No prime factorization of
A0 is needed. Also gcd(q,N)=1, so q^(-s) modN is a common root.
The congruence condition keeps a fixed positive fraction of allowed M;
degrees d=2 mod(2s) keep l even and allow the same degree-scale limits.

For positive primitive x,z, the exact values are

    Res(F_s,xT+z)=z^l+A0 x^l,
    Res(L_s,xT+z)=x+q^s z.

Use x<=exp(aD), z<=exp(cD), c>=a>0, total population exponent u=a+c.
The same elementary primitive edge-rectangle count as in the proposer report
gives an attained exponent u with uniform actual leading norm coefficients.
For fixed s and delta, the rational coefficient is s/delta, while the
algebraic one is max(c delta/s, 2/delta+a delta/s). Thus

    W_s=s/delta+max(c delta/s, 2/delta+a delta/s).       (I1)

Balance when u delta²>2s:

    a=(u-2s/delta²)/2,
    c=(u+2s/delta²)/2,
    W_s=(s+1)/delta+u delta/(2s).                      (I2)

Its minimum over delta is

    min W_s=sqrt(2u(s+1)/s),
    delta²=2s(s+1)/u,
    a=u s/[2(s+1)], c=u(s+2)/[2(s+1)].                (I3)

For u delta²<=2s the closure a=0 minimizes the maximum, giving
W_s=(s+2)/delta >=(s+2)sqrt(u/(2s)), whose square is larger
than I3's square by u*s/2. Thus this boundary is no better.
The opposite boundary a=c also cannot improve the interior minimum.

With the SAME hypothetical sufficient useful-yield/collection law and matrix
charge as H023, b=u/2 leads to the exact real-relaxation infimum

    u_s³=32(s+1)/(9s).                               (I4)

This equals 64/9 at s=1, 16/3 at s=2, and 40/9 at s=4, and approaches
the usual SNFS cube 32/9 as a sequence of fixed-s model optima.
Every s has a different optimal original degree scale delta; this is not
an asymptotic theorem with s growing with N, nor uniform dominance on a
fixed input. Available divisors and the actual delta must be respected.
All irreducibility restrictions and candidate coordinates are explicit.

This comparison makes a standalone special-family novelty claim based on
16/3 even less justified. It does not prove the optimal special-family
algorithm, actual smoothness, rank, character/square-root costs or proper
splitting. It introduces no new all-input selector. A reviewer should reject
any promotion of I4 to a full factoring bound.

## Handoff

Independently audit the complete proposer report and I1–I4 above. In
particular check root counts/irreducibility, actual coefficient height, exact
thresholds, finite recognition, input sparsity, degree/parity restrictions,
attained primitive counts, boundary optimization and correct comparison of
fixed-input versus globally optimized parameters. No finite run is needed.
Any accepted result should retain the geometric counterexample while
classifying the algorithmic mechanism against established special-form NFS.
