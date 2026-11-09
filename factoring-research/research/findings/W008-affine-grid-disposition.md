# W008 — affine-grid audit disposition and source corrections

2026-10-08. Parent intake of completed Opus task B.
[Original note](W008-random-affine-grid.md) and
[unaltered review](W008-affine-grid-review.md) are preserved. Parent verified
all four delivery hashes and read the source text around BY Theorem 5.
Verified complete factoring improvement: **NONE**.

## Accepted control and new schedule

Accept the five-residue generator, pairwise independence for K<=p, uniform
marginals for every K, and the no-global-zero/full-gcd extraction argument.
The original parent note explicitly left the K>p schedule open; the review's
description of an asserted monotonicity extension in that note is inaccurate.
Its newly supplied covering proof nevertheless fills the missing step:
for K>=p, a_1!=0 mod p guarantees a p-zero by varying the first coordinate
over [0,p). The event has probability 1-1/p. Subtract the global-zero bound.

Together with the K<=p second-moment law and the N-only cap, every stage
after the useful threshold has success >3/8. For example the common lower
bound 130/261-16/131=12854/34191>3/8 is valid when p,q>=131.
Four trials per doubling stage suffice for the quadratic cost. The result
is expected sqrt(p)*poly(log N) work, with N as the only problem input.

Accept the composite-ring monic block evaluator, including exact arbitrary
boxes. For dyadic boxes distribute baby exponents across coordinates so
their total is half the total exponent. Then D+P is at most
(sqrt(2)+1/sqrt(2))*sqrt(box volume); at the initial K^4 box it is exactly
2K^2. Each descent halves volume, so the sum of record costs is geometric.
The original common per-coordinate split already had the same K^2 exponent;
the review improves constants, not asymptotics.

## Corrections to the review's recurrence/source claims

The symbolic shift overlap is accepted over independent symbolic slopes.
Specialization can increase gcd degree; a generic degree bound cannot be
imposed on all finite-field slopes. At K^4>p there must be repeated grid
roots modulo p, but repetition alone does not prove strict extra cancellation
for every chosen shift. Only the non-strict specialization inequality is used.

The coordinate-slicing sequence has ratio g(n) of degree K^3. The minimal
nonzero coefficient in any symbolic polynomial recurrence for its products
must be divisible by the next g; the review's all-order divisibility argument
is accepted for that sequence. It is different from the parent's later
[shift-of-G boundary lemma](W008-grid-boundary-recurrence.md), which remains
provisional and was not in task B's frozen prompt.

**The cited fast recurrence theorem does not give a K^2 slicing algorithm.**
Bostan--Yurkevich, [Theorem 5 and section 3.4](https://arxiv.org/abs/2012.08656),
explicitly require the sequence length N_term>d. Here N_term=K and d=K^3,
so the requirement fails. The source's optimal baby step sqrt(N_term/d)
would be below one. Moreover, constructing a dense g already writes K^3
coefficients. The arithmetic expression sqrt(K*K^3)=K^2 cannot be quoted
as an applicable algorithmic bound while omitting these hypotheses and
coefficient acquisition. The separate exact block evaluator establishes
the K^2 control. No holonomic theorem establishes a faster one here.

The report's C4 is not an accepted closure of all p-specific identities.
A known non-global collision would itself reveal a factor, but that is not
a proof that a compressed identity cannot be discovered more cheaply.
Likewise Z/NZ certainly has finite additive subgroups; the characteristic-zero
absence of nontrivial finite additive subgroups must not be transferred to it.
An explicitly supplied generator of a proper nonzero additive subgroup of
Z/NZ has a proper gcd with N. None of these statements excludes a new
algorithm for acquiring the needed information.

The proposed nontranslation block-fiber computation and its recursive cost
remain unsupplied, not an accepted saving. An abstract-only Lipton reference
is not a verified use of its theorem. No new experiment, solver or Lean
change is warranted by this review. The parent continues with an actual
quotient-product update calculation and an independent dynamics factorization.
