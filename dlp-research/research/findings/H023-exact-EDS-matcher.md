# H023 exact EDS match refinement without a small-fiber assumption

2026-10-08. Native Sol proposer and independent native Astra reviewer
COMPLETED. Root independently checked normalization, point-key implication,
counts and fixed-length expectation. Brief in H023-coordinate-walk-and-EDS-keys.
This is a paper correctness/cost primitive, not Lean formalization or an
ECDLP improvement. The H022 generation schedules still lose their arithmetic
comparisons. No numerical experiment or general infrastructure follows.

## Spacing-independent exact key

Assume p>3, prime point order q>3, q not dividing p-1, common normalization
h(P)=phi(P)/alpha with alpha=phi(G)!=0, and nonzero subgroup spacing T.
Write P=mT and beta=phi(T). From the consistent normalized convention
u_m=beta^(m²-1)*psi_m(T), the exponent difference in
u_(m-1)*u_(m+1)/u_m² is2. The division-polynomial x identity therefore gives

    D_T/C = beta²*(x(T)-x(P)),
    C=h(P)², D_T=h(P-T)*h(P+T),
    N_T=x(T)*C-beta^(-2)*D_T=C*x(P),

for P!=O. The common alpha cancels from D_T/C. Source conventions are
[Liao–Zhang, Eq3/5/6](https://tches.iacr.org/index.php/TCHES/article/download/13106/12653),
already independently read in the retained publisher text. No arbitrary
rescaling-invariance assumption is used.

For nonzero centers, (canonical±h(P),N_T) is an exact negation-class key.
Equal keys have equal nonzero C and N, hence equal x; conversely opposite
points have opposite h and the same C*x. Raw h retained with the record
resolves which sign occurs. (h,N) without canonicalization identifies the full
point. This compares G-neighbor keys against DG-neighbor keys correctly.

At P=±T one neighbor is zero and D_T=0, so the formula is valid. Detect
h(P)=0 first and handle O by a sentinel/direct target recovery; affine x(O)
is undefined. Require the normalized-EDS zero locus and order hypotheses.

## Paid matching options

With the two neighbors available, C costs1S, D_T costs1M, and the two
constant multiplications in N cost2M: total3M+S plus additions. Fixed
beta^-2, neighbor generation/access, two-field records and comparison/index
costs remain paid. A prefix implementation must initialize its leading
neighbor, retain the previous boundary and produce terminal lookahead;
delaying key construction until neighbors exist is sound, not free.

Alternatively, refine a signed raw-center match via

    (x(T1)-x(T2))*C = beta1^(-2)*D1-beta2^(-2)*D2.

Forming both products anew costs at most5M+S; cached products may help.
This rejects false raw matches without scalar multiplication. One can instead
build secondary exact-N dictionaries within raw-center buckets, refining each
known record once and each target once when its raw bucket is occupied.
Ordered dictionaries give logarithmic comparison counts; hashes require
their own cost assumptions and full-key equality checks. Duplicate keys need
retained relevant indices or a justified deduplication rule. Final recovered
scalar verification remains a charged group computation.

Thus a small phi-fiber theorem is NOT a prerequisite for a correct bounded
lookup implementation. The larger keys and additional arithmetic must still
be in the complete solver ledger. An SCM per false hit is a choice made by
the literal H022 verifier, not an unavoidable lower bound on EDS matching.

## Exact fixed-length raw-match expectation

For nonzero t let c(t)=#{P!=O:h(P)=t}. Oddness gives c(t)=c(-t).
Take a fixed nonzero known list independent of uniform full-group Q, and J
fixed or Q-independent shifts. Each shifted target has a uniform marginal.
Linearity of expectation gives

    E[false signed matched records]
      = (2J/q)*sum_i(c(h(P_i))-1).

The true signed point-record contribution is2IJ/q. Dependencies between
targets do not affect these fixed-length expressions. Conditioning Q to be
nonzero changes the exact formula. Do not replace J by an expected adaptive
stopping time. For a fixed cap, the full-cap expectation is an upper bound
on stopped nonnegative record scans. Duplicate records are not distinct
recovered scalars; count each object according to the implemented operation.

No random-function behavior, small-fiber bound, new speed result or exponent
improvement is asserted. Future candidate admission requires exact refinement
and its memory/arithmetic, or justified raw-bucket costs. Current main-goal
verified improvement remains NONE.
