# W002 Lens A — Reviewed paired-residual reduction and hull closure

2026-10-08. **ACCEPT the scoped reduction and finite HullProbe construction;
REJECT that construction as a sub-1/5 factoring improvement.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

The coordinator consumed all 557 independent-review lines and its source notes.
All 48 frozen review inputs, 17 original input snapshots, 27 original delivery
entries, 63 review delivery entries, three supplemental copies and three fresh
source identities verified. The review's SHA-256 is
464e15cbae2a7dcf3c8297db89547b6c81528879783995288a9eb704902de1da.
The original report and submitted draft remain byte-identical at
35ae0bb4b0412f7a5a1d3a26c5e1d554b32df614e6c05437de3d355e5d90872f.
The unchanged intake is
c49cfb0725fe47cc1d4923c184bafb3ee76792b52b35ded4b4851286c161685e.
No algebraic repair or modification of the submitted program is required.

## Accepted scope

On the paid H029 remainder domain M=pq>=4096, p and q distinct, with
K=ceil(M^(1/3)), every original row has 0<=e<8K<M and both linear leaves in
[1,M-1]. The ceiling/floor bounds cover the band endpoints and maximal t.
The identity A_- A_+=4kM+e transfers paired products only modulo d|M.
Original positions and multiplicities remain authoritative.

A total, uniformly costed exact-product-or-proper-factor primitive supports
one-branch interval descent. At a full-gcd singleton e=0; recomputing its
original two leaves gives a proper factor without another factoring oracle.
Setup C and reachable-query cost P would give the conditional complete bound
N_0^(1/6) poly(log N_0)+O(log V)(C+P+poly(log N_0)). The primitive is still
missing; a failure output or known full-product value does not instantiate it.

The additional factorial search through E=8K costs M^(1/6) poly(log N_0),
including its unsuccessful branch and extraction. If it finds no factor,
every nonzero residual is a unit modulo every nontrivial d|M. A correct
original-interval zero-existence decision would then suffice, with paid binary
location and recovery. This assertion concerns residual products; it does not
constrain other intermediate quantities in a different algorithm.

HullProbe has a weaker factor-or-UNIT interface. Its clipped hull contains
all original signs, and a length-ceil(sqrt(M)) prefix necessarily contains a
multiple of the unknown smaller prime. Padding may supply a valid factor
without identifying an original row. UNIT certifies all requested residuals
are units. HullProbe neither returns their exact product nor decides whether
the requested row interval contains a zero.

Its consecutive-product construction uses ordinary monic polynomial arithmetic
over the composite ring. Sequential product/remainder trees, packed operand
widths, failed gcd branches, fresh subqueries, prime-support recovery and
restoration of original multiplicities are paid. The complete factorization
upper bound is N_0^(1/4) poly(log N_0), with peak space bounded by
soft-O((N_0^(1/6)+M^(1/4)) log N_0)+poly(log N_0).

The prescribed dense degree-Theta(M^(1/4)) polynomial is written before the
first product gcd on continuing full-hull calls. An unbounded family of
distinct balanced semiprimes with N_0=M survives both cutoffs. Consequently
this specific program has an Omega(N_0^(1/4)) write obstruction on that
family. This is not a lower bound for sparse or implicit products, different
execution orders, or factoring. No coefficient-density assumption is used.

The coordinator checked the strict rounding inequalities, unit/full-gcd
invariants, clipped-hull cap, geometric recomputation sum, and continuing-input
family before accepting these scopes. The independent review supplies the
expanded proofs and focused primary-source comparison. No novelty claim is
made for the known factorial method or conditional Lehman acceleration.

## Next research obligation

Reopening requires an actual cheaper original-interval product or decision
algorithm with totality, uniform construction, access and recovery costs. The
known zero value of the full product and a faster method for the dense hull
alone do not supply that algorithm. No experiment or Lean task is selected:
the specified realization already misses its objective symbolically.

No code, mathematical experiment, numerical sweep, Lean invocation or source
manifest change accompanied this disposition. The original and review evidence
remain preserved. Both Lens A tasks are completed with no pending runs; Lens B
and Lens C independent reviews remain separate live work.

[Submission](W002-paired-residual-products.md),
[independent review](W002-paired-residual-review.md),
[intake](W002-paired-residual-intake.md).
