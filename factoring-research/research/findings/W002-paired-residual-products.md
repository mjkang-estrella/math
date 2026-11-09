# W002 Lens A — Paired residuals and a root-free integer-envelope search

2026-10-08. **Constructive research submission; all new deductions below are
UNACCEPTED pending independent review. Verified COMPLETE classical factoring
complexity improvement: NONE.**

The selected realization is a **factor-or-unit-certificate search using an
integer interval containing the paired linear factors**. It avoids expanding
the Theta(M^(1/3)) integer roots and does not construct H030's polynomial block
cover. It is finite and sufficient for complete factoring, but its useful
operation reduces to the known shifted-factorial method. Its supported complete
cost is N_0^(1/4) poly(log N_0), with the N_0^(1/6) preprocessing included.
Its prescribed full-interval product construction actually writes
Theta(M^(1/4)) coefficients. Close this realization as a sub-1/5 candidate.

Two narrower deductions may be useful independently: the unchanged descriptor
has 0 <= e < 8K; and, after another paid M^(1/6) small-factor stage, every
nonzero residual is a unit modulo every divisor of M. On that remaining
domain, locating a nonunit residual product is exactly locating an interval
containing a square row. This is a reduction of the missing computation, not
an algorithm for it. In particular, a fast full product equal to zero does
not locate the row needed for recovery.

## 1. Authority, evidence, and comparison scope

The frozen [W002 brief](../hypotheses/W002.md) matches SHA-256
`5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723`.
Read the project instructions, specification, research/team protocols, STATE,
W001 synthesis, corrected H029 construction/disposition, corrected H030
report/disposition, H004's accepted reduction/disposition, and H031's current
disposition. H031 is complete; stale live-review language in STATE, W001 and
H030's disposition does not override the handoff or H031's own disposition.
No task registry was polled and no prior review was duplicated.

The [input inventory](W002-residual-inputs.json) identifies 17 saved input
copies. [Source notes](W002-residual-source-notes.md) identify the retrieved
primary bytes, reading scope and limitations. All supporting files use the
assigned W002-residual-* prefix. No sibling W002 draft was read. No numerical
example, arithmetic experiment, sweep, benchmark, candidate implementation,
Lean change, shared-file edit, package, delegation, commit, publication or
scheduler was performed. Copying, retrieval and hashing are evidence handling.

Primary checks relevant to comparison:

* [Harvey, arXiv:2010.05450v1](https://arxiv.org/html/2010.05450v1), Proposition
  2.5, Remarks 3.2 and 3.4: the square-root cost of a factorial small-factor
  search, recovery without knowing the separate multipliers, and the ambition
  of a square-root speedup for Lehman's original search are already present.
  The selected envelope method below uses the factorial mechanism. Neither
  pairing nor the 1/6 aspiration is claimed as novel.
* [Hittmeir, Math. Comp. 90 (2021), Theorem 2.1](https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf)
  supplies the exact Lehman statement used by accepted H029, including
  x=ap+bq, y=|ap-bq|, k=ab. Coverage below is inherited, not rediscovered.
* [Harvey–Hittmeir, arXiv:2105.11105v1, Theorem 1.1](https://arxiv.org/html/2105.11105v1)
  gives the matched rigorous complete deterministic bound
  O(N^(1/5)(log N)^(16/5)/(log log N)^(3/5)). Our 1/4 bound is worse.

This is a focused check, not an exhaustive novelty survey or assertion about
the latest worldwide record. Deterministic power bounds, rigorous randomized
complete factoring, heuristic GNFS and smaller-factor promises remain distinct.
Even the unrealized N^(1/6) target is exponential in binary input length and
would not beat heuristic GNFS asymptotically. No changed input distribution,
smoothness law or success-probability premise is used here.

## 2. Unchanged input and row identities

Write n=bitlength(N_0). Run exactly H029 B1's paid small-factor stage through
K_0=ceil(N_0^(1/3)), strip all recovered prime multiplicities from N_0, test
primality, and handle square remainders. Its complete cost is
N_0^(1/6) poly(n), including its products, gcd descent, leaf factoring and
checks. The unresolved case is

    M=pq >= 4096,  K_0 < p < q,  K=ceil(M^(1/3)) <= K_0.

Small M is handled by the same bounded finite exception as H029. Neither p
nor q is supplied to the subsequent algorithm.

Keep the exact H029 descriptor:

    l_j=2^j, h_j=min(2^(j+1)-1,K),
    T_j=1+ceil(sqrt(M/[16(K+1)^2 l_j])),
    c(k)=ceil(sqrt(4kM)), x=c(k)+t,
    z=x^2-4kM, y=floor(sqrt(z)), e=z-y^2,
    A_-=x-y, A_+=x+y.

Rows are ordered by j, then k, then t, with 0<=t<=T_j. Retain both signs of
each original pair, including equal signs when y=0. A row index always means
this original ordering, not an ordering by the residual value. The short
descriptor includes band endpoints and row prefix counts. Its construction
cost is O(n^4), storage O(n^2), and decoding costs poly(n). There are
V=Theta(K) rows. No root table is part of the descriptor.

Accepted H029 supplies, for every row,

    1 <= A_- <= A_+ < M,

and at least one row with e=0. The paired identity is exact over the integers:

    A_- A_+ = 4kM+e.                              (1)

Thus for every d|M, products of complete pairs over an interval I satisfy

    product_(r in I) A_(r,-) A_(r,+)
        = product_(r in I) e_r   (mod d).          (2)

This is not an arbitrary-modulus identity. If an original *sign-leaf*
interval is requested, peel its at most two unpaired endpoint leaves, compute
them exactly in poly(n), and use (2) only for its complete pairs. The factorer
below needs only row intervals. It never silently discards an endpoint or
repeated pair.

## 3. Recovery and the actually sufficient product interface

First state what a hypothetical exact product routine would have to do;
this section does not assert its fast existence. On an original row interval
I and d|M, it may return either

    a verified f with 1<f<d and f|d,
    or the exact residue R(I,d)=product_(r in I) e_r mod d.

Every inverse attempted inside such a routine must have its gcd charged. A
proper nonunit gcd may return f; gcd=d is not a proper factor and must be
resolved by a specified alternative or included in the failure cost. The
selected implementation in section 5 uses no inverse and has a different,
weaker search output, explicitly defined there.

On the actual semiprime factorer, a proper divisor of M already completes
the difficult split; validate it and its complement by deterministic primality
testing. Thus no product query on a known prime d=p or q is necessary.
All unresolved composite queries have d=M. This suffices for the actual
factorer without an extension to arbitrary d, or an attempt to split a prime.

Initialize with the full interval. Charge the root query if made, then compute
g=gcd(M,R(I,M)). Coverage implies g=M. Maintain gcd(M,R(I,M))=M until a proper
factor is returned. At an internal node with original midpoint children L,U,
query L and put u=gcd(M,R(L,M)):

* 1<u<M: return u, verify the complementary factor, and finish.
* u=M: continue on L.
* u=1: continue on U. Since the left product is a unit, M divides the right
  product; this branch preserves the invariant without a modular inverse.

At most one child remains unresolved at a depth, so there are at most
1+ceil(log2 V) product calls, including the charged root. A child product can
have full gcd because different rows supply different primes; no inference
of an individual zero is made until a singleton is reached.

At the singleton recompute its **original** (j,k,t), x, y, e, A_-, A_+.
The bound e<8K<M proved in section 4 implies that gcd(M,e)=M forces e=0.
Now M divides A_-A_+ by (1). Each positive A is less than M. If
gcd(M,A_-)=1, all of M would divide A_+, impossible. If gcd(M,A_-)=M,
then M would divide A_-<M, also impossible. Consequently

    1 < gcd(M,A_-) < M.                            (3)

It equals p or q; the other sign contains the complementary prime. This
proves recovery for **any** zero row, not only the row singled out in Lehman's
existence proof. A zero row with y=0 would contradict these inequalities and
squarefreeness. For a prime assigned d, a full gcd at a leaf simply identifies
the already-prime d; it is never advertised as a proper factor of d.

Gcd 1, full gcd and proper gcd are all accounted for. Singleton recomputation
uses a constant number of O(n)-bit integer roots and gcds, conservatively
O(n^3)+Pr(n). No zero is known in advance or treated as a locatable certificate.
The identity R(full,M)=0 can itself be deduced from coverage, but returning
that one value is computationally useless without a paid locating procedure.

Finally strip **all** occurrences of every recovered prime from the original
N_0, merge with the preprocessing output, validate all primes and reconstruct
N_0. The residual product has no obligation to encode original valuations.
This costs poly(n), with at most n prime occurrences and no recursion into a
new hard semiprime. H004's multiplicity warning remains essential.

If a genuine product-or-factor algorithm had setup C and uniform *reachable*
interval cost P, the sufficient complete envelope would be

    N_0^(1/6) poly(n) + C + O((1+log V)(P+poly(n))). (4)

Its retained memory, scratch space, all failed computations and access must
be included in C,P. Hence C+P<=M^(tau+o(1)) poly(n) would suffice for exponent
max(1/6,tau). Equation (4) is conditional; no such sub-1/5 algorithm is supplied.

## 4. Small residuals: a paid reduction to zero-row location

Here is an explicit uniform range bound, without statistics about rounding.
Let delta=c(k)-2sqrt(kM), so 0<=delta<1, and h=t+delta. Since ceil(s)<=s+1,

    h < 3 + sqrt(M)/[4(K+1)sqrt(l_j)],
    z = 4sqrt(kM)h+h^2.

Use k<2l_j, k<=K, M<=K^3, and K>=16. They give

    z < 12sqrt(KM) + sqrt(2) M/(K+1)
          + (3+sqrt(K)/4)^2
      <= (12+sqrt(2)+1/16)K^2
      < 14K^2 < 16K^2.                            (5)

For the middle inequality, 3+sqrt(K)/4<=K/4 follows from K>=16
(put s=sqrt(K)>=4 and use s^2-s-12=(s-4)(s+3)>=0).
The definition of floor square root gives 0<=e<=2y. Therefore

    y<4K,       0<=e<8K.                          (6)

Also 8K<M: with U=M^(1/3)>=16, K<=U+1 and
8K<=8(U+1)<U^3=M. This completes the singleton justification above.

Set E=8K and perform a **charged** small-factor search through E on M. Use
the same ordinary factorial product and gcd descent as the accepted small-
factor stage, not a sieve listing all E integers. If a prime <=E divides M,
return a proper factor. Full product gcd=M is resolved by integer-interval
descent, since every integer in [1,E] is smaller than M. The cost is

    E^(1/2) poly(n)=M^(1/6) poly(n),

including the unsuccessful case and factor recovery. Workspace is
soft-O(M^(1/6)n). All previously recovered multiplicities remain tracked.
This is optional in the final algorithm but is included in its ledger so
the following conclusion holds on every continuing input:

    p,q > E.

For every nonempty original row interval I and every d>1 dividing M,

    gcd(d,R(I,d)) = d  iff some row of I has e=0;
    gcd(d,R(I,d)) = 1  otherwise.                  (7)

Indeed a nonzero e is a positive integer <E<p,q, so it is a unit modulo
each d|M; a zero annihilates the product. In particular no exact residual
product has a **proper** nonunit gcd on this remaining domain. The factor-or-
residue permission does not create an intermediate residual gcd success here.
It could still help a materially different computation through some other
intermediate nonunit; (7) does not rule that out.

Thus a proved interval *zero-existence decision*, with paid setup and query
costs as in (4), would already suffice: start from the known existence on
the full descriptor and bisect in its original ordering, finally applying
(3). Exact unit residues are more information than that reduction needs.
This observation grants no zero-decision oracle. No routine computing those
decisions at the target cost has been found.

## 5. Concrete selected realization: factor-or-unit by integer envelopes

Three alternatives were considered within this lens. Direct residual batch
inversion still needs the residuals, and (7) isolates precisely its zero
failure. An explicit histogram over e=0,...,E-1 already allocates Theta(K)
entries before explaining how to obtain their counts. Neither is developed
as a surviving algorithm. The selected alternative replaces the rounded
values by a certified interval **superset** of the linear factors and exploits
the permission to return any valid factor found there. Its output contract
does not pretend that a padded product equals R(I,M).

### 5.1 Search interface and constructed interval

`HullProbe(M,I)` takes a nonempty original row interval, on the continuing
semiprime domain. It returns either a verified proper factor of M, or
`UNIT(I)`, a correct assertion that every e in I is a unit modulo M. It is
allowed to find a factor at an integer unrelated to any actual row. A valid
factor solves the actual factoring task regardless of that integer's origin.
It must never return an unlocated `HIT` or interpret padding as a real row.
An empty interval returns UNIT, consistently with empty product 1.

Decode its first and last k as a,b. The t endpoints are retained in I; for
the containing interval use the safe global T_0. Compute only c(a),c(b), and
set

    L=max(1,c(a)-4K),
    U=min(M-1,c(b)+T_0+4K),
    H=U-L+1,  C=ceil(sqrt(M)),  ell=min(H,C).        (8)

By (6), monotonicity of c(k), T_j<=T_0, and the accepted 1<=A_±<M,
every A_± from I belongs to [L,U]. This holds for same-k partial t ranges,
band boundaries, singletons and repeated sign values. Store I alongside
L,U, so any later request still refers to the original rows. Only O(poly(n))
descriptor access and two scalar roots are needed; no list of interior roots
is generated.

Compute

    Q=product_(v=L)^(L+ell-1) v mod M,
    g=gcd(M,Q).                                   (9)

If g=1 and ell=H, every integer in the containing interval is a unit, so
both factors of each original pair are units and UNIT(I) is correct by (1).
This conclusion does not need preservation of product multiplicities.

If ell<H, then ell=C. Since p<=sqrt(M)<=C, **any** C consecutive integers
contain a multiple of p. Hence g>1 in that case. Thus the program can return
UNIT on g=1 without falsely certifying an unexamined suffix. This uses the
known semiprime input promise, not a supplied value of p. For a known proper
d|M, d is already a prime factor and the outer factorer terminates rather
than calling HullProbe; no prime-modulus version of this cap argument is used.

If 1<g<M, validate and return it. If g=M, bisect the tested **integer**
interval and compute the left interval product modulo M. A proper gcd
returns a factor; gcd=M takes the left child; gcd=1 takes the right child.
All tested integers remain in [1,M-1]. Thus a singleton can never have gcd M,
and a proper split must occur. Distinguish this integer descent from a descent
to a real (j,k,t) row: the former returns a directly verified factor and makes
no claim to have located a zero row.

### 5.2 Product construction and all costs

For any tested consecutive integer interval of length s>=1, set
h=ceil(sqrt(s)), q=floor(s/h). Over Z/MZ construct

    F(X)=product_(i=0)^(h-1)(X+L+i).

Form it by a balanced product tree, evaluate it at 0,h,...,(q-1)h by a
monic subproduct/remainder tree, multiply those values, then multiply the
fewer than h remaining integers. This identity gives exactly (9). The program
constructs the degree-h coefficient array before checking its final product
gcd; this order is part of the selected realization.

No modular inverse is used: remainder-tree divisors are monic, whose reversed
polynomials have constant term 1. Formal reciprocal doubling uses additions
and multiplications even over a composite ring. Coefficient packing uses
slots of O(n+log h) bits, so packed intermediates have O(h(n+log h)) bits.
Fast integer multiplication, balanced trees and sequential level storage give

    s^(1/2) poly(n) bit time,
    soft-O(s^(1/2)n) scratch bits.                 (10)

Here all s<=C=O(M^(1/2)), so log s=O(n). Sequential tree traversal, coefficient
writes, reductions, tails, indices, gcds, failed unit outcomes and regenerating
the data on every query are charged. No value-dependent table or free random
access is needed. No denominator, modular root or order oracle occurs.

In a full-gcd recovery chain the lengths are at most ell/2, ell/4,... up to
integer rounding. Summing (10) gives O(sqrt(ell) poly(n)), since the geometric
sum of square roots is bounded and the O(log ell) small/control costs are
polynomial. There is one unresolved branch at a time, and no failed leaf or
random retry. Peak space is soft-O(sqrt(ell)n)+poly(n); earlier product data
are released before the next descent query.

Thus a cold HullProbe costs at most M^(1/4) poly(n), including extraction;
shared preparation is only the O(n^4) H029 descriptor. This is an upper bound
for all original intervals in its promised domain, not an exact value of each
execution's cost.

### 5.3 Complete factorer and the first actual obstruction

After the two paid small-factor stages, call HullProbe on the full original
row interval. It cannot return UNIT: by coverage there is a zero row whose
paired product is divisible by M. Alternatively, the interval cap argument
alone ensures a hit. Return the factor it finds, validate its complementary
prime, restore the original multiplicities, and reconstruct N_0.

The full bound, including preprocessing that may itself finish the input, is

    T(N_0) <= N_0^(1/6) poly(n)
                 + M^(1/6) poly(n)
                 + M^(1/4) poly(n)
                 + poly(n)
            <= N_0^(1/4) poly(n).                  (11)

Peak memory is soft-O((N_0^(1/6)+M^(1/4))n)+poly(n). There is no randomness,
success exception or restart term. The conditional formula (4) concerns a
different exact-product/zero-decision interface; it is not substituted into
(11) as if HullProbe returned exact paired residues.

The obstruction is already in this realization's full root query. Its
containing interval has

    H >= c(K)-c(1)+1
      >= 2sqrt(M)(sqrt(K)-1)
      >= 6sqrt(M),                                (12)

using K>=16. The clipping in (8) cannot remove c(1) or c(K), which are
positive and <M. Hence ell=C=ceil(sqrt(M)). The selected product constructor
actually writes a polynomial of degree h=ceil(sqrt(C))=Theta(M^(1/4)). Its
leading coefficient is 1 even modulo M. It therefore incurs at least
Omega(M^(1/4)) coefficient-slot writes before its first final product gcd.
No lower bound on slot bit width is needed for this conclusion.

This is a representation/execution-order obstruction for the specified
factorial construction on inputs that reach this query. It is not inferred
from its upper bound alone. Such continuing inputs are not excluded by the
extra cutoff: sufficiently large balanced distinct semiprimes have
p>8ceil(M^(1/3)). The argument does not assert that an arbitrary factorer or
an early-exit rearrangement must take that time.

Without the cap, the full hull has length Theta(M^(2/3)), and the same method
would cost M^(1/3) poly(n). The cap saves that padding cost by reverting to
the ordinary fact that sqrt(M) consecutive integers contain a multiple of
the smaller factor. It discards the special sparse pairing advantage. Thus
(11) is a rediscovery/specialization of shifted-factorial factoring, not an
improved Lehman search or a new exponent. A global full-product value of zero,
cheap small-residual inverses or exact H030-style polynomial certificates do
not remove this first cost in the chosen program.

## 6. Disposition and stopping boundary

**Strongest supported conclusion:** a paid divisor-only paired-residual
reduction has cheap and reliable zero-row recovery. After a further
M^(1/6) factorial stage, its outstanding successful search is precisely an
original-interval zero-row location problem. The selected root-free integer-
envelope realization is complete but returns known N_0^(1/4) scale. All new
derivations here remain unaccepted until independent review.

**Exact limitation:** this report supplies no uniform sub-1/5 procedure to
locate a zero row or decide the needed original row intervals. The envelope
implementation loses the
arithmetic sparsity by filling a consecutive integer interval; its prescribed
polynomial construction is already too large. This closes only that
realization. H030's characteristic-zero block obstruction was not used to
infer a lower bound on modular residual products, and no factoring lower bound
is claimed.

**Next proof/test:** none selected. The selected realization is already closed
symbolically; a timing run, larger sweep, or restatement of the missing
zero-decision routine would not change that conclusion. The coordinator may
choose independent review of the scoped reductions, but this researcher
neither launches nor prescribes a duplicate review or new candidate merely to
fill a follow-up quota. Verified COMPLETE factoring improvement remains NONE.
