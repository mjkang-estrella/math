# W002 Lens A — First independent review of paired residuals and HullProbe

2026-10-08. **RECOMMEND ACCEPTANCE of the scoped deductions and finite
factorer; REJECT the selected realization as a sub-1/5 improvement.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.
This is the first review, with no earlier findings or proposer responses.
Acceptance remains the coordinator's decision; this report changes no shared
status or submitted artifact.

The six requested mathematical claims pass within their stated domains.
I found no required algebraic repair. The proofs below make explicit the
rounding boundaries, complete preprocessing, two different descents, sequential
costs, and an unbounded family reaching the dense construction. In particular,
HullProbe is a factor-or-UNIT procedure, not an exact residual-product routine
and not a zero-row decision procedure. Its complete upper bound is
N_0^(1/4) poly(log N_0). Its mandatory dense coefficient writes give an
Omega(M^(1/4)) lower bound on continuing executions of this specific program,
including an unbounded family with N_0=M. Nothing here lower-bounds other
modular-product algorithms or factoring.

## 1. Frozen object, review authority, and evidence

The authoritative 414-line submission and its preserved submitted draft both
verify at SHA-256

    35ae0bb4b0412f7a5a1d3a26c5e1d554b32df614e6c05437de3d355e5d90872f

The coordinator intake verifies at

    c49cfb0725fe47cc1d4923c184bafb3ee76792b52b35ded4b4851286c161685e

The frozen W002 brief verifies at

    5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723

I independently verified all 17 submission input snapshots and all 27 original
delivery entries. At this review's capture time, both current STATE and current
W001 synthesis differed from their submission snapshots. This is a later
mutable-context observation, not an alteration or failure of the frozen
evidence. The intake's earlier statement that only STATE differed is retained
unchanged. Every other recorded current input matched its submission hash.

[Evidence directory](W002-residual-review-evidence/) contains 48 initial input
copies, including the submission, intake, submitted draft, frozen brief,
instructions, accepted dependencies, old input snapshots and original
manifests. Its [intake verification](W002-residual-review-evidence/intake-verification.json)
records each identity and comparison. The original constructive wrapper plus
the exact frozen brief and this review assignment are separately preserved.
The [delivery manifest](W002-residual-review-delivery.sha256) seals this report
and all review evidence, excluding the manifest itself.

Read the required instructions, specification, research/team protocols,
current captured STATE, W001 synthesis, corrected H029 and H030 reports and
dispositions, H004's reduction/disposition, H031's completed disposition, and
the submission and source notes. Dependency scopes used here are:

* H029 B1–B4: paid reduction to a distinct semiprime, exact original descriptor,
  Lehman coverage, polynomial-cost decoding, and positive linear leaves <M.
* H004 sections 2, 4 and 5B: valuation-aware descent, original multiplicities,
  and the ordinary monic factorial product method. Its final-prime argument
  at a square-root cutoff is not applied to the cube-root cutoff.
* H030: ordinary monic polynomial arithmetic over composite rings and the
  scope of its accepted characteristic-zero representation obstruction.
  Its obstruction is not a premise for this review's modular conclusions.
* H031 disposition and current handoff: completed-review status only. No
  relation-generation or ECM draft supplies a mathematical premise here.

No sibling W002 draft contents were read, no task was duplicated or delegated,
and no task registry was queried. Work was symbolic reasoning, document
retrieval/inspection, copying, hashing, and writing these owned artifacts.
There was no finite mathematical test, factor sample, sweep, implementation,
benchmark, package, Lean action, shared-file write, commit or publication.
Hash computations and document handling are not mathematical experiments.

## 2. Reachable domain and unchanged original indices

Let n=bitlength(N_0), K_0=ceil(N_0^(1/3)). H029's first stage finds the prime
support of N_0 among integers through K_0, then removes every occurrence of
each recovered prime from the original input. A remaining M has all prime
factors >K_0. Three factors counted with multiplicity would have product
greater than K_0^3>=N_0, impossible because M divides N_0. Consequently the remaining
cases are 1, a prime, a prime square, or a product of two distinct primes.
Deterministic primality testing and an exact square test resolve the first
three; bounded M<4096 has the inherited finite trial-division branch.

Thus the new difficult stage really has

    M=pq>=4096,   K_0<p<q,   K=ceil(M^(1/3))<=K_0,

with p,q odd, K>=16, K<sqrt(M), and
sqrt(M/(K+1))<M^(1/3)<=K<p. These are exactly sufficient for Hittmeir's
stated Lehman theorem. None of p,q is an algorithm input.

The bands partition k=1,...,K in increasing order, including a singleton last
band when K is a power of two. A band has m_j=h_j-l_j+1 values of k and
w_j=T_j+1 values of t. Store the cumulative row counts

    P_j=sum_(i<j) m_i w_i.

For a zero-based row index r, locate the unique band with
P_j<=r<P_j+m_j w_j, then set

    k=l_j+floor((r-P_j)/w_j),   t=(r-P_j) mod w_j.

This explicitly preserves the original row, even when values of e, x, y or
the signs repeat. The O(n)-band descriptor takes O(n^2) bits. Exact rational
ceiling roots for T_j are computed by finding the least integer u with
16(K+1)^2 l_j u^2>=M, followed by T_j=1+u. All comparison operands have O(n)
bits. An O(n^3) scalar root bound gives O(n^4) descriptor construction;
sequential band scanning and decoding are polynomial in n. No root table is
constructed. The usual geometric band sum gives V=Theta(K).

H029's leaf bound can also be checked without any new promise: y<x, so
A_->0 and A_+<2x. Its x bound gives

    2x <= 4sqrt(2) M^(2/3)+6+M^(1/6)/2 < 8M^(2/3)<M

for M>=4096. For the middle comparison put U=M^(1/3)>=16, use
4sqrt(2)<6 and 6+sqrt(U)/2<U^2. The last comparison uses U>8.
This independently verifies the strict endpoints needed later.

The exact integer identity A_- A_+=4kM+e immediately gives equation (2) for
d|M. It is not valid for an arbitrary modulus merely because d<=M.
In the flattened minus/plus order, a contiguous sign interval has at most
two unpaired endpoint signs. Compute each such sign once, multiply its
residue separately, and apply (2) to the remaining complete pairs. A singleton
sign is peeled only once; if no complete pair remains its paired product is
1. Equal signs still occur twice when both original positions are requested.
The actual new factorer needs row intervals only.

## 3. Equations (5)–(6): the strict residual bound passes

Put delta=c(k)-2sqrt(kM) in [0,1), including delta=0 at an exact square, and
a_j=sqrt(M)/(4(K+1)sqrt(l_j)). Since t<=1+ceil(a_j)<=2+a_j,

    h=t+delta<3+a_j,
    z=4sqrt(kM)h+h^2>=0.

Using k<2l_j, k<=K, l_j>=1 and M<=K^3 gives

    4sqrt(kM)h < 12sqrt(KM)+sqrt(2) M/(K+1),
    h^2 < (3+sqrt(K)/4)^2.

For K>=16 and s=sqrt(K)>=4, (s-4)(s+3)>=0 is precisely
3+sqrt(K)/4<=K/4. Hence

    z < (12+sqrt(2)+1/16)K^2 < 14K^2 < 16K^2.

The weak inequality at K=16 is harmless: strictness already comes from
delta<1, and sqrt(2)<3/2 leaves a strict margin in the constant. No rounding
statistics or non-square assumption was used. At M>=4096 the boundary K=16
can occur only at M=4096, which is removed by preprocessing; the range proof
nevertheless covers that boundary directly.

With integer z and y=floor(sqrt(z)),

    y^2<=z<(y+1)^2   implies   0<=e=z-y^2<=2y.

Thus y<4K and 0<=e<8K. To compare with M, put U=M^(1/3)>=16. Then
K<=U+1 and U^3>=256U>8(U+1), proving 8K<M with strict inequality.
The conclusions apply to every original row, including maximal t, partial
bands and repeated values. **Recommend ACCEPT (5)–(6), without repair.**

## 4. Exact products, zero-row location and recovery

### 4.1 Recovery before the additional cutoff

A total exact-product-or-factor primitive must return a verified proper
divisor of its supplied d, or the exact residual product. On reachable
unresolved calls d=M. If it returns a factor, validate it and M/f and stop;
both are prime by the established semiprime promise. Prime-modulus calls are
unnecessary. The declared d|M interface can include them, but the factorer
does not require any proper-factor output for a prime d.

Otherwise coverage makes the full residual product zero modulo M. At an
internal original row interval with product divisible by M, query its left
midpoint child. A proper gcd finishes; a full gcd retains the left child;
gcd 1 retains the right. The last inference is cancellation of a unit in
the divisibility proof and needs no computed modular inverse. At most one
unresolved child survives each level. Thus the number of product calls is
at most 1+ceil(log2 V), including a root call if one is actually made.
The root can instead be initialized from the coverage theorem at polynomial
control cost; a made root query cannot be declared free.

A full internal gcd need not identify any individual zero before the cutoff:
different nonzero residuals may supply different primes. At the eventual
singleton, however, M|e and 0<=e<M force e=0. Recompute that original row
by the explicit decoder, then put a=A_- and b=A_+. We have M|ab with
1<=a<=b<M. If gcd(M,a)=1, then M|b, a contradiction. If gcd(M,a)=M,
then M|a, also a contradiction. The remaining gcd is p or q. The other
sign contains the complementary prime. Indeed p,q>K>=k and both are odd,
so neither divides 4k; in the equality ab=4kM each occurs to valuation one.

For a zero row with y=0, a=b=x and M|x^2. Squarefreeness would give M|x,
contradicting 0<x<M. Such a zero row cannot be reached. A row with y=0 and
e>0 would also contradict e<=2y; thus on this domain equal-sign rows do
not occur at all, although keeping both positions is the correct descriptor
convention and costs nothing in the proof. This is a symbolic exclusion,
not permission to filter rows using uncomputed values.

Recomputation uses two scalar integer roots, O(n)-bit arithmetic and a gcd,
with O(n^3)+Pr(n) a conservative bound. All cases gcd 1, proper gcd and full
gcd are covered. No singleton factoring oracle is present.

### 4.2 Additional paid search and equation (7)

Set E=8K<M. Compute the product of the integers 1,...,E modulo M by the
factorial method analyzed in section 6 below. If its gcd is 1, every prime
divisor of M exceeds E: a prime <=E would itself occur in the product.
If its gcd is proper, the split is already complete. If the gcd is M,
descend in the tested integer interval, preserving M|product on the one
unresolved branch exactly as above. A singleton v<=E<M cannot have full
gcd, so a proper split must occur. Unit leaves cannot be reached with that
invariant. There is no trial division of all E integers and no need to
factor an arbitrary residual at a leaf.

The initial product and all descending recomputations cost
O(sqrt(E) poly(n))=M^(1/6) poly(n), with soft-O(sqrt(E)n) scratch plus
polynomial control space. This includes the unsuccessful search, where
gcd=1. At the smaller bounded M scales E may exceed ceil(sqrt(M)); that
does not invalidate this stage: its product routine works for E<M and still
has log(E)=O(n). The cap is a separate feature of HullProbe.

Only after this stage returns no factor do we infer p,q>E. Every nonzero
residual satisfies 0<e<E<p,q and is a unit modulo M, p and q. A zero
annihilates the product for each nontrivial d|M. Consequently equation (7)
holds for every original nonempty interval. An empty interval has product 1
and contains no zero, consistently. No residual product has a proper
nonunit gcd on this remaining domain. This says nothing about other
intermediate quantities of a different algorithm.

### 4.3 Exactly what the conditional implication says

A correct original-interval zero-existence decision now suffices for a
binary location search: the root is known to contain a zero; decide the
left child, retain it on YES, and otherwise retain the right. After at most
ceil(log2 V) decisions, apply the singleton recovery above. A NO answer
must certify absence on that entire original interval. A YES answer need
not supply a row, but its later location is charged.

With total uniform setup C and reachable-query cost P, the submission's
equation (4) follows. Including the optional second stage adds
M^(1/6) poly(n), already absorbed by N_0^(1/6) poly(n). Here “reachable”
means every call that the finite adaptive factorer can actually make on
every promised input, not an input distribution or a favored branch.
The C,P bounds must include all failures, nonunit handling, access and
recovery internal to the primitive. An unresolved failure output does not
satisfy this interface merely because its time was counted; any fallback
must return a permitted answer and its full cost belongs in C,P.

Thus C+P<=M^(tau+o(1)) poly(n) would imply complete exponent
max(1/6,tau). This is a conditional reduction, not an instantiated algorithm.
The known full-product answer zero supplies no information locating an
original row. The equivalence in (7) does not identify factor-or-UNIT with
either exact products or YES/NO zero decisions.
**Recommend ACCEPT the reduction and paid cutoff at precisely these scopes.**

## 5. HullProbe correctness on every promised original interval

For a nonempty interval, its first and last k values a,b satisfy a<=b because
the original band/k ordering is monotone. For every included row,

    c(a)<=x<=c(b)+T_0,   0<=y<4K.

Thus both signs lie between c(a)-4K and c(b)+T_0+4K. Intersecting with
[1,M-1] retains them because of the strict leaf bound. This proves that the
clipped [L,U] is nonempty and contains every required sign, including
singletons, partial t endpoints, band crossings and repeated values.
Keeping the original interval identifier prevents decoding a padding integer
as an original row. Only two c-values are computed.

Let C=ceil(sqrt(M)), ell=min(U-L+1,C). The tested prefix remains wholly in
[1,M-1]. If its length equals the hull length and its product is a unit,
each tested integer is coprime to M; hence each original A_- and A_+ is a
unit and so is their product e modulo M. A UNIT answer is sound. Multiplicity
information is unnecessary for this one-direction unit assertion.

If the prefix is truncated, ell=C. To make the cap proof explicit, let
v=p ceil(L/p). Then

    L<=v<=L+p-1<=L+C-1.

This integer lies in the prefix and is divisible by the unknown p, since
p<=sqrt(M)<=C. Therefore its product gcd is >1. The supposedly truncated
unit branch is impossible on promised inputs. This is a proof about p,
not an algorithm that obtains p for free. The same argument applies when
H=C, although the untruncated UNIT proof alone was already safe.

For a proper gcd, validate and return it. For gcd M, keep the invariant
M|product of the current tested integer interval. Query its left product;
use the same three gcd branches as in section 4. A singleton full gcd
would require M|v for 1<=v<M, impossible. Since length strictly decreases,
a proper gcd must be encountered. This pays for locating a useful integer,
which may be padding. It need not locate a descriptor row, prove a zero
exists in the requested row interval, or return the original residual
product. An incidental factor on a zero-free interval is a valid output.

For the empty input interval, UNIT is sound without decoding endpoints.
For a known proper d|M, the outer factorer has already finished the split;
no cap or proper-factor guarantee on an unknown prime modulus is invoked.
HullProbe is not claimed correct on prime M or arbitrary unpreprocessed M.
**Recommend ACCEPT this factor-or-UNIT contract, without broadening it.**

## 6. Complete bit, space and access costs

### 6.1 One exact consecutive product

For an interval [a,a+s-1], s>=1, put h=ceil(sqrt(s)) and b=floor(s/h).
For integer s>=1, 1<=h<=s, 1<=b<=h, and 0<=s-bh<h. The polynomial

    F(X)=product_(i=0)^(h-1)(X+a+i)

evaluated at jh, j=0,...,b-1, multiplies precisely the disjoint integers
a,...,a+bh-1. Multiplying the tail a+bh,...,a+s-1 includes every integer
exactly once, including when the tail is empty. For s=1 this uses h=b=1
and returns a modulo the working modulus. An offered empty product is 1.

Construct F by a balanced product tree. Build monic products of X-jh and
use a remainder tree to evaluate F. A monic divisor has reversed polynomial
G with constant term 1. Starting with B=1, the update B'=B(2-GB) satisfies

    1-GB'=(1-GB)^2.

It therefore doubles the precision of the reciprocal as a formal power
series over any commutative ring. No inverse of a residue, point difference,
2 or factorial is used. Truncated multiplication and reversal give monic
polynomial division. Reduction modulo X-jh gives evaluation. Coincident
residues or composite moduli do not invalidate the procedure. This is
ordinary evaluation, not interpolation.

For maximum temporary degree D=O(h) over Z/dZ, normalize coefficients to
[0,d-1] and choose a binary packing base larger than (D+1)(d-1)^2. Each
convolution coefficient fits one slot, of width O(log d+log(D+1)); packed
integers have O(h(log d+log(h+1))) bits. Reduce unpacked coefficients after
each multiplication. Fast finite integer multiplication thus gives
h poly(n) bit cost including normalization and unpacking, since every d
and every relevant index have O(n) bits. The larger packed operands are
charged; they are not treated as n-bit scalars.

Each tree level has O(h) total degree and there are O(log(h+1)) levels.
For evaluation, storing the subproduct levels costs O(h log(h+1)) residue
slots. Scan them sequentially in reverse level order while carrying the
corresponding remainders; their total degrees per level are O(h). Product
construction uses adjacent-pair scans. This gives sequential access with
logarithmic storage/traffic overhead, not free indexing into an enormous
table. Rebuilding levels instead also changes only polynomial logarithms.
The fewer than h tail operations, b output products, scalar gcd, root/index
work and clearing/releasing temporary data all fit

    O((sqrt(s)+1) poly(n)) time,
    soft-O((sqrt(s)+1)n)+poly(n) scratch bits.

The polynomial term includes scalar roots and primality/control work when
called by the surrounding algorithm. Integer-multiplication workspaces can
be chosen within soft-linear space; no full integer factorial is materialized.
The same construction applies for first-stage divisors d<=N_0, not just M.
For those smaller d retain log(h+1) in the packing width; it is still O(n).

### 6.2 Repeated products and both preprocessing stages

In a one-branch full-gcd descent starting with length s, the successive
unresolved lengths are at most ceil(s/2^r). The queried left children are
no larger. For O(log(s+1)) levels,

    sum_r sqrt(ceil(s/2^r))
        <= sqrt(s) sum_r 2^(-r/2)+O(log(s+1)).

This is O(sqrt(s)+log(s+1)); all small/control terms fit poly(n). Thus the
initial product and paid recovery preserve the sqrt(s) poly(n) envelope.
Only one path remains live. Previous polynomial data may be freed before
recomputing the next child. There is no free right-child product obtained by
division, no successful-later retry assumption and no unpriced failed leaf.

The first H029 stage needs more than this single semiprime path, because its
input is arbitrary. It starts with g_0=gcd(N_0,K_0!) and applies H004's
valuation partition to g_0, not all of N_0. If d|Q_left Q_right and
u=gcd(d,Q_left), then d/u|Q_right. The product of all active divisors at a
depth divides g_0, so there are at most n active nodes per depth and at most
n nontrivial leaves in total. Each product query costs at most
sqrt(K_0) poly(n); a leaf divisor is <=K_0 and is fully trial-factored in
sqrt(K_0) poly(n), with all validations charged. The O(n log(K_0+1))
queries and <=n leaves therefore cost N_0^(1/6) poly(n). This is the paid
small-factor stage, not a sieve listing K_0 primes or integers.

The second stage uses the one-branch semiprime argument with s=E=8K,
so costs M^(1/6) poly(n). A cold HullProbe uses s=ell<=C=O(sqrt(M)),
so costs M^(1/4) poly(n), including factor extraction, even on an interval
that ultimately returns UNIT. All trees are regenerated and charged on each
actual product call. The full factorer invokes HullProbe once after the
two stages; it does not also run a row-location search.

### 6.3 Original multiplicities and complete envelope

Retain recovered prime identities, remove duplicate identities, and divide
a fresh copy of original N_0 by every recovered prime to exhaustion.
Count exponents, validate prime outputs deterministically, and reconstruct
N_0. The first-stage support suffices even if K_0! contained too few copies
of some prime. The last difficult remainder is a distinct semiprime, so a
proper split supplies both remaining primes without a new hard recursion.
At most n prime occurrences and polynomially many n-bit control/arithmetic
steps are needed; include at most O(n) calls to the fixed polynomial-time
primality algorithm. No original valuation is inferred from an e-product.

For inputs finishing earlier, omit the later stages. Otherwise the total is

    N_0^(1/6) poly(n)+M^(1/6) poly(n)+M^(1/4) poly(n)+poly(n)
        <= N_0^(1/4) poly(n).

A safe peak-space bound is

    soft-O((N_0^(1/6)+M^(1/4))n)+poly(n),

including descriptor, input/output, polynomial trees and traversal state.
The sum is conservative because the stages run sequentially. No randomness,
success probability, restart count, root oracle or prior factoring advice is
used. These are bounds for a finite on-paper classical algorithm; no code
timing or Lean machine refinement is claimed. **Recommend ACCEPT (10)–(11).**

## 7. Dense construction obstruction and its actual reachability

For the full original row interval, c(1) and c(K) both belong to [1,M-1]
(use the t=0 bounds). Clipping therefore cannot exclude either. For real
alpha,beta, ceil(alpha)>=alpha and ceil(beta)<beta+1 imply
ceil(alpha)-ceil(beta)+1>alpha-beta. Consequently

    H>=c(K)-c(1)+1
      >=2sqrt(M)(sqrt(K)-1)
      >=6sqrt(M)>=ceil(sqrt(M)).

This includes the ceiling boundary K=16 and proves ell=C. The prescribed
constructor forms the dense degree-h array before the product gcd, where
h=ceil(sqrt(C))=Theta(M^(1/4)). Its leading coefficient remains 1 modulo M,
so its actual degree is h. The selected representation writes h+1 slots,
including zero coefficients. At least Omega(h) bit-machine steps follow
from those writes without any assertion that each slot has a matching
Omega(n)-bit lower bound. The lower bound is about this actual execution
order, not inferred from the stated O(M^(1/4) poly(n)) upper bound.

There really are unbounded inputs reaching this operation. For sufficiently
large X, choose distinct primes X<p<q<=2X. Their existence follows, for
example, from Rosser–Schoenfeld's checked inequality

    pi(2X)-pi(X)>3X/(5 log X)   for X>=20.5,

whose right-hand side tends to infinity. Take original N_0=M=pq. Then

    X^2<M<=4X^2,
    8ceil(M^(1/3))<=8(4^(1/3)X^(2/3)+1)<X<p

for all sufficiently large X. Thus both prime factors exceed the second
cutoff and also K_0=K; neither preprocessing stage finds a factor. M is
composite, nonsquare and eventually >=4096, so it reaches the full hull
query. This is an existence proof for a family, not an algorithm using
prime-counting advice and not a performed prime search.

On this family N_0=M, so the coefficient-write lower bound is also
Omega(N_0^(1/4)). It rules out a uniform sub-1/5 complete bound for the
specified execution. On general inputs M can be much smaller than N_0 or
not reach HullProbe; an M-scale lower bound alone would not imply such an
N_0-scale statement. No claim that every input costs Omega(N_0^(1/4)) is made.

The uncapped hull length is Theta(M^(2/3)): the endpoint difference supplies
the lower bound and c(K)+T_0+4K=O(M^(2/3)) supplies the upper bound, including
clipping. Applying this same constructor uncapped writes Theta(M^(1/3))
coefficients. The cap merely returns to a length-sqrt(M) factorial search.
It does not preserve an advantage from sparse descriptor rows.

**Recommend ACCEPT (12) and this scoped dense-execution closure.** Sparse
representations, earlier factor tests, different execution orders, direct
modular products, different interval decisions and other factoring algorithms
are outside this lower bound. H030's Q-polynomial obstruction is unnecessary
and supplies no additional modular lower bound.

## 8. Primary-source comparison and limitations

All three cited submission sources were reopened and freshly downloaded;
HTTP 200 was obtained and all three files match the submitted source bytes.
[Retrieval records](W002-residual-review-evidence/retrieval.json) identify the
URLs, file sizes, hashes and retrieval times. Reading aids and originals are
both preserved. The [source notes](W002-residual-review-evidence/source-notes.md)
give exact reading scope and the additional archived prime-count source.

Harvey's Proposition 2.5 and Remark 2.6 confirm the factorial small-factor
method and its one-quarter specialization. His Remarks 3.2 and 3.4 already
discuss recovery using the product of multipliers and the one-sixth aspiration
from accelerating Lehman's search. Our p>K>=k verifies the relevant
coprimality premise. The present recovery proof additionally checks every
padded zero row through its strict leaf bounds; no priority claim follows.
The ordinary composite-ring arithmetic used here was checked against section
2 and proved explicitly above. [Harvey, arXiv:2010.05450v1](https://arxiv.org/html/2010.05450v1).

Hittmeir's Theorem 2.1, printed page 2001, has exactly the K+1 denominator,
weak upper endpoint and p-range used by H029. It includes x=ap+bq,
y=|ap-bq|, k=ab and points to the representation in Lehman's original proof.
This validates the cited coverage statement, without pretending that the
original 1974 proof was freshly audited. [Hittmeir, Math. Comp. 90 (2021)](https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf).

Harvey–Hittmeir's Theorem 1.1 states the complete rigorous deterministic
comparison O(N^(1/5)(log N)^(16/5)/(log log N)^(3/5)); its following paragraph
explicitly addresses small-factor preprocessing and semiprime reduction.
The reviewed one-quarter realization loses this matched comparison.
[Harvey–Hittmeir, arXiv:2105.11105v1](https://arxiv.org/html/2105.11105v1).

For the continuing family, I copied and rechecked the archived primary
Rosser–Schoenfeld PDF, its text and the printed-page-69 image. Corollary 3,
(3.8), supplies the inequality used above. The fresh DOI browser attempt
failed; the preserved primary bytes and visible page, not an inaccessible
new download, support this check. [Rosser–Schoenfeld (1962)](https://doi.org/10.1215/ijm/1255631807).

This is a focused comparison, not a global novelty search or a statement of
the latest record. H004/H029/H030 are reviewed project dependencies. The
original Lehman PDF's earlier retrieval limitation is preserved; it was not
retried. No external theorem is silently promoted from a conditional or
heuristic statement. A hypothetical N^(1/6) bound remains exponential in
binary input length and is a different comparison from heuristic GNFS.

## 9. Repairs, unresolved objections and narrow recommendation

**Required mathematical repairs: NONE for the six scoped claims reviewed.**
No replacement equation, changed cutoff or revised recovery branch is needed.
Sections 2–7 provide proof details for the terse parts of the submission,
particularly bounded cutoff cases, original-coordinate decoding, totality of
the conditional primitive, sequential data movement and N_0=M reachability.
These details do not change the selected program or add an experiment.

For any condensed disposition, retain these exact qualifications:

1. Accept e<8K<M and recovery only with the unchanged descriptor and stated
   M>=4096 domain. Proper-factor completion uses the paid distinct-semiprime
   promise; equal signs do not justify deleting original positions.
2. Accept equation (7) only after the additional E=8K search returns no
   factor. It is a theorem about residual products, not about every internal
   value a possible algorithm might compute.
3. Accept equation (4) only for a total, uniformly costed exact-product-or-
   factor routine, or separately for the stated original-interval decision
   routine. No unresolved failure output or unpriced restart is permitted.
4. Accept HullProbe as factor-or-UNIT. A returned padding factor is valid but
   does not certify a descriptor hit. It does not implement R(I,d).
5. Accept the complete N_0^(1/4) poly(n) upper envelope and the mandatory
   Omega(M^(1/4)) dense-write obstruction for the specified construction
   order on continuing inputs. The proof supplies an unbounded N_0=M family;
   it does not make the bound universal over inputs or alternative programs.

**Unresolved mathematical objections within those scopes: none found.**
The unresolved research obligation is still a real, uniformly cheaper
original-interval product/decision computation with its recovery and full
costs paid. It is not supplied by knowing the full product is zero, by fast
inversion of already computed units, or by naming a product expression.
No N-only polynomial-time factorer, new deterministic exponent or improved
general complete factoring bound is established.

Recommend retaining the reductions as reviewed mathematical statements and
closing only the selected dense factorial-envelope realization as a speedup.
No finite test, new candidate or further proof task is selected merely to
continue a quota. All original artifacts remain unchanged; the coordinator
can record the disposition separately. Verified COMPLETE factoring
complexity improvement remains **NONE**.
