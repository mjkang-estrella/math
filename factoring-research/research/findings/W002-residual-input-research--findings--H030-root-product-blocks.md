# H030 — Certified cubic blocks for exact nested-root products

2026-10-08. **Scoped deductions accepted after independent review; this
realization is rejected as a sub-1/5 construction. Verified improvement in
complete classical factoring complexity: NONE.**

Coordinator update: the [independent review](H030-independent-review.md) accepts
the mathematical core without algebraic correction. Three cost/notation
clarifications are adopted below. The byte-identical
[submitted draft](H030-submitted-draft.md) preserves the original report sealed
by the original manifests; those seals refer to the pre-clarification bytes.
See the [disposition](H030-disposition.md) for exact acceptance and limitations.

**Outcome:** the single realization below is a finite, exact specification for
the full RootProduct interface, but fails its intended compression. Its outer
rounded root alone requires Omega(M^(1/3)) explicit cubic block records. The
specified construction and query have the conservative upper bound
M^(1/3) poly(log M), not an exponent below 1/5. A symbolic extension also rules
out saving this particular dense polynomial representation merely by raising
degrees and explicitly patching exceptions. This is a representation result,
not a lower bound on RootProduct, rounded-polynomial products, or factoring.

No implementation, finite research experiment, sweep, replay, timing test,
package, Lean change, shared-code change, delegation, commit, publication, or
scheduler was used. The finite algorithms below were described, not executed.
Source downloads, text extraction, copying, hashing, and report editing are
evidence handling only. This is not an independent review of these deductions.

## 1. Authoritative input and unchanged scope

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, the complete H030 hypothesis, all 306 lines
of the corrected H029 construction, its 76-line disposition, all 622 lines of
its independent review, and H004's complete 464-line reduction review and
30-line disposition. The handoff supersedes STATE's old H029-intake instruction;
no coordinator work or prior review was repeated or polled.

The four supplied SHA-256 identities matched:

* H030 hypothesis: `51a0ffdb7ef8c1f1a80d3d72719e26b9dbbb14c9dfc6f20b946a309ae43c23be`.
* H029 disposition: `8c2ef4754aa49a02e4f20c23b92c90078223c37e2e22bd5eff2a0e0550f62e44`.
* Corrected H029 construction: `056e83ae5c7ce5f32a5fe720b54518f6036068d880a9a6ddc0e23cf41d8ec74d`.
* H029 independent review: `c42bd1a2f1dcd495992e6621f5cb87932db9047247862dd4734e7b413c476d52`.

Copies are identified by [H030-block-inputs.sha256](H030-block-inputs.sha256).
The STATE copy captures a later coordinator update; the source notes distinguish
that archived version from the older checkpoint read during intake.
[Source notes](H030-block-source-notes.md) give primary URLs, precise reading
scope and limitations; [delivery manifest](H030-block-delivery.sha256) seals
this report and its supporting artifacts. None of these hashes certifies a
mathematical claim. Original H029 evidence remains unchanged.

Put n=bitlength(M), K=ceil(M^(1/3)), and retain exactly H030's bands
l_j=2^j, h_j=min(2^(j+1)-1,K), and

    T_j = 1 + ceil(sqrt(M/[16(K+1)^2 l_j])),  w_j=T_j+1.
    c(k) = ceil(sqrt(4Mk)),
    x(k,t)=c(k)+t,
    y(k,t)=floor(sqrt((c(k)+t)^2-4Mk)),
    A(k,t,-)=c(k)+t-y(k,t),  A(k,t,+)=c(k)+t+y(k,t).

The order is j, k, t, minus/plus. Every M>=4096 and every integer 2<=d<=M
is allowed. No factorization, squarefreeness, semiprime, prime, or d|M promise
is used in this report's product algorithm or obstruction. Inclusive partial
intervals, singletons, duplicate signs when y=0, and the full interval are
retained; an empty query returns 1 mod d.

Write m_j=h_j-l_j+1 and V=sum_j m_j w_j. H029's accepted padding calculation
gives V=Theta(K), with O(n^4) time and O(n^2) bits for its short descriptor.
That descriptor is not a list of the roots. H029's paid N_0^(1/6) preprocessing,
root gcd initialization, divisor-of-input-and-product invariant, and stripping
of original multiplicities remain prerequisites of its accepted reduction.
They supply no stronger promise for this product interface.

## 2. One selected realization: certified Newton cubics

The attempted saving is to partition each k band into consecutive blocks on
which both integer root sequences are *exact rational polynomials of degree
at most three*. A constant number of initial exact roots constructs each
polynomial. A rational interval certificate either establishes every rounded
boundary throughout the block, or rejects the block and causes bisection.
Accepted leaves are then evaluated by polynomial products. This is one
finite-difference realization, not an assumed approximation theorem.

### 2.1 Constructor, including every failure

For a proposed block k=a,...,a+L-1 within one band:

1. If L<=3, compute and retain the actual c(k) and all y(k,t) for its L values
   of k and 0<=t<=T_j. These are explicit short terminal records.
2. Otherwise compute c(a+i) for i=0,1,2,3 by exact integer square roots and a
   square/equality comparison. Set

       C(u)=sum_(r=0)^3 Delta^r c(a) binom(u,r).

   All four differences are obtained from these four values. This constructs
   the unique rational cubic through them. Its coefficients have denominator
   dividing 6, and C(u) is integer for every integer u>=0.
3. Use the certificate in 2.2 for C. If it fails, discard its tentative data
   and bisect the block into lengths floor(L/2) and ceil(L/2). Recurse in order.
4. If the outer certificate passes, for each t=0,...,T_j compute the four exact
   y(a+i,t), i=0,...,3, and construct

       Y_t(u)=sum_(r=0)^3 Delta^r y(a,t) binom(u,r).

   Certify Y_t using 2.2. A failure for any t discards the tentative block and
   bisects it. The earlier t work is charged, including discarded records.
5. Only if every certificate passes, retain a,L,j,C and every Y_t, and stop
   recursing at this block.

Start with each complete dyadic band. The length decreases at each failed
attempt; length <=3 always terminates by exact evaluation. No search for a
favorable degree, denominator, modulus or input is hidden in this procedure.
No long block is certified by inspecting all its roots. There are no unlocated
exceptions: a failed certificate triggers charged subdivision of the whole
uncertified block. This can be inefficient even when the desired identity is
true; no favorable acceptance rate is assumed.

### 2.2 Exact rational certificate for both rounded boundaries

Let R(u)=4M(a+u). Require throughout the real interval 0<=u<=L-1:

    C-1 >= 0,
    R-(C-1)^2 > 0,
    C^2-R >= 0.                                      (O)

For each t, put X=C+t and Z=X^2-R and require:

    Y_t >= 0,
    Z-Y_t^2 >= 0,
    (Y_t+1)^2-Z > 0.                                 (I)

These are polynomials of degree at most 6 with rational coefficients. A fixed,
sufficient certificate is obtained without root isolation or floating point.
For each polynomial g, write

    g((L-1)v)=sum_(i=0)^6 a_i v^i,
    b_h=sum_(i=0)^h a_i binom(h,i)/binom(6,i),  0<=h<=6.

Then the exact identity

    g((L-1)v)=sum_(h=0)^6 b_h binom(6,h) v^h(1-v)^(6-h)

follows by substituting the binomial expansion of v^i in the degree-6
Bernstein basis. Its basis functions are nonnegative and sum to one on
[0,1]. For a weak inequality require every b_h>=0; for a strict inequality
require every b_h>0. These finite rational comparisons suffice for (O)/(I).
Failure means only that this sufficient certificate did not prove the block.
The use of a stronger real-interval test does not justify an identity on a
block that failed it.

At an integer u in an accepted block, C(u) is an integer at least 1. Hence
(O) gives C(u)-1<sqrt(R(u))<=C(u), proving C(u)=c(a+u), including square
arguments. Similarly Y_t(u) is a nonnegative integer, Z(u)>=Y_t(u)^2>=0,
and (I) gives Y_t(u)<=sqrt(Z(u))<Y_t(u)+1. Thus Y_t(u)=y(a+u,t).
Every floor/ceiling boundary is determined, including equality on the weak
side. No implication from merely having real error less than one is used.

All scalar roots, input products and initial values have O(n) bits. The Newton
differences have O(n) bits and denominators dividing 6. Squaring, substituting
(L-1)v and converting degree <=6 to Bernstein form leave O(n)-bit numerators
and constant denominators, because log L=O(n) and degrees are fixed. Each
certificate uses a constant number of exact O(n)-bit operations. Conservative
binary-search square roots cost O(n^3); coefficient/certificate work fits this
per-attempt-per-t allowance. There is no precision-refinement branch.

## 3. Exact products once a block is certified

This section pays for the product stage instead of granting it as an oracle.
It is the familiar baby-step/giant-step polynomial technique, specialized to
the constructed cubic coefficients. Section 5 shows why the prerequisite
block list is too large.

### 3.1 Clear rational denominators before reducing modulo d

The leaf polynomial in a block is C(u)+t +/- Y_t(u), a rational
integer-valued cubic. Division by 2, 3 or 6 modulo d is not permitted.
Separate u into its six residue classes, u=6z+r, 0<=r<6. Then

    F_(t,r,+/-)(z)=C(6z+r)+t +/- Y_t(6z+r) lies in Z[z].       (F)

Here is a coefficient proof, not an assumed unit denominator. If P is C or
Y_t, then H=6P is in Z[u]. Each nonconstant coefficient of H(6z+r) is a
multiple of 6. Its constant coefficient divided by 6 is P(r), an integer
because P is a sum of integer multiples of binom(u,i). Thus P(6z+r) has
integer coefficients. Form those coefficients by exact integer division
before reduction modulo d. The degree remains <=3 and all coefficients have
O(n) bits. There are only six classes and two signs per t.

This transformation also handles a clipped block: for u in [u_0,u_1], each
class gives the consecutive integer z range

    ceil((u_0-r)/6) <= z <= floor((u_1-r)/6).

Empty ranges are omitted. Reordering these factors is valid because Z/dZ is
commutative. No inverse of a leaf or prefix product is taken.

### 3.2 A finite all-composite-ring product routine

For one F in Z[z] of degree <=3 and z=z_0,...,z_0+s-1:

* For s=0 return 1. Otherwise set h=ceil(sqrt(s)) and q=floor(s/h).
* Construct all h shifted cubics F(W+i), 0<=i<h, by the binomial expansion of
  their four coefficients, reduced modulo d. This costs O(h) ring operations
  and charged O(n)-bit index/translation work.
* Multiply them with a balanced product tree to obtain

      H(W)=product_(i=0)^(h-1) F(W+i),  degree H<=3h.

* Evaluate H at z_0,z_0+h,...,z_0+(q-1)h with a monic subproduct/remainder
  tree. Multiply those q values and the fewer than h remaining values of F.

The exact identity H(z_0+jh)=product_(i=0)^(h-1) F(z_0+jh+i)
proves the result, including the tail. All factors are included exactly once.
F and H need not be monic: the *divisors used for evaluation* are monic.
Reversing such a divisor gives constant coefficient 1. Its formal reciprocal
is computed by h_new=h_old(2-f h_old) with precision doubling, involving
only additions and multiplications; there is no inversion of 2 or any
nonunit. The error squares over every commutative ring. Reduction modulo
W-a then gives evaluation. Coincident evaluation residues cause no problem.

For explicit bit costs, multiply degree-S residue polynomials by packing into
integers with slot width b satisfying 2^b>(S+1)(d-1)^2. Packed widths are
O(S(log d+log(S+1))), not O(n). A fixed quasi-linear integer multiplier,
balanced trees and their sequential data movement give soft-O(S(n+log S))
time and space majorants. This general width formula does not require
S=O(d); d may be as small as 2 while S is large. Store/copy tree levels
sequentially, including their logarithmic total traffic. Degree-3 shifts are
formed directly; no fast interpolation or factorial inversion is being
imported. Here S=O(sqrt(s)), log s=O(n), so the routine costs

    soft-O(sqrt(s) n) time and scratch bits, plus polynomial index work.

The six classes, both signs and w_j values of t therefore cost at most
w_j sqrt(L') poly(n) for a nonempty clipped certified block of length L'.
All modulus-specific reductions and trees are regenerated and charged on
every query. A factor of d found incidentally would not replace the required
exact output residue; this routine has no such failure branch.

### 3.3 Arbitrary intervals in the frozen leaf order

Use the O(n^2)-bit band descriptor to decode both leaf endpoints. If they
have the same k, compute the requested t/sign slice directly. Otherwise
handle the included suffix of the first k and prefix of the last k directly.
There are at most two such partial k rows; together they need at most
2w_0=O(M^(1/6)+1) exact row evaluations. This deliberately generous boundary
charge includes one-sign endpoints. It is never silently dropped.

The remaining part contains complete k rows, divided into consecutive ranges
in O(n) bands. Intersect these ranges with terminal constructor blocks. For
a certified block use (F) and 3.2; for a short explicit block use its actual
retained values. A clipped certified block inherits its identities, so no
new sampling/certification is needed. Sequentially scan the retained records
and charge the entire scan, even for a short query; no uncharged random
access is assumed. Multiplying the pieces returns exactly the requested
residue. In particular, singletons and full intervals have specified paths.

This does not replace A_- A_+=4kM+e by e. Both leaf factors are retained and
their products are valid for arbitrary d, including composite nondivisors
of M. Nothing here changes H029's recovery invariant or its paid root queries.

## 4. Full ledger for this finite specification

There are at most 2m_j-1 constructor nodes in band j. Charging w_j at every
node, even those failing early at the outer certificate, gives

    sum_j O(m_j w_j)=O(V)=O(K)

attempted scalar groups. Tentative coefficients are discarded before
recursing; all generation, certificate comparisons, failures, erasures and
record writes fit

    C_P(M,n)=O(n^4+V n^3)=O(M^(1/3) n^3+n^4).          (C)

Terminal cubic records contain O(w_j) coefficients; short records contain
at most 3w_j roots. Retained data occupy O(Vn+n^2) bits. A depth-first
constructor needs an O(n^2)-bit index stack and at most O(w_0 n) temporary
coefficient bits beyond its output. No huge exact product is retained.

For a query, let L'_b be the number of complete queried k rows in terminal
block b. Let V_short=sum_(short b) w_(j(b)) L'_b count queried (k,t) pairs
in short terminal records. Besides scanning the
O(Vn)-bit descriptor, a safe cost is

    P <= V poly(n) + (w_0+1) poly(n)
          + sum_(certified b, L'_b>0) w_j sqrt(L'_b) poly(n)
          + V_short poly(n).

Since sqrt(L'_b)<=L'_b for nonempty intersections and blocks are disjoint,
the sum is at most V poly(n). Thus

    C_P+P <= M^(1/3) poly(n).                         (U)

The largest product tree uses soft-O(sqrt(K)n) scratch bits, and the boundary
routine can stream its rows. Peak space including retained data is
O(Vn+n^2)+soft-O(sqrt(K)n); the construction's O(w_0 n) temporary space is
within this bound. Record reads, branch bookkeeping, writes of partial
products and changes of modulus have all been included. These are symbolic
bit-machine majorants, not implementation timings or Lean refinements.

If there were few long certified blocks, 3.2 could give the intended saving.
An upper bound of (U) alone would not refute a better analysis. The next
section supplies a lower bound on the *actual required representation* of
this realization, before any conjecture about fast products is relevant.

## 5. First exact obstruction: outer roots cannot have long cubic blocks

The scoped deductions in this section passed independent review. They use no
sampled inputs or numerical evaluations; their cost conclusions require the
explicit representations stated below.

Put U=M^(1/3) as a real number and consider the integer interval

    J={ceil(3U/4),...,floor(U)} subset {1,...,K}.

For U>=16 its length satisfies |J|>=U/4-1>=U/8, so |J|=Theta(K).
J may cross a dyadic-band boundary; intersecting a consecutive block with J
still produces a consecutive interval. J is only a proof device; if its
endpoints were needed algorithmically, the lower one is the least a with
64a^3>=27M and the upper is floor(cuberoot(M)), both exactly computable.

Let f(v)=2sqrt(Mv) for real v>0 and c(k)=ceil(f(k)). On [3U/4,U],

    f''(v)=-sqrt(M)/(2 v^(3/2)),
    -4/5 < -4/(3sqrt(3)) <= f''(v) <= -1/2.           (D)

The rational lower bound follows from sqrt(3)>5/3. Whenever k,k+1,k+2
belong to J, the finite-difference identity

    Delta^2 f(k)=integral_0^1 integral_0^1 f''(k+s+t) ds dt

puts Delta^2 f(k) between -4/5 and -1/2. Also e(k)=c(k)-f(k)
is in [0,1), including zero for square arguments, and
-2<Delta^2 e(k)<2. Therefore the integer second difference satisfies

    Delta^2 c(k) in {-2,-1,0,1}.                     (S)

### 5.1 Polynomial block lemma

Suppose a rational polynomial P of degree <=D equals c at L consecutive
integers in J, with no exceptions. Then

    L <= max(8, 4D-6).                              (B)

For L<=2 this holds immediately. Otherwise Q(v)=P(v+2)-2P(v+1)+P(v).
If Q is nonconstant, its degree is at most D-2. Each of Q+2,Q+1,Q,Q-1
is a nonzero polynomial with at most D-2 distinct real roots. By (S), their
union contains all L-2 consecutive triple-start positions. Consequently
L-2<=4(D-2), proving L<=4D-6 in this case.

If Q is constant, it is an integer m in {-2,-1,0,1}, since at least one
triple exists. A polynomial with constant second difference has degree at
most two (the leading term of a degree-d polynomial has second difference
of degree d-2 in characteristic zero). Hence P''=m. For E=P-f, (D) gives:

* if m<=-1, E''=m-f''<=-1/5;
* if m>=0, E''=m-f''>=1/2>=1/5.

The sign is constant. Let a be the block's first integer and
q=floor((L-1)/2). At a,a+q,a+2q we have 0<=E<1. For q>=1,

    |E(a+2q)-2E(a+q)+E(a)|
      = |integral_0^q integral_0^q E''(a+s+t) ds dt|
      >= q^2/5,

whereas the same absolute value is strictly less than 2. Thus q^2<10,
q<=3 and L<=8. For q=0 the result is immediate. This proves (B), including
D=0,1,2. Notice that no coefficient-height bound, Taylor estimate, statistical
distribution, primality assumption or rounding-gap assumption was required.

For a cubic, every intersection with J has length <=8. Any accepted block
of section 2 supplies such a polynomial P(k)=C(k-a), since translation
preserves its degree. Short explicit terminal blocks have at most
three positions. Covering all of J therefore requires at least |J|/8
terminal records. The chosen constructor writes these explicit records, so

    number of records >= |J|/8 >= U/64,
    C_P = Omega(M^(1/3)) bit-machine steps.           (L)

The constructor writes at least |J|/8 nonempty terminal records. Any actually
used field widths and storage traffic add costs; an O(n)-bit field upper bound
alone implies no Omega(n)-per-field lower bound. The weaker bound (L) already
suffices. Moving the
same record construction into the query would move this work into the full
interval query, rather than remove it. No lower bound on other query
algorithms is inferred.

This is the first decisive failure: the hoped-for short exact outer polynomial
description does not exist in this representation. Improving the sufficient
Bernstein certificate, perfectly certifying integer points only, or granting
the inner-root and modular-product work for free cannot remove (L).

### 5.2 Growing degrees and explicitly patched exceptions

This is a scope extension of the same representation, not another algorithm.
Suppose a block intersection of length L in J is represented by one rational
polynomial P of degree <=D with e explicitly listed exceptional k positions;
P(k)=c(k) is required at all the other positions. Then the following safe
inequality holds:

    L <= 4D+9e+8.                                   (E)

Each exception spoils at most three of the L-2 consecutive triples. If Q is
nonconstant, at least L-2-3e triple-starts are good, and the four-root-count
argument gives L-2-3e<=4(D-2), which implies (E).

If Q is constant and there is a good triple, Q=m is again an integer in (S).
After removing the e exceptions, there are at most e+1 consecutive runs.
The constant-Q argument in 5.1 bounds each good run by eight positions.
Thus L<=8(e+1)+e=9e+8. If there is no good triple, L<=3e+2 already follows.
Both cases imply (E). The proof includes empty good runs and short blocks.

For any partition of J into B such blocks, with total exception count E_all,
summing yields

    |J| <= 4 sum_b D_b + 9 E_all + 8B.               (E-total)

Apply this inequality with each polynomial's actual degree delta_b, assigning
the zero polynomial degree budget zero. Then

    W=sum_b(delta_b+1)+E_all >= |J|/9 >= U/72.

If every block separately materializes a dense list of delta_b+1 coefficient
slots and explicitly lists its exceptions, it writes at least W slots/entries.
A larger declared degree counts only if the extra dense slots are actually
written. Shared arrays, compressed expressions and direct modular generation
are outside this output-cost conclusion. Coefficient bit widths and finding
all exceptions add costs under the stated premise. Thus large degrees plus a
small explicit exception table do not restore a sub-1/5 construction bound
within this separately materialized dense representation. Exact dense Newton
or binomial lists have the same degree/entry accounting. This is no positive
exception-patching algorithm and grants no nonunit modular inverses.

This extension counts dense degree, not the number of nonzero coefficients
of an arbitrarily high-degree sparse expression. Implicit circuits,
implicitly encoded exceptions and specialized products of high-degree sparse
expressions would require other algorithms and are outside (E-total)'s cost
conclusion. The statement does not turn a degree bound into a lower bound on
every possible way to represent a polynomial.

## 6. What closes, what remains, and primary attribution

The selected contiguous exact-cubic/finite-difference realization fails the
H030 target for every sufficiently large M: (L) exceeds
M^(tau+o(1)) poly(n) for every fixed tau<1/3, in particular tau<1/5.
This conclusion concerns the representation's mandatory constructor; it
does not rely on treating an upper cost estimate as a lower bound. Its full
finite specification is exact on all requested inputs, but its known complete
bound stays at M^(1/3) poly(n). It therefore supplies no improved factoring
algorithm through the already accepted H029/H004 reduction.

The decisive distinction is between a polynomial *equal to the rounded
integer sequence* and a rational polynomial whose values still require a
floor or ceiling. Section 5 bounds the former. It does not bound how well a
real root can be approximated, or forbid a short exact description such as
ceil(P(k)/Q) with a proved correction rule. Such a floor-bearing expression
is not the polynomial input of section 3. Computing products from it without
expanding its rounded values would need a different proved operation. This
report neither supplies nor assumes that operation. Nonconsecutive residue
blocks, implicit exception sets, joint treatment of many blocks, direct
pair-product descriptions, and identities valid only after modular reduction
are likewise outside this obstruction. There is no general RootProduct or
factoring lower bound, and no average-input premise.

The primary check was deliberately limited, with no exhaustive novelty claim:

* [Harvey, arXiv:2010.05450v1, §§2.1–2.3, Lemma 3.3 and Remark 3.4](https://arxiv.org/html/2010.05450v1).
  Lemma 2.3 takes the root list as input; its cost does not construct this
  report's integer-root data. Lemma 2.1's proof gives the general packed-width
  expression, with the simplified bound requiring its degree restriction.
  Proposition 2.5 supplies the familiar small-factor scale. Remark 3.4
  already asks whether a full square-root saving on Lehman's original
  N^(1/3) search can yield exponent 1/6. That ambition is not new here.
* [Bostan–Gaudry–Schost, SIAM J. Comput. 36 (2007), 1777–1806, DOI 10.1137/S0097539704443793](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf).
  The introductory factorial construction explicitly works over arbitrary
  rings using ordinary product/evaluation trees. Their faster structured
  evaluation in Theorem 8 assumes a specified unit product and its inverse;
  Lemma 13 handles failed unit conditions by finding a factor in its factoring
  application. Neither permits returning a factor instead of RootProduct's
  specified residue. This report uses the ordinary monic remainder method,
  not an unchecked import of the inverse-dependent improvement.
* [Harvey–Hittmeir, arXiv:2105.11105v1, introduction and Theorem 1.1](https://arxiv.org/html/2105.11105v1).
  The checked deterministic full-factorization comparison is
  O(N^(1/5)(log N)^(16/5)/(log log N)^(3/5)). The present result does not
  improve it. This is a matched deterministic comparison, not a comparison
  with heuristic GNFS or a comprehensive survey of later literature.

The original Lehman proof and the full cited polynomial-arithmetic textbook
were not reread in this round. The accepted H029 cover theorem is inherited,
not independently reproved here. The scalar cubic product identity,
denominator handling, certificate and obstruction above are written out so
that their exact scope can be assessed independently of the source summaries.

**Coordinator disposition after review:** reject this realization as a
sub-1/5 RootProduct construction and accept sections 2–5 within their stated
scope, with the three cost/notation clarifications above. No additional
constructive proof question or finite experiment is selected by this report.
Numerical testing was not needed for the proof. The proposer wrote only this
report and adjacent H030-block-* artifacts; the coordinator preserved the
original submission and recorded acceptance separately.
