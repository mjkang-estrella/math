# W008 four-list review: supply passes; the supplied computation stays quadratic

2026-10-08. Independent T3 child audit of the frozen W008 construction.
**Disposition: REVISED / ACCEPT AT THE SCOPES BELOW. Verified new complete
factoring complexity improvement: NONE.**

The pairwise-independence proof, useful-collision supply, loss allowance for
global zeros, and one-path recovery are correct. The N-only schedule works,
with an explicit success lower bound greater than 3/8. Balanced splitting and
a specified number of trials complete its cost proof. The conditional exponent
needs a sampling qualification: use max(1, alpha)/4, or assume alpha >= 1.

There is an actual ordinary-ring K^2 poly(log N + log K) control. The power-series
construction is legal after a paid denominator check. A monic evaluation-tree
finish supplies its scalar resultant without arbitrary polynomial-pivot
inversions. This finish explicitly materializes one pair list; the completely
division-free fallback materializes both. Neither is a subquadratic algorithm.
The independent-label filter and limited exact-scalar 4SUM reduction pass with
the qualifications below. No scalar-computation lower bound follows.

## 1. Scope, ownership, and evidence

The end-to-end promise is N=pq with distinct odd primes p<q. The program knows
N only. Sampling, arithmetic, indices, recovery, and repetition are charged.
Results here are mathematical algorithm/cost arguments, not an implementation,
Lean proof, measured speedup, or general all-composite factoring theorem.

Read in full: AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md,
docs/SPECIFICATION.md, the frozen current STATE, W008.md, W006-batch-review.md,
and W006-map-batch-disposition.md. The task registry was preserved as provenance;
no registry or task lifecycle was changed. The user-supplied brief agrees with
the frozen W008 proposal. The W007 D residual-dynamics task and closed W007
rational-family audits were not reopened or used as evidence.

All authored files are this report and W008-fourlist-review-prefixed artifacts
inside [the evidence directory](W008-fourlist-review-evidence/). No numerical
candidate, parameter sweep, solver, shared code, Lean, dependency, commit,
publication, or recursive delegation was performed. An exact rational
certificate check verifies only displayed proof constants. Shared project tests
were not rerun: there is no shared code change to validate.

The [input manifest](W008-fourlist-review-evidence/W008-fourlist-review-inputs.json)
records ten byte-identical snapshots and SHA-256 identities. STATE changed in
the parent during this review; the frozen version is the reviewed input, not
a claim about subsequent coordinator state. Delivery verification is recorded
in the prefixed manifest and verification files alongside the report evidence.

## 2. Exact distribution: pairwise independence is sufficient

Use independent coordinates a_i,b_j,c_k,d_l, including independent coordinates
when two realized residues happen to be equal. For distinct index tuples t,u,
their four-coordinate supports differ. Both supports have cardinality four,
so there is a coordinate used only by t and one used only by u. Restricting
the two linear forms to these two coordinates gives a diagonal 2-by-2 matrix
whose diagonal entries are +1 or -1. Its determinant is a unit over Z/NZ and
over every prime field, including characteristic two.

Conditioning on all other input coordinates therefore leaves (L_t,L_u)
uniform on (Z/NZ)^2. In particular they are independent. Equivalently, the
rank-two argument works separately at p and q, and the entire p-coordinate
array is independent of the q-coordinate array by CRT. Shared coordinates,
small fields, and repeated realized entries cause no exception. What would
break the proof is reusing the same random coordinates in different lists.

Let a=(q-1)/(pq), M_4=K^4, and Z count p-only zeros. Then, exactly,

    E Z = lambda = M_4 a,
    E Z^2 = M_4 a + M_4(M_4-1)a^2
          = lambda^2 + lambda(1-a),
    Pr(Z>0) >= (E Z)^2/E Z^2 = lambda/(lambda+1-a).

This last step is Cauchy-Schwarz, not an iid or Poisson approximation. For
example, swapping two A and two B indices gives the four-term identity
L_ij + L_i'j' = L_ij' + L_i'j with C,D fixed; higher independence must not be
asserted. K=1 is covered by the same Bernoulli calculation.

Every individual L_t is uniform modulo N. If G means that some cross-pair
tuple is globally zero, then

    Pr(G) <= K^4/N.

There is no requirement that G be independent of Z>0. Ordinary repeated
entries or repeated sums within one side are not automatically global zeros
of a cross-pair tuple. No extra loss for those repetitions is needed.

## 3. Scalar identity and the actual bounded recovery

For nonempty list lengths m_A,m_B,m_C,m_D, set d=m_A m_B and e=m_C m_D.
With the usual convention Res(f,g)=product_{f(x)=0} g(x) for monic f,

    S_AB(T) = product_(i,j)(T-a_i-b_j),
    S_CD(T) = product_(k,l)(T-c_k-d_l),
    R = Res(S_AB,S_CD) = product_(i,j,k,l)(a_i+b_j-c_k-d_l).

These are identities over the integers and hence over Z/NZ. Multiplicities
are preserved. The parent's first nested resultant has exactly the stated
monic composed-sum value. Alternative resultant conventions only change a
known sign. An empty input list gives R=1 and no collision.

Specify the descent as follows: at a full-gcd node, select a list with more
than one entry and divide its index interval into floor/ceiling halves. Its
two nonempty child products multiply to the parent product. Evaluate only
the first child and compute its gcd with N. Return a proper gcd; descend
there if its gcd is N; if its gcd is 1, descend into the other child, whose
gcd must be N. A singleton tuple with full gcd terminates this trial as a
failure. There is no exploration of all siblings.

The invariant is that the current product has gcd N. A unit child cannot
carry any prime divisibility of its parent, so the other child retains full
gcd. On G's complement every singleton L_t is nonzero modulo N and therefore
cannot have full gcd. Thus the descent must return a proper factor before
reaching such a leaf. A useful p-only tuple makes the root gcd either p or
N, so

    Pr(actual factor) >= Pr(Z>0) - Pr(G).                 (1)

The success event may be larger: q-only tuples and some trials containing a
global zero can also succeed. Equation (1) does not claim deterministic
completeness in the presence of a global zero. Finding a full-gcd leaf is
not evidence that no useful tuple exists elsewhere.

Balanced splitting is a necessary specification for the claimed invocation
count. Along one path the total depth is at most

    sum_E ceil(log2 m_E) <= 4 ceil(log2 K).

There is one root call and at most one additional scalar call per edge, plus
the same order of gcds and charged list/index access. Arbitrarily unbalanced
partitions would not give this bound. All scalar calls must support unequal
sublists with their actual multiplicities, not padding by extra roots.

The scalar clean-leaf argument itself works more broadly for composite N;
the distribution and end-to-end estimates being accepted here still have the
stated squarefree semiprime promise. In particular, do not import W006's
quadratic-algebra prime-power counterexample as a counterexample to this
different scalar leaf identity.

## 4. Safe constants and an N-only expected-cost schedule

First test the fixed primes through 127 and return a proper factor when found.
This is a constant number of arithmetic operations, or poly(log N) bit work,
not literally constant bit cost. Now p,q>=131.

Let K_* be the first power of two with K_*^4>=p and K_max the first power of
two with K_max^4>=ceil(sqrt(N)). Both exist, K_*<=K_max, and

    K_*^4 < 16p,       K_max^4 < 16 sqrt(N).

The second strict inequality survives the ceiling: the integer
(K_max/2)^4 is smaller than ceil(sqrt(N)), hence smaller than sqrt(N).
There is no missing +1 error in the submitted inequality.

For every scheduled K in [K_*,K_max],

    lambda >= 1-1/q >= 130/131,
    Pr(Z>0) >= lambda/(lambda+1) >= 130/261,
    Pr(G) < 16/sqrt(N) <= 16/p <= 16/131.

Consequently (1) is strictly greater than

    130/261 - 16/131 = 12854/34191
                    = 3/8 + 259/273528 > 3/8 > 1/3.      (2)

These exact comparisons are separately checked in
[the constant certificate](W008-fourlist-review-evidence/W008-fourlist-review-constants.json).
The first-threshold 16/q estimate is also valid; (2) is the common bound for
the entire interval through the cap.

For a per-trial expected envelope C K^beta P(log N), beta>0 fixed, do r fresh
independent trials at K=1,2,4,...,K_max and then repeat r-trial blocks at
K_max. Choose the fixed integer r so that

    eta = (2/3)^r,       eta 2^beta < 1.                  (3)

Four trials per stage suffice when beta<=2, since 4(2/3)^4=64/81<1. A fixed
r depending on the fixed algorithm exponent suffices for every fixed beta;
one universal r for arbitrarily large exponents is not being asserted.

Work before K_* is a geometric sum O(K_*^beta P(log N)). Reaching the m-th
stage after K_* has probability at most eta^m, so its expected contribution
is at most C' K_*^beta (eta 2^beta)^m P(log N). The repeated cap contributes
the analogous last-stage term times 1/(1-eta). This proves the total envelope
O(p^(beta/4) P(log N)), including early failures and all cap repetitions.
An integer square root and comparisons of fourth powers implement the cap
without p. Throughout, log K=O(log N).

Generate each uniform residue by rejecting n-bit words >=N, where n is
bitlength(N). Acceptance is >1/2, so 4K independent residues cost expected
O(K n) random-bit and ordinary bit work. This is an exact uniform sampler
with an unbounded possible rejection count, consistent with the expected
Las Vegas statement. Future trial randomness is independent of the event
of reaching a stage; variable sampling time does not invalidate the cost sum.
No bounded worst-case random-tape theorem is asserted.

## 5. Primary source: what was actually read and accepted

The downloaded author copy is a 35-page preprint dated 27 June 2005 of the
paper cited as BFSS (2006). Text pages 1-16 were read; pages 4,8,9,12,13 were
also rendered and inspected. Theorem 1(1) assumes a field, monic degrees m,n,
D=mn, and characteristic zero or >D; its composed-sum cost is O(M(D)) field
operations. Lemma 1/Proposition 1 treat power sums; Proposition 2(1), Lemma 2
and Corollary 1 reconstruct coefficients; Lemma 4/section 3.2 give the
exponential-generating-series convolution. Small-characteristic clauses have
multiplicity conditions; they are not an unrestricted composite-ring theorem.
[Primary author copy](https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf).

No later diamond-product application, arbitrary-composite fast-resultant
implementation, or scalar-only subquadratic theorem was imported. The PDF
SHA-256 is

    19db312c68f997949db342a050df568a009a340dd5026e4584e2c4fa59fcc375

The source download, extracted text and inspected page PNGs are retained.
Browser PDF screenshots returned unsupported-content errors; local Poppler
rendering supplied the inspected images. The ring construction below is an
explicit audit derivation from the task's identity, rather than replacing
the source's field assumption by assertion.

## 6. A fully charged ordinary-ring quadratic control

Write R_N=Z/NZ and use a different symbol H(z) for power series to avoid
confusing the coefficient ring with the scalar resultant. For a node let
D_0=max(m_A m_B,m_C m_D)<=K^2; the following construction may use precision
D_0+1. For readability, d denotes the degree of the particular composed sum
being constructed.

### 6.1 Denominators: legal chart, early factor, or an exact fallback

Compute f_j=j! mod N for 0<=j<=D_0 and g=gcd(f_D0,N). This takes
O(D_0 poly(log N+log D_0)) bit work and stores only reduced residues.

* If g=1, every integer 1,...,D_0 is a unit. One extended gcd inverts f_D0;
  the reverse recurrence invfact[j-1]=j invfact[j] obtains all inverse
  factorials. Then j^(-1)=(j-1)! invfact[j]. No untested division remains.
* If 1<g<N, the factoring detector may immediately return g. This is a
  verified factor, not an exact scalar-R output.
* If g=N on the semiprime promise, a single scan of gcd(j,N), j=1,...,D_0,
  returns a proper factor by j=p: p<=D_0 and p<N. No p-dependent loop bound
  is used. This costs at most the already allowed D_0 scale. In particular,
  encountering a full factorial gcd need not cause a failed chart.
* If an exact scalar value rather than an early factor is required, use the
  division-free pair-product/evaluation fallback below whenever g!=1. It
  works even for prime moduli or outside the semiprime promise.

Within the capped schedule after small-prime removal,
D_0<=K_max^2<4 N^(1/4)<sqrt(N)<q, so the factorial's full gcd cannot actually
occur. At K_*, D_0<4 sqrt(p)<p, so all these denominators are units. The
general handling above still matters for the advertised arbitrary-list
control. Permitting unspecified failed charts or pivot failures would not
preserve the probability theorem for an otherwise hypothetical fast detector.

### 6.2 Constructing a composed sum, with exact truncation

Build Q_A(z)=product_i(1-a_i z), using a balanced polynomial product tree,
and similarly Q_B. Its constant term is exactly one, even with repeated or
zero roots. For m_A=|A|,

    P_A(z) = sum_(r=0)^d s_r(A) z^r
           = m_A - z Q_A'(z)/Q_A(z) mod z^(d+1).          (4)

The reciprocal needed here is computed by Newton doubling

    V_new = V(2-Q_A V) mod z^h,
    1-Q_A V_new = (1-Q_A V)^2 mod z^h,

starting with V=1 and h=min(2s,d+1). This uses no inverse of 2 or arbitrary
coefficient. Retain s_0 through s_d; treating the known s_0 as one of only
d stored terms would omit the last needed power sum.

On the unit-denominator chart, form

    E_A(z)=sum_(r=0)^d s_r(A) z^r/r!,
    E_B(z)=sum_(r=0)^d s_r(B) z^r/r!,
    u_r=r! [z^r](E_A E_B),       0<=r<=d.

The binomial theorem, applied to each indexed pair, proves
u_r=sum_(i,j)(a_i+b_j)^r. Next set

    H(z)=-sum_(r=1)^d u_r z^r/r,
    Q_AB(z)=exp(H(z)) mod z^(d+1),
    S_AB(T)=T^d Q_AB(1/T).                                (5)

For an explicit fast exponential start E=1 mod z. If E=exp(H) mod z^s,
put h=min(2s,d+1), compute log(E)=integral(E'/E) mod z^h using the same
unit-constant reciprocal, and replace

    E <- E(1+H-log(E)) mod z^h.

The error H-log(E) has valuation at least s, so its square is zero at this
precision; this proves the doubled precision. Integration always has zero
constant and divides coefficient z^(r-1) by r. Every precision is clipped
at d+1, so no denominator greater than d is silently introduced by a final
doubling step. These identities are valid in R_N once 1,...,d are units.
They preserve multiplicities and require no squarefreeness assumption.

The same construction gives S_CD if desired. Using full-precision inverses
at successive doublings already suffices for a conservative
O(M_R(d) log(2d)) bound. No quadratic coefficient-by-coefficient Newton
recurrence or direct summation of all d binomial convolutions is allowed
under that bound; the EGF convolution is one fast polynomial multiplication.

### 6.3 Exact scalar finish that removes the pivot gap

The paper's composed-sum theorem does not itself certify a general fast
Euclidean resultant over R_N. For a proposed coefficient inverse v, a proper
gcd(v,N) is useful, whereas gcd(v,N)=N means v=0 in R_N and supplies no
factor. Such a zero must lead to correct zero/degree-drop handling or a
proved fallback, not a claimed successful extraction. A black-box field
routine with unhandled failed pivots is not accepted.

Here is a complete replacement at the required quadratic scale:

1. Obtain S_AB from (4)-(5). Explicitly form y_kl=c_k+d_l for the e pairs.
2. Build a balanced monic query tree with leaves T-y_kl. Use a remainder
   tree to evaluate S_AB at every y_kl, retaining repetitions.
3. Multiply these e values modulo N and return

       R=(-1)^(de) product_(k,l) S_AB(y_kl).              (6)

The sign follows by reversing each of the de differences; (6) is an exact
scalar identity. Building S_CD in addition is harmless but unnecessary.

Division by a monic query-tree polynomial is reversal followed by inversion
of a series with constant term 1, then quotient recovery and subtraction.
Thus all divisions in this finish are monic divisions. No node differences,
interpolation denominators, or remainder leading coefficients are inverted.
Repeated roots, zero evaluations, full gcds, and nonunit values are legitimate
data, not arithmetic failures. Full gcds in (6) are handled by section 3.

For the exact fallback in section 6.1, explicitly form all x_ij=a_i+b_j and
construct S_AB=product(T-x_ij) by a monic product tree, then apply these same
three steps. This gives an unconditional exact scalar routine over Z/NZ in
the quadratic envelope; the power-series route is an alternative realization
on its legal chart. One could instead use W006's scalar deduplication and
derivative detector on the two explicit pair lists; that returns a factor
under its contract and is not generally an evaluator of the original R.

### 6.4 Bit work and storage, not just ring-operation counts

For coefficient arrays of length at most t, canonical entries in [0,N),
choose radix 2^b with b=2n+ceil(log2(t+1))+2. Every coefficient of their
nonnegative integer convolution is <2^b. Pack, multiply integers, unpack,
and reduce coefficients modulo N. This gives a polynomial multiplication
envelope

    M_R(t)=O(M_Z(t(n+log(t+1))) + t poly(n+log(t+1))),

where fast integer multiplication is used. No roots of unity or field
structure in R_N are needed. Signed operations take place after unpacking.
Stored coefficients are reduced at each stage, so the huge integer lift
of the K^4-term product is never constructed.

The input product trees, fast series operations, query trees, remainder
trees, and products in (6) take K^2 poly(n+log K) bit work in total. The
denominator checks, gcds, bit sampling, index records, and sequential tree
traffic fit this envelope. A fully stored implementation uses at most
K^2 poly(n+log K) working bits as well. Recomputing at each of the
O(log K) recovery calls adds only a logarithmic factor.

At K_* this is expected sqrt(p) poly(log N) splitting under section 4's
schedule, the accepted known-scale control. The Newton arrays and dense
composed-sum polynomial each contain Theta(K^2) slots. That is a cost of
these specified implementations, not a lower bound on producing one scalar.

## 7. Independent auxiliary labels: exact count and precise closure

Assume gcd(M,N)=1 and log M is paid. Sampling uniformly modulo MN makes
the full auxiliary-label array independent of the entire payload array
modulo N. Conditional on any realized labels, the payloads remain the
original four independent uniform lists. This is stronger than independence
of a single hidden-prime test and supplies the needed conditioning argument.

Let U count AB pairs whose label sum is zero and V count CD pairs whose
label sum is zero. Then U and V are independent, and

    E U=E V=L=K^2/M,
    E(number of retained p-only tuples)=a E(UV)=a L^2.    (7)

Markov's inequality gives Pr(any retained p-only tuple)<=a L^2. For factor
success by either orientation, replace a by

    rho=1/p+1/q-2/N <= 2/p.

Consequently any fixed positive success probability using only these retained
cross pairs requires L=Omega(sqrt(p)). Expected traffic from writing all
retained pairs is 2L, already Omega(sqrt(p)). Sorting input labels and
enumerating matching buckets can avoid inspecting all K^2 potential pairs;
it cannot avoid writing the U+V pairs if the selected algorithm explicitly
materializes them. Charge O(K poly(log K+log M+log N)) input/bucket work in
addition to retained output traffic. No free array of M buckets is needed.

Equation (7) alone is a necessary-size argument, not a sufficiency theorem.
As an additional exact check, distinct AB pair-label sums are pairwise
independent even for composite M: the same exclusive-coordinate argument
uses determinant +/-1. Put b=1-1/M. Then

    E U^2=E V^2=L^2+Lb,
    E Z_filtered^2=a^2(L^2+Lb)^2+a(1-a)L^2,
    Pr(Z_filtered>0)
      >= 1 / ((1+b/L)^2+(1-a)/(a L^2)).                  (8)

The second identity follows by conditioning on the labels and using the
pairwise independence of all retained payload tests. It neither makes U,V
deterministic nor assumes independent retained tuples. Global-zero losses
still have to be subtracted for one-path extraction; their expected count
in the retained collection is L^2/N. This is not a faster factoring control.

For the matched-bucket variant keeping every pair and comparing equal pair
labels, each original tuple survives with probability 1/M. Its expected
p-only count is a K^4/M, and it writes 2K^2 pair records. Constant success
by either useful orientation needs K^2=Omega(sqrt(Mp)), which gives no
exponent gain for M>=1.

These conclusions concern the specified fixed independent-label experiments
and explicit retained-pair traffic. They do not exclude implicit consumers,
arithmetic-correlated filters, adaptive methods with different accounting,
or successes from other factor tests. Ordinary low bits of a representative
sampled only modulo N have not been proved independent of its CRT payload.
They are not the experiment analyzed here.

## 8. Conditional consequence and the exact-scalar reduction

Suppose a uniform routine, on every list/sublists instance of maximum size
K, computes the exact R modulo N in K^alpha poly(log N+log K) bit work.
Together with section 3 and paid acquisition, the per-trial exponent is

    beta=max(1,alpha),
    expected splitting work = p^(beta/4) poly(log N).    (9)

Thus the parent's p^(alpha/4) conclusion is correct for 1<=alpha<2.
Stating only alpha<2 omits the O(K) input-generation cost when alpha<1.
The condition is hypothetical; no such subquadratic evaluator is supplied.
Equation (9) improves this collision control if beta<2, not the cited
general subexponential factoring algorithms merely by its existence.

Worst-case support for arbitrary sublists is consequential. Nodes chosen
after observing full gcds are not fresh iid lists. A routine correct and
fast only in expectation under the initial random-list distribution needs
a separate correctness and cost theorem on the selected path, or an actual
new recovery procedure. Even an exact but distribution-average-time routine
does not automatically compose with adaptive selection. Bounded-error
routines additionally need failure probabilities charged across calls;
verifying an output factor does not certify an erroneous gcd-one decision.

For four integer lists with each entry of magnitude <=B, B>=1, take a prime
ell>4B. Every integer L_t has |L_t|<=4B, hence

    L_t=0 in Z iff L_t=0 mod ell,
    R=0 mod ell iff some L_t=0 in Z.

The last implication uses that F_ell is a field; for a composite modulus a
product can vanish without any zero term. Magnitude 4B itself is not excluded
by using ell=4B, so the strict inequality matters. Four-list equality means
A+B=C+D; four-sum-zero is obtained by negating the last two lists.

This is a correct exact decision reduction for an arbitrary-list scalar
routine that also accepts prime moduli. To attach a bit-complexity claim,
charge reading the O(K log(B+1))-bit input and obtaining the prime as well.
A supplied suitable prime gives the immediate cost transfer. Merely writing
"choose a prime" does not specify a deterministic poly(log B) prime search;
that stronger fine-grained reduction is not established here. No 4SUM
conjecture, novelty claim, or lower bound is imported.

A proper-factor-only routine has no useful proper factor to return on a
prime modulus. A routine promised only squarefree semiprimes, or only random
lists, likewise does not satisfy this reduction's oracle contract. The
distinction from (9), which needs a semiprime evaluator, must be retained.

## 9. Constructive challenge: an explicit alternative representation and its gate

No actual subquadratic replacement was found. The following symbolic check
locates a specific obstruction to a natural compact representation and a
different, concrete next calculation; it is not a scalar lower bound.

For equal nonempty list sizes K, form the free rank-K^2 ordinary algebra

    Q=R_N[X,Y]/(F_C(X),F_D(Y)),
    H_b=F_A(X+Y-b) in Q for b in B.

The determinant norm of product_b H_b is (-1)^(K^4) R: its evaluations
at (c_k,d_l) give products of c_k+d_l-a_i-b_j, with K^4 reversed
differences. This identity includes repeated roots, using the monic
quotient's multiplication determinant, not a separability assumption.
It is another representation of the same required computation.

Even one H_b generally cannot be carried by o(K) separated terms
sum_h u_h(X)v_h(Y). In fact this is a uniform symbolic obstruction on the
unit chart, not a random-input experiment. Write

    F_A(T-b)=sum_(t=0)^K h_t T^t,       h_K=1.

For 1<=r,s<=K-1 the mixed coefficient matrix of H_b in the monomial basis is

    C_rs=binom(r+s,r) h_(r+s) if r+s<=K, else 0.

Reducing X^K and Y^K changes only the pure-variable row or column, so this
mixed block is unaffected by F_C,F_D. Reversing its columns makes it
triangular, with diagonal binom(K,r), r=1,...,K-1. Therefore

    det(C)=(-1)^((K-1)(K-2)/2) product_(r=1)^(K-1) binom(K,r).

At every prime ell>K this is nonzero. Its separation rank is at least K-1,
since each separated term contributes a rank-one coefficient matrix.
This closes an o(K)-separation-rank state for this particular quotient
representation. It does not bound an implicitly represented matrix, its norm,
or all random-list algorithms.

There is a more specific representation still worth checking symbolically.
Before pure-variable reductions, factorial scaling of the coefficient array
gives Ctilde_rs=(r+s)! h_(r+s), a Hankel matrix (constant on anti-diagonals).
Pure-variable reductions change only its boundary row and column. Thus full
matrix rank alone does not rule out short descriptions via the difference
J Ctilde - Ctilde J^T, where J shifts coordinates down by one; an unreduced
Hankel matrix has only boundary entries in this difference.

The next concrete computation is to derive the update of those boundary/
displacement generators when multiplying two residues modulo F_C(X),F_D(Y),
then determine whether the entire product and its determinant norm can be
computed from those generators in o(K^2) total bit work. The update must
include reductions in both variables, arbitrary sublists, all nonunits,
and the K factors; a short description of a single H_b is insufficient.
If the update requires a dense K-by-K state or K successive quadratic
products, it fails the intended saving immediately. No cheap norm-update
algorithm or favorable generator-growth law is asserted here. This is a
defined symbolic gate for the parent's constructive work, not permission
for a numerical screen or a renamed norm oracle.

## 10. Exact handoff dispositions

* **ACCEPT:** pairwise independence, the two moment identities, union-bound
  global-zero loss, and one-path extraction on their stated events.
* **ACCEPT WITH SPECIFICATION:** balanced splitting, the N-only cap, and
  expected-cost summation; four trials per stage suffice for exponent <=2.
  The common success lower bound is >3/8 after fixed small-prime tests.
* **REPAIR SUPPLIED:** denominator handling and a monic multipoint scalar
  finish establish the actual K^2 polylog control. The unchecked generic
  field-resultant implementation is not needed or accepted on faith.
* **ACCEPT AT LIMITED SCOPE:** independent-label counts and explicit-traffic
  obstruction; exact-scalar integer four-list equality reduction with its
  prime-modulus/input-domain and prime-acquisition qualifications.
* **CORRECT:** conditional exponent is max(1,alpha)/4 unless alpha>=1.
  A random-input-only routine also needs a selected-sublists recovery theorem.
* **OPEN:** scalar computation below K^2. The supplied dense Newton and
  explicit filtering algorithms do not achieve it; no output-size argument
  proves it impossible. The quotient displacement-update calculation above
  is the next specific symbolic gate, with no experiment selected.
