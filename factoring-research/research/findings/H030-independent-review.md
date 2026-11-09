# H030 — Independent review of the exact polynomial-block attempt

2026-10-08. **ACCEPT the scoped mathematical core and its negative disposition;
REJECT this realization as a sub-1/5 RootProduct construction.**
Verified improvement in COMPLETE classical factoring complexity: **NONE**.

The finite cubic constructor and interval-product procedure are correct on the
unchanged all-M/all-d/all-interval interface. The submitted block lemma, including
its constant 8 and degree-dependent term 4D-6, is valid. The exception inequality
L <= 4D+9e+8 is also valid. Mandatory explicit cubic records give the claimed
Omega(M^(1/3)) construction cost. For growing degrees the cost conclusion needs
the stated, actual dense-output premise: a degree bound alone is not paid output.
No algebraic repair to these inequalities is required.

The conservative complete upper bound is M^(1/3) poly(log M), with retained and
temporary space accounted for below. This is a mathematical finite specification,
not an executed solver, timing result, Lean theorem, or machine refinement.
Acceptance here is an independent review decision for the coordinator; no shared
acceptance status, checkpoint, registry, or original finding has been edited.

## 1. Frozen target, ownership, and decisions

The complete 482-line [submitted draft](H030-submitted-draft.md), complete
56-line [coordinator intake](H030-intake.md), original
[brief](../hypotheses/H030.md), and complete proposer source notes were read.
Their identities are:

- Submitted draft and unchanged proposer report, both:
  `f66360ee379188f50b83fb1f11fff43536aa3c2beb18c6a05118d4986b864581`.
- Coordinator intake:
  `7cfe2a8d1c53a8b4c2946de9a7082c5cf850bb3bb29b6716de3abd6f3d124777`.
- H030 hypothesis:
  `51a0ffdb7ef8c1f1a80d3d72719e26b9dbbb14c9dfc6f20b946a309ae43c23be`.

All 12 proposer frozen-input entries and all 21 delivery entries matched before
review. [H030-review-inputs.sha256](H030-review-inputs.sha256) identifies 36 new,
byte-for-byte review snapshots, including the originals above, the governing
project documents, accepted dependencies, and all H030-block-* evidence and
manifests. [H030-review-originals.sha256](H030-review-originals.sha256) records
their original paths and start-of-review identities. Hashes establish identity,
not proof. Reading scope and primary-source identities are in
[H030-review-source-notes.md](H030-review-source-notes.md).

The start-of-review 580-line STATE was read. Its description of H030 as live is stale;
the task handoff says the constructive task completed and governs this review.
H031's separate files, task status, and draft were not consulted. No delegation,
finite experiment, sweep, numerical replay, benchmark, solver implementation,
package, Lean edit, commit, publication, scheduler, or outside-project write was
performed. Only this report and adjacent H030-review-* artifacts are owned here.
Final original-input comparison found drift only in the shared STATE, which
this reviewer never wrote. The exact read version is frozen; all 36 frozen
copies and all original H030 submission/intake/proposer-manifest entries still
match. The verification artifact records both STATE identities rather than
silently replacing its historical snapshot.

The major decisions are as follows; the following sections supply the independent
arguments rather than treating the intake's provisional checks as acceptance.

1. **Interface and H029/H004 dependency — ACCEPT.** Every M >= 4096, arbitrary
   2 <= d <= M, and every valid inclusive leaf interval remains required.
   Coverage, small-factor preprocessing, and factor recovery are inherited.
2. **Newton interpolation, Bernstein certificates, and termination — ACCEPT.**
   Strict/weak tests have the correct orientation; rejected true blocks merely
   incur paid subdivision. Short records provide unconditional termination.
3. **Denominator clearing and modular products — ACCEPT.** Integer division
   precedes reduction. Monic remainder operations work with zero divisors and
   coincident evaluation residues. No arbitrary modular inverse is required.
4. **Partial intervals, complete upper bound, and memory — ACCEPT.** Failed t
   tests, boundary slices, all records, modulus preparation, and tree traffic are
   charged. Section 5 makes the sequential schedule and weighted short-row count
   explicit; neither changes the submitted asymptotic bounds.
5. **J, curvature, second differences, and exact polynomial block lemma — ACCEPT.**
   The precise endpoints, small lengths, and all degree cases pass.
6. **Mandatory cubic records and their construction lower bound — ACCEPT.**
   This is a lower bound on the specified record-writing constructor, not one
   inferred from its upper runtime estimate or from coefficient bit upper bounds.
7. **Growing degrees with explicit exceptions — ACCEPT with its dense-list
   scope made explicit.** Apply the bound with actual degree, or with the
   genuinely allocated dense length. Section 8 gives the precise cost statement;
   shared arrays, circuits, and modular-only generation are outside it.
8. **Primary attribution and historical comparison — ACCEPT.** The specific
   primary passages support the limited attributions. No current-record survey
   or exhaustive novelty claim is made.
9. **Sub-1/5 success or a general impossibility result — REJECT.** The former
   fails for this mandatory representation; the latter does not follow.

There is no major claim requiring mathematical revision. Section 10 gives exact
wording clarifications the coordinator may adopt without altering the originals.
The explicit reversal formula, sequential scan schedule, overlap checks, and
U/72 slot-budget constant below are reviewer proof completions, restricted to
the stated algorithms and representations. They assert no additional factoring
or general product lower bound.

## 2. The interface really is unchanged

Write n = bitlength(M), K = ceil(M^(1/3)), and retain the frozen bands, inclusive
t range 0,...,T_j, and order j, k, t, minus/plus. Let w_j = T_j+1,
m_j = h_j-l_j+1, and V = sum_j m_j w_j. There are 2V leaves. In this review a
"k row" contains w_j pairs; an unqualified scalar pair is indexed by (k,t).

All ordinary roots are computed over the integers before reduction modulo d.
Their arguments are nonnegative: c(k) = ceil(sqrt(4Mk)) and t >= 0 give
(c(k)+t)^2 >= 4Mk. Since 4Mk > 0, the inner y is smaller than x=c(k)+t, so both
leaves are positive. If y=0 their equal values are still two occurrences in
the ordered product. No squarefree, semiprime, primality, or divisor promise
on d is used to define or compute a product.

I read the corrected H029 report and its disposition, the relevant independent
review sections, and H004's reduction and cost arguments. Their accepted
root-gcd initialization preserves d dividing both the input and its assigned
integer product. Both root queries, visited-leaf work, and restoration of all
multiplicities from the original input remain charged. H029's positive small
leaves make its *visited* Leaf cheap after preprocessing. That does not weaken
RootProduct's stronger total domain. H030 inherits these facts and contributes
no new coverage/recovery reduction.

The scalar identity A_- A_+ = 4kM + e, where e=x^2-4kM-y^2, remains an integer
identity. Replacing the product by e requires d dividing 4kM; H030 never makes
that replacement. Its output is the specified residue, not an incidental
factor, a square detector, or a zero with an unprovided recovery routine.

## 3. Exact certificate and constructor

For L >= 4 all four samples a,...,a+3 belong to the proposed block. For any four
integer samples p_0,...,p_3, the forward differences are integers and

    P(u) = sum_(r=0)^3 Delta^r p_0 * binom(u,r)

interpolates them and is integer-valued at every nonnegative integer u. The
denominators of its power-basis coefficients divide 6. This supplies the needed
integrality separately from any analytic estimate; interpolation alone does
not prove equality at later indices.

To re-derive the Bernstein conversion, for 0 <= i <= 6 use

    sum_(h=i)^6 [binom(h,i)/binom(6,i)] binom(6,h)
                 v^h (1-v)^(6-h)
      = v^i sum_(j=0)^(6-i) binom(6-i,j) v^j (1-v)^(6-i-j)
      = v^i.

Applying this to each coefficient of g((L-1)v) proves the submitted expression
for b_h. The degree-six basis weights are nonnegative and sum to one, including
v=0 and v=1. Thus all b_h >= 0 prove the weak inequality, and all b_h > 0 prove
the strict inequality on the *closed* real interval. Degree-zero and lower-degree
polynomials are padded by zero power coefficients before the conversion.

For the outer root, the tests give C >= 1 and

    (C-1)^2 < R <= C^2,       R=4M(a+u)>0.

Both quantities being squared are nonnegative; taking square roots is therefore
legitimate. At integer u this proves C-1 < sqrt(R) <= C, hence C=ceil(sqrt(R)).
If R is a perfect square, equality on the right is permitted and gives precisely
that integer. Weakening the left strict inequality would admit an incorrect
ceiling one larger at a square; the submission does not weaken it.

For the inner root the tests give Y >= 0 and

    Y^2 <= Z < (Y+1)^2,       Z=(C+t)^2-R.

In particular Z >= 0, and integer-valued Y equals floor(sqrt(Z)). Equality at
Z=Y^2, including Z=0 and Y=0, is permitted. Equality at Z=(Y+1)^2 is correctly
excluded. A vanishing weak-certificate coefficient is harmless; a vanishing
strict-certificate coefficient causes rejection even when some weaker method
could prove the integer-point identity. Such rejection is inefficiency, not
an incorrect answer. Repeated roots or interior zeros can similarly make the
sufficient real test fail; no completeness of this certificate is asserted.

If any test fails, the two children have positive lengths floor(L/2) and
ceil(L/2), each smaller than L. At L <= 3 the actual roots are evaluated without
certification. There is no length-zero recursive child. The resulting terminal
blocks partition every band, whether or not any long block ever passes. A failure
at the last tested t discards all previously accumulated tentative Y_t data;
charging every t at every node includes that event. This proves a finite, exact
constructor independently of favorable approximation errors or exception density.

All sampled roots and their arguments have O(n) bits: k=O(M^(1/3)),
t=O(M^(1/6)+1), and x=O(M^(2/3)). Fixed-order differences, degree-six products,
and substitution by L-1=O(K) only multiply bit lengths by constants. Bernstein
conversion uses fixed rational denominators, which can be cleared positively
before sign comparison. Exact binary-search roots use O(n) comparisons and
O(n^2) schoolbook square/comparison work per comparison, hence O(n^3) time and
O(n) scalar scratch bits. These are symbolic bounds, not executed checks.

## 4. Integer coefficients and the all-composite-ring product

For either interpolant P, set H=6P in Z[u]. Expanding a term
H_j(6z+r)^j shows that its coefficient of z^i for i >= 1 contains 6^i.
Its constant term is H(r)=6P(r), also divisible by 6 because r=0,...,5 is an
integer. Therefore H(6z+r)/6 belongs to Z[z]. This proves the denominator
clearing, including residue classes outside the four initial sample positions.
The constant term's divisibility follows from integer-valued Newton form,
not from knowing an actual rounded root at r outside the accepted block.

The divisions by 6 are exact integer divisions. Reducing beforehand would be
invalid for moduli with a factor 2 or 3. The procedure does not do that.
Each resulting F=C(6z+r)+t +/- Y_t(6z+r) is an integer polynomial of degree at
most three, even if its degree later drops modulo d.

For a clipped u interval [u_0,u_1] subset [0,L-1], the exact z bounds are

    ceil((u_0-r)/6) <= z <= floor((u_1-r)/6).

Every u occurs in one and only one class. Empty classes are omitted. The floor
and ceiling bounds use mathematical signed division, including negative
numerators. Reordering factors is permitted in Z/dZ; it does not remove
multiplicity or require any prefix-product inverse.

For s>0 consecutive z values, h=ceil(sqrt(s)) satisfies 1 <= h <= s, and
q=floor(s/h) satisfies 1 <= q <= h. The q complete batches cover offsets
0,...,qh-1. The tail qh,...,s-1 has length s-qh<h. The identity

    H(z_0+jh) = product_(i=0)^(h-1) F(z_0+jh+i)

then includes each required factor exactly once. For s=1 it reduces to its
single value; s=0 returns 1. Zero or constant F, zero leading coefficients,
and repeated factors do not invalidate the identity.

Here is the division argument in more detail. Let G be a monic degree-r
divisor and A have degree at most m, with m >= r. Then
G^*(X)=X^r G(X^(-1)) has constant coefficient 1. Starting with its inverse
mod X equal to 1, if E=1-G^*B vanishes modulo X^ell, put

    B_new = B(2-G^*B) mod X^(2ell).

Before truncation, 1-G^*B(2-G^*B)=E^2. Consequently
1-G^*B_new=0 modulo X^(2ell), proving doubled precision in any commutative
ring, including characteristic two. It contains no division by 2. The reversal
of the quotient is

    rev_(m-r)(Q) = rev_m(A) * (G^*)^(-1) mod X^(m-r+1).

Reverse it back and compute A-GQ. This gives the unique remainder of degree
less than r; if m<r, A is already the remainder. Padding A to a known degree
bound also works. All divisors in the evaluation tree are products of X-a_i
and are monic. Their factors need not be coprime: reduction modulo a parent
followed by reduction modulo a child is legitimate because the child divides
the parent. At X-a_i the remainder is evaluation. Repeated a_i modulo d
cause repeated, correct outputs, not singular interpolation.

For multiplication, represent residue coefficients in [0,d). For two polynomials
of degree at most S, every integer convolution coefficient is at most
(S+1)(d-1)^2. Choosing 2^b strictly larger than this avoids all carries between
base-2^b slots. Each packed operand has (S+1)b bits and the product at most
(2S+2)b bits, hence O((S+1)(log d+log(S+1))) bits. Unpack, reduce each coefficient,
and continue. Signed ring differences are normalized before the next packing.
No assumption S=O(d) is needed, in particular when d=2.

A fixed quasi-linear integer multiplication/division algorithm gives the stated
soft-O(S(n+log(S+1))) arithmetic bound for S>=1. At each balanced tree level
the total degree and record count are O(h); root reduction, including
deg(H)<=3h versus q evaluation points, also has O(h) degree budget. Sequential
level construction/remainder passes and all coefficient reductions add only
logarithmic tree factors. Scratch including stored tree levels is
soft-O(h(n+log(h+1))) bits. Degree-three translations cost O(h) ring operations
plus their O(n)-bit index arithmetic. Thus the per-F claim
soft-O(sqrt(s)n), with polynomial scalar/index work included in the final
poly(n) envelope, is valid.

This uses neither fast interpolation with inverted differences nor a
factor-return alternative to the residue. The exact output is available for
every permitted modulus, even a composite nondivisor of M.

## 5. Complete ledger, partial intervals, and sequential memory

The accepted padding bound can also be checked directly for its use here:

    w_j <= 3 + sqrt(M)/(4(K+1)sqrt(l_j)),
    sum_j m_j/sqrt(l_j) <= (2+sqrt(2))sqrt(K),
    K <= V <= 3K + ((2+sqrt(2))/4)sqrt(M/K) = O(K).

The truncated final band and a singleton final band satisfy m_j <= l_j, so
neither is an exception. Computing widths by integer comparisons and all
prefix counts costs O(n^4), retaining O(n^2) bits. The number of bands and
the bit lengths of all leaf indices are O(n).

A binary subdivision tree for m_j integer positions has at most m_j leaves
and at most 2m_j-1 total nodes. Charge O(w_j n^3) at each node, including
outer failures and all discarded t tests. This proves

    C_P <= O(n^4 + V n^3).

Terminal records contain O(w_j) words for a cubic, or at most a constant times
L w_j words for L<=3. Summed over disjoint terminal intervals this is O(V)
words of O(n) bits, plus the small descriptor. A depth-first construction
appends accepted records in order. Before descending after rejection, it
discards the current O(w_j n)-bit candidate array, so candidate arrays do not
accumulate down the stack. The stack stores O(log K) frames of O(n) bits.
Construction scratch is O(n^2+w_0 n), with O(Vn+n^2) retained bits.

For completeness, a zero-based leaf index i in band j has offset
delta=i-prefix_j, then sign=delta mod 2, pair=floor(delta/2),
k=l_j+floor(pair/w_j), and t=pair mod w_j. Scanning the short band descriptor
and these exact divisions give the stated polynomial decoding cost.

If endpoints have the same k, process the one t/sign slice once. Otherwise
process the first k suffix and last k prefix once each, whether or not either
happens to be a full k row, and exclude those k's from the middle ranges.
This convention prevents endpoint double counting. There are at most
2w_0=O(M^(1/6)+1) scalar (k,t) evaluations and only a constant factor more
leaf multiplications. Single signs, both equal signs, adjacent endpoint k's,
and an empty middle range are all covered. An offered empty interval returns 1.

The remaining complete k rows meet O(n) bands and their terminal records in
ordered consecutive ranges. Scan the retained data sequentially. Keep C and
the record header in O(n) bits; stream each Y_t and process its twelve
class/sign polynomials sequentially, disposing of each product tree before
the next. A skipped record is still scanned. There is no need to return to
the start of the whole retained array for every t or every interval fragment.
Each clipped certified block inherits its identity without further sampling.

For a nonempty clipped block of L'_b k rows, each of six class lengths is
at most L'_b, so the fixed six/sign sum is O(sqrt(L'_b)); processing all t
costs w_j sqrt(L'_b) poly(n). Define the short-record count unambiguously as

    V_short = sum_(short b) w_(j(b)) L'_b,

the number of requested (k,t) pairs in explicit terminal records. Then

    sum_(certified b) w_(j(b)) sqrt(L'_b)
       <= sum_(certified b) w_(j(b)) L'_b <= V,
    V_short <= V.

Adding the full O(Vn)-bit scan, boundary work, decoding, modular reductions,
tree traffic and output yields P <= V poly(n) and

    C_P + P <= M^(1/3) poly(n).

This is a worst-case majorant; a short or empty query need not actually scan
all data, but charging such a scan is safe. It is not evidence that every
individual query requires Omega(V) work. Modulus-specific coefficients and
trees are regenerated and charged on every query, with no cache assumed.

The largest tree has h=O(sqrt(K)). Stream boundary rows and the t/class/sign
queries, giving the submitted safe peak bound

    O(Vn+n^2) + soft-O(sqrt(K)n) bits.

Construction's O(w_0 n) temporary data fits because w_0=O(sqrt(K)+1). All
live data, including retained output, is counted. This proof supplies a finite
sequential-access majorant; it is not a runtime assertion about unexecuted code.

## 6. Independent derivation of the outer-root block lemma

Set U=M^(1/3), a_J=ceil(3U/4), b_J=floor(U), and
J={a_J,...,b_J}. M>=4096 gives U>=16, K>=b_J, and

    |J| = floor(U)-ceil(3U/4)+1 >= U/4-1 >= U/8.

An upper bound O(U) is immediate. The exact lower-end test is 64a^3>=27M
and the upper-end test is b^3<=M. Thus the endpoints are correct even when
M is not a cube; no rounding of a numerical cube root is being assumed.

For f(v)=2sqrt(Mv), differentiation gives

    f''(v) = -sqrt(M)/(2v^(3/2)),
    f''(3U/4) = -4/(3sqrt(3)),    f''(U)=-1/2.

This derivative increases with v. Since 3>25/9, sqrt(3)>5/3, and hence

    -4/5 < -4/(3sqrt(3)) <= f''(v) <= -1/2

throughout the entire closed real interval. For a triple inside J, its
double integral over unit steps is exactly Delta^2 f(k). Let
epsilon_k=ceil(f(k))-f(k). Then 0<=epsilon_k<1, including epsilon_k=0 at
square arguments, and -2<epsilon_(k+2)-2epsilon_(k+1)+epsilon_k<2. Consequently

    -14/5 < Delta^2 c(k) < 3/2.

Integrality gives precisely the containing set {-2,-1,0,1}. This is a
containment assertion, not a claim that each value occurs for every M.

Now let P in Q[X] agree with c on L consecutive integers of J and let
D be a nonnegative integer with deg(P)<=D. L=0,1,2 is immediate. For L>=3,
put Q(X)=P(X+2)-2P(X+1)+P(X).

If Q is nonconstant, deg(P)>=3 and deg(Q)=deg(P)-2<=D-2 in characteristic
zero. The polynomial

    (Q+2)(Q+1)Q(Q-1)

is nonzero and has degree at most 4(D-2). Its roots include all L-2 distinct
integer triple starts. Thus L-2<=4(D-2), or L<=4D-6. This argument does not
count multiplicities of roots as additional positions and needs no assumptions
about repeated roots of this polynomial. The nonconstant case cannot occur
for D=0,1,2; in particular a degree-two polynomial cannot be hidden here.

If Q is constant, any one matching triple makes it an integer
m in {-2,-1,0,1}. The leading coefficient formula for a degree-d polynomial's
second difference is d(d-1) times its leading coefficient; therefore P has
degree at most two and P''=m. Set E=P-f on the real block interval. If m<=-1,

    E'' <= -1+4/(3sqrt(3)) < -1/5.

If m>=0, E''>=1/2. In both cases the sign is fixed and |E''|>=1/5.
For q=floor((L-1)/2), the three integer points a,a+q,a+2q all belong to the
block. At those points E belongs to [0,1). If q>=1,

    |E(a+2q)-2E(a+q)+E(a)| >= q^2/5,

by the double-integral formula and fixed sign. The same absolute value is
strictly less than 2 from the three endpoint values. Hence q^2<10, so
q<=3. Since L is either 2q+1 or 2q+2, L<=8. The q=0 case is already small.
The proof includes constants and linear polynomials (m=0) and every quadratic
case; it never asserts E in [0,1) at noninteger points.

Combining the cases gives exactly the submitted bound

    L <= max(8,4D-6).

For an actual cubic with nonconstant second difference the sharper bound is
L<=6, but degree-at-most-three records may be quadratic. Eight is a valid
uniform constant; there is no need to assert that it is attained or optimal.

## 7. Why the cubic lemma really costs this constructor work

Intersect every terminal block with J. Each nonempty intersection is a single
consecutive integer interval. A certified record supplies P(k)=C(k-a), whose
degree is at most three; translation does not change degree. Thus its
intersection has at most eight positions. An explicit short record has at
most three. These intersections partition J even if J crosses a dyadic boundary.
If B_J records meet J, then

    B_J >= |J|/8 >= U/64.

Section 2 of the submission explicitly retains one header and coefficients or
root data per terminal block. Producing B_J separate records takes Omega(B_J)
bit-machine steps, independently of how fast any later multiplication is.
This proves C_P=Omega(M^(1/3)) for every M>=4096 in this specified constructor.
The bound does not require inferring an Omega(n)-bit field from an O(n)-bit
upper bound. If fields are actually padded to a chosen linear-in-n width,
their larger traffic must also be charged, but the weaker bound already closes
the target.

Splitting at band endpoints, clipping a block to J, or making more short
records cannot defeat this cover count. Empty intersections contribute nothing.
Even an overlapping cover by individually valid consecutive cubic blocks has
|J|<=sum_b |I_b intersect J|<=8B_J. Reusing coefficients does not erase the
specified cubic block records. This observation concerns record incidence;
it is not a theorem about shared high-degree coefficient arrays or joint
batch computations.

A better Bernstein test could accept more of the valid blocks, but no valid
outer cubic covers more than eight of these positions. Granting inner roots
and modular products at zero cost still leaves the written records. Lazily
writing the same collection for the full interval would charge that work to
P instead. This last statement applies only if the same representation is
actually materialized; it is not a lower bound on a different lazy algorithm.

For fixed tau<1/3 and any fixed polynomial factor in n, the ratio of U to
M^(tau+o(1)) poly(n) grows without bound. Thus this mandatory constructor fails
the requested fixed tau<1/5 scale. Small-modulus shortcuts, early zero products,
or an easy particular interval may reduce a query's work, but do not remove
this constructor's once-per-M output. A different modulus-aware construction
would require its own proof and is not ruled out.

## 8. Growing degrees, explicit exceptions, and the dense-output premise

Let a length-L consecutive interval inside J have e distinct exceptional
positions, 0<=e<=L, and let P agree with c at every other position. For L<=2
the bound L<=4D+9e+8 is immediate, including empty intervals. For L>=3 let
g be the number of triples avoiding all exceptions. An exception can spoil
only starts k-2,k-1,k, clipped to the interval, so

    g >= L-2-3e.

If Q=Delta^2 P is nonconstant, the preceding polynomial root count on good
triples gives g<=4(D-2), and hence L<=4D+3e-6. It implies the submitted
weaker bound even when L-2-3e is negative. This case necessarily has D>=3.

If no good triple exists, every nonexceptional run has length at most two.
There are at most e+1 runs, including empty runs at endpoints, so
L-e<=2(e+1), or L<=3e+2. This also proves the claimed inequality without
knowing whether Q is constant or whether P matches anywhere.

The remaining case has Q constant and at least one good triple. That triple
forces Q=m in {-2,-1,0,1}, giving the same curvature argument on any
nonexceptional run. Runs of length at least three have length at most eight;
shorter runs satisfy the same bound automatically. Therefore

    L-e <= 8(e+1),       L <= 9e+8 <= 4D+9e+8.

This covers exceptions at endpoints, adjacent exceptions, all-exception blocks,
and constant or zero polynomials. Counting duplicate listed positions cannot
help: use the distinct set for the proof, while duplicates only add paid entries.
No bound on coefficient height, or on the numerical size of D, enters the proof.

For a partition of J by such block intersections, apply the inequality with
the **actual degree** delta_b=max(0,deg P_b), assigning zero polynomial degree
budget zero. Let E_all=sum e_b, and set

    W = sum_b (delta_b+1) + E_all.

Summation gives

    |J| <= 4 sum_b delta_b + 9 E_all + 8B <= 9W,
    W >= |J|/9 >= U/72.

This is an algebraic degree/exception-budget inequality. It becomes an
Omega(M^(1/3)) paid-output inequality under the following representation
premise: each block separately materializes a dense list through its actual
degree (zero coefficient slots included), and exceptions are separately listed
with their positions and correction information. Each written slot or entry
has at least one bit/symbol; producing or passing this actual list therefore
costs Omega(W). Explicit dense Newton/binomial lists have the same degree count.
Rational numerators, denominators, locating exceptions, and residue preparation
can only add work after this premise is satisfied.

An arbitrary declared upper bound D_b is not itself an allocated list length.
For example, a low-degree P does not cost D_b+1 slots merely because someone
declares a much larger D_b. Applying the proof with delta_b avoids that error;
alternatively a padded dense list really written through D_b pays its padding.
The submitted conclusion is sound within that dense-list interpretation. It
does not prove a lower bound for merely *having* a high degree or supplying a
small sparse expression. Nor does the inequality lower-bound distinct shared
coefficient arrays by summing their uses; independent materialization is part
of the cost premise.

For an overlapping collection of independently valid full consecutive blocks,
|J|<=sum L_b still allows the same sum-of-incidences argument, with exceptions
counted for each representation. That observation supplies no shortcut for
shared data, assigning each point to an unlisted nonconsecutive subset, or
implicit exception selection. Those are different representations. Band/J
clipping only reduces each L_b and its exception set; no new high-degree
coefficients are presumed to have been generated for free when clipping.

This growing-degree section is a lower count, not a positive growing-degree
algorithm. It does not extend cubic denominator 6, fixed-degree certificate
costs, or fixed-degree product costs to arbitrary D. In particular, correcting
a wrong modular product at an exception by dividing out its old value would
not be legitimate over arbitrary composite rings. No such patch algorithm is
needed or granted by this negative count; even free correct patch handling
would leave its mandatory dense output.

Rounded polynomial expressions, sparse high-degree circuits, nonconsecutive
residue blocks, implicit exceptions, shared batch computation, direct pair
products, and modular-only polynomial identities are all outside this cost
theorem. The characteristic-zero root-count proof cannot be transferred to
Z/dZ by assertion. Reducing away coefficients or deriving a residue without
first materializing the counted rational lists is likewise outside the premise.

## 9. Primary attribution, with limited historical scope

These source checks are distinct from the symbolic proofs above. The precise
reading ranges, access history, and hashes are in the review source notes.

[Harvey, arXiv:2010.05450v1](https://arxiv.org/html/2010.05450v1), sections
2.1-2.3, supplies integer arithmetic, the general packed-width formula in
Lemma 2.1's proof, a product tree whose roots are inputs in Lemma 2.3, and the
small-factor scale in Proposition 2.5. Its simplified polynomial bound has a
degree-versus-modulus restriction; H030 correctly retains the general width.
Remark 3.4, especially its last paragraph, already poses the full square-root
saving on Lehman's original search and the possible exponent 1/6. The aspiration
is not H030 novelty. Harvey's unit-based geometric evaluator is not being
substituted for H030's arbitrary-point remainder tree.

[Bostan, Gaudry and Schost, SIAM J. Comput. 36(6), 1777-1806 (2007),
DOI 10.1137/S0097539704443793](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf):
printed pages 1779-1780 describe ordinary factorial batching over arbitrary
rings; page 1782 distinguishes evaluation from inverse-dependent interpolation.
Theorem 8 on page 1787 assumes H(alpha,beta,k) and a known inverse of D.
Lemma 13 on page 1791 uses nonunit detection to find a factor in its factoring
application. That output does not satisfy RootProduct. The appendix, pages
1802-1803, also describes packed widths and sequential tree passes. These
passages support the ordinary tools and the limitation on importing the faster
unit-dependent method; none constructs H030's rounded-root coefficients.

[Harvey and Hittmeir, arXiv:2105.11105v1, introduction and Theorem
1.1](https://arxiv.org/html/2105.11105v1) states full deterministic classical
factorization in
O(N^(1/5)(log N)^(16/5)/(log log N)^(3/5)) bit operations on a fixed finite-tape
machine. This is the historical matched comparison used here. It is not a
claim about the latest worldwide result as of the review date. No exhaustive
novelty search, heuristic-GNFS comparison, or later-literature exclusion follows.

The original Lehman proof and the polynomial-arithmetic textbook were not newly
audited. The accepted H029/H004 coverage and recovery arguments are inherited
within their reviewed scope, not reattributed to H030.

## 10. Exact clarifications and final disposition

No correction to the submitted certificate inequalities, denominators, product
identity, degree cases, constants 8 and 4D-6, exception constant 9, or final
fixed-exponent rejection is required. The following wording makes acceptance
less vulnerable to broader interpretations; it is supplied here without editing
the preserved submission:

1. At section 4's V_short declaration: "Let V_short=sum_(short b)
   w_(j(b)) L'_b count queried (k,t) pairs in short terminal records." This
   resolves the possible ambiguity between k rows and scalar pairs.
2. At section 5.1's record-traffic sentence: "The constructor writes at least
   |J|/8 nonempty terminal records, hence costs Omega(M^(1/3)) bit steps. Any
   actually used field widths and storage traffic are additional; O(n)-bit
   field upper bounds alone imply no Omega(n)-per-field lower bound."
3. At section 5.2's cost consequence: "Apply the inequality with each
   polynomial's actual degree delta_b. If every block separately materializes
   a dense list of delta_b+1 coefficient slots and explicitly lists its e_b
   exceptions, the total number of written slots/entries is at least |J|/9.
   A larger declared degree counts only if those extra dense slots are actually
   written. Shared arrays, compressed expressions, and direct modular generation
   are outside this output-cost conclusion."

These clarify notation and cost scope rather than repair a false mathematical
claim. The scoped negative result is useful evidence: the chosen exact
consecutive-cubic constructor cannot provide the missing fast RootProduct, and
merely increasing separately materialized dense degrees with explicitly listed
exceptions does not fix its output count. Accept that conclusion and the finite
M^(1/3) poly(n) specification. Reject this realization as the requested faster
construction. RootProduct and COMPLETE factoring have no lower bound proved
here, and verified full factoring improvement remains **NONE**.

No further constructive task or finite experiment is selected by this reviewer.
Symbolic analysis closes the assigned audit; no numerical preregistration is
needed for its conclusions. The evidence delivery manifest excludes itself and
seals this report and all H030-review-* supporting artifacts.
