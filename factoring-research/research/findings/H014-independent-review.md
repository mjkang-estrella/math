# H014 — Independent review of exact coefficient-line enumeration

Date: 2026-10-08. Reviewed mathematical construction, source, and frozen evidence
in [H014-resultant-enumerator.md](H014-resultant-enumerator.md).

**Disposition: accept the exact output-sensitive primitive and its polynomial
bit-cost construction, including a conservative mathematical realization of
the stated Z^30 envelope. Accept the fixed eta = 2/5 conditional obstruction
and the eta = 1/10 optimistic inequality witness.** No correctness defect was
found in the frozen implementation. The explicit exponent is supported by the
additional arithmetic/access ledger below, not by applying a fast isolation
theorem to this slower Python program. This is reviewed informal mathematics,
not a proof of CPython execution cost, Lean refinement, or novelty.

**Verified full factoring complexity improvement: NONE.** There is no lower
bound on useful supply, established joint smoothness law, rank guarantee,
complete ideal/square-root algorithm, or proper-splitting probability here.

## 1. Scope and claim decisions

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, W001 Card C and shared accounting,
H008's independent review and disposition, the full H013 construction and
independent review, H013's disposition, and the complete H014 report,
implementation, validation source, protocol, raw records, summary and provenance.
The current H013 disposition supersedes H014's historical statement that H013
was awaiting review. H013 closes its full-cube model; it does not close this
changed enumerator. Only the nonnegative-f counting argument is needed here,
and it is checked directly below.

The decisions are:

1. **ACCEPT — exact set and line construction.** Every positive-leading cube
   quadratic satisfying the closed resultant cutoff is emitted exactly once,
   before primitive/irreducible filtering. Threshold flooring, degree loss at
   interpolation nodes, repeated f-roots and zero resultants are covered.
2. **ACCEPT — executable boundary search.** The square-free union polynomial,
   positive primitive normalization, one-sided Sturm counts, dyadic isolation,
   integer testing and cursor partition are correct. Short-interval counting
   is not substituted for a root-location algorithm.
3. **ACCEPT — uniform polynomial bit work and polynomial working space.**
   The primitive costs (H² + S_all) poly(Z), where Z includes n, d, log A and
   log H. Section 4 supports the deliberately loose Z^30 bound for a finite
   multitape realization. No fast root-isolation bound is attributed to the
   prototype, and no formal refinement of that prototype is accepted.
4. **ACCEPT — frozen finite screen, within its stated scope.** All six manifest
   output hashes match. The 47 records match the registered cases and summary.
   This review inspected the evidence and source; it did not rerun either
   candidate or original runner. The recorded 47/47 pass is not a growing-degree
   complexity test or an eta = .1 density test.
5. **ACCEPT — population upper bound and conditional eta = .4 exclusion.**
   The proof uses upper supply to limit possible distinct attempts, not as a
   lower cost. It derives c >= u >= (1024/135)^(1/3) within the unchanged model.
6. **ACCEPT — eta = .1 feasibility witness only.** The exact fractions and strict
   margins check. A nonempty optimistic region is not achieved candidate supply
   or a factoring bound. **REJECT any stronger interpretation** of that witness.
7. **ACCEPT — remaining cost qualifications.** Naive norm trial division retains
   its B factor. Reducible-factor parity, empty lines, failed candidates,
   ideal data, useful rank, root extraction and restarts remain charged.

No proposer file, shared code, Lean file, STATE, registry, prior report or frozen
evidence was modified. This review writes only this report and
[H014-review-provenance.json](H014-review-provenance.json). No packages,
delegation, commits, publication, scheduler, new density sweep, or smoothness
implementation was used. H016 and H017 are separate tasks; their work is neither
assumed nor duplicated here.

## 2. Exact threshold and resultant polynomials

Assume the report's domain: N > 1, H >= 1 an integer, and monic nonnegative
integer f of degree d >= 3, with height A >= 1. Degree and coefficient/height
bit lengths must be polynomial in n = bitlength(N) to use the shorter poly(n)
notation. Otherwise the accepted complexity is polynomial in Z, not n alone.

Let p = 5d, C0 = (3H)^d(d+1)A² and

    T = iroot_p(floor(C0^p / N^6)).

For each nonnegative integer r, r^p N^6 <= C0^p is equivalent to
r^p <= floor(C0^p/N^6). Thus the exact acceptance predicate is |Res| <= T,
including equality and T = 0. The two power inequalities checked by
`threshold_for` certify the floor independently of floating-point arithmetic.
The unreduced powers occupy O(d² log(2H) + d log(2A) + d log(d+1) + n) bits.
Binary root search is polynomial in these widths and d. Eta = .1 instead uses
N^9 with the same p = 5d; the implemented `n_power` argument permits that
cutoff, although the frozen cube screen used its default value 6.

The map (a,b,c) -> (a,beta=b+2a,gamma=c-a) is an integer bijection. Solving the
three height inequalities gives exactly

    L = max(1, ceil((beta-H)/2), -H-gamma),
    U = min(H, floor((beta+H)/2), H-gamma).

The code's `-((height-beta)//2)` is the correct ceiling, including negative
arguments. The label rectangle [-3H,3H] x [-2H,2H] contains all required
labels. Empty intervals are tested and charged. The full invocation visits
exactly (6H+1)(4H+1) labels, and the a=1 slice alone supplies (2H+1)² distinct
nonempty labels. This particular complete algorithm necessarily pays an H²
line scale even when its output is empty.

Writing the roots of monic f with multiplicity, the leading coefficient of

    P_beta,gamma(Z) = product_i [Z(alpha_i-1)² + beta alpha_i + gamma]

is f(1)² >= A² > 0. Therefore each P has exact degree d. Neither threshold
polynomial P-T nor P+T vanishes identically. Repeated roots of f do not change
this argument. At T=0 some individual a values may give zero resultants;
that never makes an entire line polynomial zero.

For the implemented resultant, multiplication by X in Q[X]/(f) has characteristic
polynomial f. Consequently det(g(M_X)) is the root product above even when the
quotient is not a field or M_X is not diagonalizable. Monicity makes the same
multiplication matrix integral in the power basis. The implementation reduces
powers only through X^(d+1), so its entries have polynomial bit width. In
Bareiss elimination, a nonzero pivot is found by a row swap, whose sign is
tracked. Each exact division is justified by the determinant identity; the
stored quantities are signed minors of a row-permuted original matrix. A
remaining all-zero pivot column correctly gives determinant zero.

The d+1 values at Z=0,...,d determine P. Newton forward differences and the
basis binomial(Z,k) in `line_polynomial` give the exact interpolant. Denominators
divide factorials; they are not real approximations. At Z=0, g can be linear,
constant or zero, all of which the multiplication determinant handles. The
integrality and f(1)² assertions are valid invariants. The independent runner
uses a different Sylvester matrix and rational Gaussian elimination, so it
does not merely compare two calls to the same determinant routine.

The ordinary N-only base construction checks both actual degree and monicity.
The supplied polynomial primitive does not require a number field; any later
NFS use does. Rejection of N=63,d=3 is a legitimate domain check, not a silent
change of f or an unproved all-input field-selection method.

## 3. Boundary search and all degeneracies

For nonconstant P, Q=(P-T)(P+T) is nonzero. Dividing by gcd(Q,Q') and taking a
primitive part retains exactly its distinct roots. For T=0 this removes the
complete duplication in P². Even multiplicities and tangencies require no
special sign-crossing assumption: subsequent integer evaluations use P itself.
For constant P, including zero, `accepted_ranges` returns the whole clipped
integer interval or nothing before calling isolation. Empty clipping and a
negative threshold return nothing. Valid line inputs always have T>=0.

In `primitive`, the denominator lcm is positive and gcd is nonnegative. Thus
normalization multiplies every nonzero polynomial by a positive scalar. It
does not force a positive leading coefficient. If consecutive polynomials are
scaled positively, the next negative remainder is positively proportional to
the corresponding ordinary Sturm remainder. Induction therefore preserves
the entire Sturm sign rule. Arbitrary negative rescaling would not do so.
The sign of the polynomial gcd does not affect square-free roots.

At a rational endpoint x, the first nonzero derivative of a polynomial has
some order j. Taylor's formula gives its sign immediately to the right, and
(-1)^j times that sign immediately to the left. The `side_sign` loop implements
this exactly and terminates in at most degree+1 derivative tests. Taking the
limits of ordinary Sturm variation counts gives

    # roots in (l,r) = V(l+) - V(r-).

This also handles zeros of intermediate sequence polynomials. A midpoint root
is output once, excluded from both open children, and included in the checked
identity `left_count + right_count + at_mid == parent_count`.

The initial radius 2+floor(max |q_i|/|lc(q)|) is strictly larger than the Cauchy
bound 1+max |q_i|/|lc(q)|, including when the ratio is an integer. Thus its
endpoints are nonroots and contain every real root strictly between them.
Nonpoint intervals are accepted only with one open root, width <=1/4 and both
endpoints nonroots. In particular they cannot also contain a root previously
output as an endpoint point. If an interval still has a root endpoint and a
different interior root, separation forces further subdivision eventually to
remove that endpoint. A degree-one square-free part needs no separation
between distinct roots; the radius and width condition suffice.

The returned intervals are ordered, with disjoint interiors; only nonroot
endpoints can be shared. Between them there is no zero of P-T or P+T, so the
closed acceptance predicate is constant on each real gap. In the code, the
integers below the next closed interval end at ceil(left)-1. The closed
interval itself contains at most one integer, found using exact floor/ceiling
and tested by exact P(k). Afterwards the cursor advances to at least
floor(right)+1. This partitions the clipped integers, including a shared
integer nonroot endpoint, without omission or duplication.

Intervals outside the clipping range cannot introduce outputs: all ends are
clipped, the cursor never decreases, and once it exceeds U no later loop emits.
If there are no real boundary roots, one evaluation classifies the whole
clipped range. Long rejected gaps cost one test; long accepted gaps incur
their number of outputs. Integer roots need not be encountered as dyadic
midpoints, and a noninteger root need not be separated from the nearest
integer: testing that one enclosed integer directly is sufficient. This
avoids a common hidden extra root-recognition obligation.

No flaw was found that calls for a new finite test. The proof handles the
specific dangerous cases more generally than another small sweep would.

## 4. Growing-degree bit cost and the explicit exponent

The two cited primary sources were opened directly and their displayed
hypotheses and bounds checked:

- Emiris–Tsigaridas, Theorems 3 and 8, bound Sturm–Habicht coefficients and
  square-free reduction; Theorem 19 gives soft-O(D^4 tau²) bit isolation,
  including multiplicities, under D=O(tau). Padding tau to max(tau,D) is
  legitimate. Section 2 identifies the proportionality with signed remainder
  polynomials. These statements justify polynomial isolation and the
  normalized coefficient-size argument, not that the prototype runs their
  optimized routine. [Primary full text](https://arxiv.org/pdf/cs/0512072).
- Sagraloff–Mehlhorn v2, Theorems 2 and 3, give square-free integer isolation
  in soft-O(D³+D² tau) and intervals of width below 2^(-k) in
  soft-O(D(D²+D tau+k)). The square-free hypothesis is met after reduction.
  These are a separate constructive polynomial-time route, not a measured
  bound for Python's rational Sturm divisions.
  [Primary full text](https://arxiv.org/pdf/1308.4088v2).

Here is an independent, deliberately slow ledger for the actual arithmetic
route. Put D=deg Q<=2d, let tau bound Q's coefficient bits, and put
W=tau+D+ceil(log2(2H))+1. Constants below are independent of N,d,H,A.

The primitive square-free factor q has coefficient bits O(tau+D). Indeed,
for a primitive integer factor h of primitive Q, multiplicativity of Mahler
measure and the complementary factor's measure >=1 give
H(h)<=2^D M(Q)<=2^D sqrt(D+1) H(Q). Derivatives add O(D log D) bits at most.
Every primitive Euclidean remainder is the primitive part, up to sign, of an
integer subresultant polynomial. Determinantal coefficient bounds give
O(DW) bits for the normalized sequence, including degree drops.

For long division of two normalized integer polynomials, let B be the bit
bound for their coefficients, here O(DW). After j<=D+1 elimination steps,
all rational denominators divide a power of the divisor's leading coefficient
with exponent at most j; numerator growth is O(D(B+log D)). Thus individual
pre-normalization fractions have O(D²W) bits. Even bounding the denominator
lcm by the product of all O(D) denominators, and then clearing content, uses
O(D³W) bits. There are O(D³) rational operations over an entire remainder/gcd
sequence. Exact quotient and square-free computations obey the same bound.
This explicitly prevents cumulative exponential coefficient growth across
successive unnormalized divisions.

For square-free q of degree k>=2, its nonzero integer discriminant gives

    1 <= |lc(q)|^(2k-2) product_(i<j) |z_i-z_j|².

Bounding all but the smallest pair distance by 2R yields
max(0,log2(1/sep(q)))=O(D²W), with log R=O(W). Therefore O(D²W) dyadic
levels suffice both for separation/nonroot endpoints and width <=1/4.
There are at most D positive-count intervals per level and at most twice
as many children; the complete traversal has O(D³W) nodes. Discovered
point roots are removed, not repeatedly rediscovered. Degree one is bounded
by the radius and width argument alone.

Dyadic numerator/denominator widths are O(D²W). Evaluating any derivative of
any sequence polynomial by Horner uses intermediates of O(D³W) bits: degree
is at most D, including accumulated powers of the endpoint denominator.
A node uses O(D³) rational operations even if every one-sided test tries all
derivatives. Classical arithmetic and Euclidean gcd fit an O(v³) allowance
on v-bit rational operands. The resulting arithmetic bound is

    O(D³W * D³ * (D³W)³) = O(D^15 W^4),

with polynomial preprocessing, sorting and gap tests below the report's
O((D+1)^16 W^4) allowance. No root, gcd, sign, or real-number operation is
being charged at unit bit cost.

**The Z^30 claim is supportable, but requires the access accounting as well.**
Let Z be exactly the report's n+d+ceil(log2(2A))+ceil(log2(2H))+2. Resultant
interpolation has coefficient bits O(Z³); T<=C0, so Q also has tau=O(Z³).
Thus D=O(Z), W=O(Z³), the root traversal performs O(Z^9) arithmetic/list
steps, and its largest rational operands have O(Z^6) bits. Its arithmetic
allowance is O(Z^27); using the report's extra degree factor gives O(Z^28).

For an explicit finite-tape realization, the sequence occupies O(D³W) bits;
normalization scratch fits O(D^4W). A depth-first stack has at most
O(D²W) pending entries, each of O(D²W) bits, hence O(D^4W²) bits. The
root list, range list and derivative scratch do not exceed these bounds.
Counters accumulated over all lines still use only O(log H+log Z) bits.
Total working storage can consequently be bounded by O(Z^10) bits.

Store self-delimited lists on working tapes; a requested operand can be
located/copied by a sequential scan, then processed on fixed arithmetic
scratch tapes. Even charging O(Z^11) access/copy work per high-level step
allows scanning and record counters. This adds O(Z^20) to the root traversal,
well inside Z^30; it does not require multiplying each arithmetic bit step
by the complete memory size. Sorting O(D) intervals can use a simple quadratic
comparison sort. Threshold search, d+1 Bareiss determinants, interpolation
and polynomial gcd/normalization have at most polynomially many operations
within the same envelope (at most O(Z^4) operations for determinant setup and
elimination, and O(Z^3) for the remaining scalar sequences, with no larger
operand/access allowance). They fit below Z^30 as well.

This supplies the missing explicit explanation behind the report's brief
statement that two spare powers cover access. It supports **existence of a
fixed finite classical implementation of this route** with

    O((H² + S_all) Z^30) bit steps,

and polynomial working space, on a multitape machine with a separate append-only
output tape. It is not a theorem about an arbitrary runtime simulation of
Python, a fixed degree assumption, or an assertion that the exponent is sharp.
A generic polynomial-time machine simulation alone would justify poly(Z),
not preserve the number 30; that shortcut is not used here.

Each emitted triple has O(log(2H)) bits. Retaining all outputs therefore costs
O(S_all log(2H)) space; the generator need retain only the current line's
O(d) ranges. Diagnostic materialization in the frozen runner is separately
charged validation memory. The generic helper's arbitrary threshold must be
included in its input-width accounting; H014's special threshold satisfies
the stated bound. Gcd/discriminant filtering after emission costs polynomial
bit work for every output and cannot reduce the enumerator's S_all charge.

## 5. Population bound and fixed eta = 2/5 obstruction

Independently of how roots are located, a degree-d polynomial with nonzero
leading coefficient L satisfies

    #{k in Z : |P(k)|<=T} <= d(1+2(T/|L|)^(1/d)).

If all d root distances exceeded the displayed radius, their product would
exceed T/|L|. Each disk intersects the real axis in an interval of length at
most twice the radius; it contains at most that length plus one integers.
The argument remains valid at T=0 and with repeated or nonreal roots.
Using L=f(1)²>=A² gives the specific all-output upper bound

    S_all <= d(6H+1)(4H+1)(1+12H N^(-6/(5d²))).

Replacing 6/5 by Q_eta=2(1-eta) proves the stated general-eta version.
In the supplied L scaling its upper exponent is

    s = max(2a, 3a-Q_eta/delta²).

This gives a sufficient enumeration upper envelope L[1/3,s]; it does not
prove an actual population of that size. The necessary full-run line cost
has exponent 2a. Output work depends on the actual S_all. The H² summand in
the population bound is not a lower count and cannot be erased as a
continuous-volume rounding error.

Now assume exactly the report's joint-smoothness and B-scale relation-count
model. Let u be the exponent of distinct candidates actually processed under
that model, counting unsuccessful candidates as work. Reprocessing the same
fixed value cannot create independent smoothness trials or fresh useful rows.
With K=2(1+eta), necessary conditions are

    u >= b+(K/delta+a delta)/(3b),    u<=s,    c>=u.

Upper supply only limits the possible u. No lower supply is used. Since
u<=max(2a,3a-Q_eta/delta²), at least one branch holds:

- If u<=2a, then a>=u/2 and
  K/delta+a delta>=2 sqrt(Ku/2). Minimizing b+A/b gives
  u^4>=32Ku/9, hence u³>=32K/9.
- If u<=3a-Q_eta/delta², then
  K/delta+a delta>=(K+Q_eta/3)/delta+u delta/3.
  The same two AM-GM steps give u³>=64(K+Q_eta/3)/27.

Here u>0 follows from the required b>0, so cancellation of u is valid.
At eta=2/5 these branch bounds are 448/45 and 1024/135. Taking the weaker
one correctly yields

    c >= u >= (1024/135)^(1/3) > (64/9)^(1/3) > c_C.

The first strict comparison follows since 1024/135>960/135. Lee–Venkatesan's
Remark 4.31 gives c_C³=(92+26 sqrt(13))/27 for its square-congruence result;
that passage was opened directly. It is not an unconditional general
factor-extraction theorem. [Primary source](https://arxiv.org/html/1805.08873v1).

The proof remains valid if line, linear-algebra and completion costs are
omitted entirely. Adding them cannot rescue this particular model. This is
a fresh obstruction for the changed generator, not an application of H013's
H³ scan lower charge. It is not a bound on the actual joint smoothness of
correlated selected norms or a lower bound on factoring. A changed norm law,
collection target or stratified candidate distribution needs separate analysis.

## 6. Exact eta = 1/10 witness and completion obligations

For a=153/200, b=189/200, delta=21/10, the exact arithmetic is

    Q_eta/delta² = 20/49,
    s = 18491/9800 > 2a = 153/100,
    r := b+(K/delta+a delta)/(3b) = 4479883/2381400,
    s-r = 1343/238140 > 0,
    2b-s = 31/9800 > 0,
    max(s,2b) = 189/100.

These fractions agree with H014, including its unreduced expression for the
trial-division envelope. Also sqrt(13)>18/5 gives c_C³>928/135, while
(189/100)³=6751269/1000000<928/135. The comparison has a strict margin.
Continuity therefore gives a nonempty open parameter region with r<s and
max(s,2b)<c_C. No numerical search is needed.

This is only compatibility of necessary supply conditions with a sufficient
**conditional** cost envelope. It would require an actual attempt population
with exponent at least r, appropriate useful-row yield under the joint law,
polynomial processing per attempt, and completion costs within the envelope.
An upper bound s supplies none of these. The fixed eta=.4 finite screen is
not evidence for them at the stronger cutoff |Res|^(5d) N^9<=C0^(5d).

In particular, naive prime enumeration and trial division through B on all
nonzero rational values and integer norms has upper cost

    B poly(n) + S_all B poly(n).

At the witness, substituting the population upper envelope gives

    s+b = 3469/1225 = 13876/4900, approximately 2.832.

That is an upper processing envelope, not a proved lower runtime. It does
show that this conservative implementation fails to establish the desired
1.89 envelope. No B factor is removed by H014's integer sublevel enumeration.
A separate paid processing construction is required; H016 owns that question.
H017 owns the stronger-tail supply question. Neither outcome is presumed here.

The other outstanding obligations remain substantive:

- Construct suitable f/field and bases from the supplied N at charged cost,
  treating nonmonic or reducible ordinary base choices honestly.
- Establish enough distinct useful selected candidates, including losses to
  primitive/irreducible filters and joint rational/ideal smoothness, with the
  required input and probability quantifiers.
- Produce ideal valuations, exceptional-prime information, signs and
  square-class/character data. Integer norm parity alone is insufficient.
- Justify filtering, storage, actual sparse matrix weight and useful rank,
  dependency lifting, algebraic square roots and proper-factor gcd outputs.
- Bound collection failures and useful splitting probability sigma_N; expected
  independent-restart accounting includes T_trial/sigma_N.

For reducibles, H(u)H(v)<=sqrt(3)H follows from multiplicativity of Mahler
measure. Their bounded linear factors may supply many directions; there is
no d-rank conclusion. In a common-u group the exact parity identity is
R=V+c 1^T. Even dependencies have the additional even-cardinality condition;
an odd coset, when present, must be retained. Those qualifications in H014
are correct and cannot be replaced by treating every product as an independent
quadratic opportunity.

A quota version pays all visited lines, every root/boundary operation and all
failed candidates before stopping. Without a useful-supply/order guarantee it
can exhaust every line and fail. The primitive yields an output-sensitive
complete enumeration bound, not a bound on the first useful relation or on
time to complete a factorization.

## 7. Frozen evidence audit and handoff

All six H014 output hashes and byte lengths agree with the proposer manifest:
report, candidate, validation source, protocol, raw JSONL and summary. The
report hash is `a0fa3c18ac09c086f4b3669ef7cddad54bc76afb4d6464b8c758c6e7e6d00c23`.
The source hashes in the protocol agree with the actual files. Every raw
record's ID and input agree with its registered case; summary status counts
and recorded aggregate work agree:

- 47 pass; zero failure, error, timeout or unstarted records.
- 27 cubes, 17 ordinary sublevel cases, one wide symbolic interval, one
  54-pair integer-root case, and one explicit nonmonic rejection.
- 1,037 full-cube reference triples and 2,469 candidate labels.
- Recorded total 3.090900 seconds, candidate time 2.969490 seconds, reference
  comparison time 0.099195 seconds, and process peak RSS 19,268 KiB.

Eight cubes use clearly marked threshold overrides. The two actual T=0 cases
are N=10^9 and N=10^9+1 with d=3,H=1; each records three zero-resultant outputs.
Those are valid primitive outputs even though they need not be field relations.
The wide (X-10^30)²<=0 case records only 10^30, with 207 isolation nodes,
depth 103, two gap tests and one boundary test. No density or speedup is
inferred from these cases.

The exact full-cube Sylvester reference, duplicate checks, and direct integer
power comparisons are appropriate finite correctness checks. The original
runner refuses to overwrite evidence and records all statuses. This review
checks correspondence and source logic; hashes alone do not independently
prove historical execution order or single-run chronology. No new candidate
execution or oracle replay was performed, and no original runner was rerun.
Read-only evidence parsing, hashing and exact arithmetic on the displayed
witness are documentation/proof checks, not a new parameter experiment.

The next work can build on the accepted enumeration primitive without treating
it as a factorer. The remaining obstacles are useful supply and a full paid
completion argument, not an unpriced root-location oracle. No required
correctness revision to H014 was found. Preserve the distinction between the
mathematical Z^30 realization and any formal/runtime claim, and update H013's
review status only in parent-owned synthesis rather than frozen evidence.

This report changes no implementation, so shared build/Lean checks were not
run. Input hashes, direct primary-source checks and this report's hash are in
[H014-review-provenance.json](H014-review-provenance.json). Positive primitive
claims remain reviewed informal mathematics. Verified full factoring
complexity improvement remains **NONE**.
