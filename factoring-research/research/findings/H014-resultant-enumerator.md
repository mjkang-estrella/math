# H014 — Exact global-resultant enumeration by coefficient lines

Date: 2026-10-08. **Provisional mathematical construction and finite validation;
independent review required. Verified factoring complexity improvement: NONE.**

The changed enumerator is valid: it streams the entire specified sublevel set
in `H² poly(n) + S_all poly(n)` bit work, under the polynomial degree/width
conditions below. It does not visit every coefficient triple. An elementary
exact standard-library implementation passed its single preregistered screen:
47/47 cases, 3.09 seconds, no failures, timeouts, or unstarted cases.

This does **not** rescue the fixed eta = 2/5 proposal under Card C's unchanged
joint-smoothness model. Even granting polynomial processing cost per emitted
candidate, that model requires a cost constant at least `(1024/135)^(1/3)`,
larger than ordinary GNFS's constant. A **different, stronger threshold**,
eta = 1/10, has an explicit nonempty optimistic parameter region with envelope
1.89. This is an inequality witness, not a lower population bound, smoothness
theorem, relation-rank theorem, or factoring bound. Ordinary norm trial division
does not attain that envelope.

## 1. Scope and exact set

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, W001 Card C and its shared accounting,
H008-independent-review.md, H008-disposition.md, and H013-global-resultant.md
in full. H013 is awaiting another independent review. Section 6 below
independently proves the only population result used here; the rest of H013
is not used as a theorem oracle or reviewed again.

All writes in this task are this report and adjacent `H014-enumerator-*` files.
No shared code, Lean, STATE, registry, prior report, package, commit, publication,
scheduler, or delegated task was changed/created. The separate validation is
deliberately not installed as a factorer in the shared experiment harness.

Input to the primitive is a monic, nonnegative integer polynomial f of degree
d >= 3, an integer H >= 1, and N > 1. Write A = max_i f_i >= 1. For the
factoring interpretation f is the ordinary base-m polynomial computed from N
and the public degree choice, f(m) = N. The primitive itself does not require
f to be irreducible or even to arise from N. Its output is exactly

\[
 S_{\rm all}=\{(a,b,c)\in\mathbb Z^3:1\le a\le H,
 |b|,|c|\le H,\quad |\operatorname{Res}(f,aX^2+bX+c)|^{5d}N^6
 \le C_0^{5d}\},\qquad C_0=(3H)^d(d+1)A^2.                 \tag{1}
\]

We also use S_all for its cardinality when it is a cost. Zero resultants,
imprimitive and reducible quadratics are included. Filtering cannot replace
this cardinality in the full-output cost by a smaller useful-survivor count.
An irreducible f of degree > 2 has no zero resultant against a genuine
quadratic, but this fact is not needed for enumeration.

Let n = bitlength(N). The claimed `poly(n)` overhead requires
d, log(2A), log(2H) = poly(n). Without that promise the same construction is
polynomial in these additional input parameters, not necessarily in n alone.
The integer base and digits are computed by power comparisons and repeated
division, at polynomial bit cost. Check the actual degree and monicity; a small
N/public-d choice can fail these conditions (the screen includes N=63,d=3).
No field is silently substituted. In the intended growing-degree NFS regime
m >> d and `(m+1)^d < 2m^d` eventually, so the ordinary expansion with
`m=floor(N^(1/d))` has leading digit 1. Irreducibility/field selection remains
a separate factoring prerequisite, not an output of this primitive.

## 2. Exact integer threshold and line polynomial

Set p=5d, U=C0^p, V=N^6 and compute

\[
 T=\operatorname{iroot}_p(\lfloor U/V\rfloor).
                                                               \tag{2}
\]

Here iroot returns the largest nonnegative k with k^p <= its integer argument.
Binary search with integer powers suffices. Because k^p is an integer,
`k^p V <= U` iff `k^p <= floor(U/V)`. Thus (2) is precisely the requested
floor, including T=0, and acceptance is **exactly** `|Res(f,g)| <= T`.
Its certificate is `T^p V <= U < (T+1)^p V`. The widths of U and V are
`O(d² log(2H) + d log(2A) + d log(d+1) + n)`. No floating logarithm or
approximate equality test occurs.

Use integer labels beta=b+2a, gamma=c-a. Then

\[
 g=a(X-1)^2+\beta X+\gamma,\qquad
 P_{\beta,\gamma}(Z)=\operatorname{Res}(f,Z(X-1)^2+\beta X+\gamma).
                                                               \tag{3}
\]

The coordinate change is an integer bijection with inverse
`(a,b,c)=(a,beta-2a,gamma+a)`. Loop over
`-3H <= beta <= 3H`, `-2H <= gamma <= 2H`. Clip to the integer interval

\[
 L=\max(1,\lceil(\beta-H)/2\rceil,-H-\gamma),\qquad
 U_a=\min(H,\lfloor(\beta+H)/2\rfloor,H-\gamma).              \tag{4}
\]

An empty interval is charged and skipped. Every cube triple lies on exactly
one line and in its clipped interval. There are `(6H+1)(4H+1)=Theta(H²)`
labels; even the lines through the a=1 slice already give `(2H+1)²` distinct
nonempty labels. A full invocation of this particular algorithm pays that
line scale regardless of how many candidates it emits.

For the roots alpha_i of monic f, with multiplicity,

\[
 P_{\beta,\gamma}(Z)=
 \prod_{i=1}^d\{Z(\alpha_i-1)^2+\beta\alpha_i+\gamma\}.
\]

The coefficient of Z^d is
`prod_i(alpha_i-1)^2 = f(1)^2`. Nonnegative coefficients imply f(1)>=A>0.
Thus **every** P has exact degree d, not just generic lines. It is integral,
by the integer Sylvester determinant identity. Neither P-T nor P+T is the
zero polynomial. Repeated f-roots and isolated zeros of P cause no exception.
This independently establishes the leading-coefficient fact needed here.

To construct P, compute its values at Z=0,...,d by exact determinants, then
interpolate. A size-(d+2) padded Sylvester determinant with monic f works even
at Z=0, where g may lose degree. Fraction-free elimination costs polynomial
bit work, with intermediate determinants bounded by minors. Exact Lagrange
or Newton interpolation also has polynomial work: the node differences have
bit size O(log(d+1)), factorial denominators have O(d log(d+1)) bits, and
the final coefficients are integers. Integrality is checked in the prototype.

The prototype instead obtains each value as the determinant of multiplication
by g in `Z[X]/(f)`, using the basis `1,X,...,X^(d-1)`, and uses Bareiss
elimination. This is the same resultant: it is the determinant of g applied
to the companion matrix of f, whose eigenvalues are f's roots with algebraic
multiplicity. The identity holds with repeated roots and for lower-degree g.
Reduction modulo monic f uses only exact integer operations. This gives a
different construction from the validation's Sylvester matrix and ordinary
rational Gaussian elimination.

For example a conservative coefficient-width bound for P is
`O(d² (log(2A)+log(2H)+log(d+1)))`; tighter bounds are unnecessary.
The quotient-matrix implementation also meets this bound: only powers through
X^(d+1) must be reduced, followed by a size-d determinant and interpolation.
All d+1 evaluations are charged for every nonempty line. No resultant oracle
or unit-cost arithmetic on unbounded integers is assumed.

## 3. Locating and enumerating the sublevel set

The following is an executable construction, rather than the short-interval
counting argument used later. It works for an arbitrary integer P and T>=0.

1. If P is constant, return the whole clipped interval exactly when
   `|P|<=T`, otherwise return nothing. This handles the zero polynomial in
   the generic helper. It cannot occur for a valid line in (3).
2. Form `Q=(P-T)(P+T)` and compute its primitive square-free part
   `q=primitive(Q/gcd(Q,Q'))`. For T=0 this is the square-free part of P².
   It has exactly the distinct roots of the union of the two boundary
   polynomials. Multiplicity is irrelevant to locating all boundary points;
   we do not infer signs by assuming simple crossings.
3. Isolate every real root of q exactly, as a rational point or an interval
   with rational nonroot endpoints containing exactly one root. Refine the
   latter to width <=1/4. All these operations use Sturm counts, as specified
   below; they have polynomial bit cost even as the degree grows.
4. In each gap between these isolating intervals, intersect with [L,U_a].
   If any integers occur, evaluate P at the first such integer. Both P-T
   and P+T have constant nonzero signs throughout the gap. Emit all its
   integers iff this evaluation satisfies the closed inequality.
5. Each closed isolating interval of width <=1/4 contains at most one
   integer. Locate it by exact floor/ceiling and test P at that integer.
   A rational-point root is treated the same way. This handles all equality
   and integer-boundary cases, including tangency and repeated roots.

The sorted intervals and a moving cursor partition the integers without
duplication, including when adjacent intervals share a nonroot endpoint.
Floors and ceilings use rational integer division. We do **not** assume that
an approximate root whose value is close to an integer has been recognized
as that integer. We also do not need to refine a noninteger root away from
the nearest integer: the one possibly enclosed integer is evaluated exactly.

The root intervals are an exact algebraic representation, not floating
approximations used as evidence. Once they are certified, the algorithm uses
O(d) gap/endpoint tests per line plus the emitted outputs. A long rejected
gap costs one test. A long accepted gap costs its actual number of records.
This is the essential change from the H³ coefficient scan.

### The implemented elementary Sturm route

The implementation uses ordinary signed polynomial remainders over Q,
normalized to primitive integer coefficients by **positive** scaling after
each remainder. This preserves Sturm signs; normalizing leading coefficients
to positive without tracking signs would be incorrect. Square-free reduction
is exact polynomial gcd/division, with no integer factorization.

For a square-free q construct the sequence q, q', -rem(q,q'), ... . For an
endpoint x and side s in {-1,+1}, find the first nonzero derivative of each
sequence polynomial at x. Its sign times s^k, where k is that derivative's
order, is the one-sided sign. Ignore identically zero entries. If V(x^s)
is its number of variations, the number of distinct roots in the **open**
interval (l,r) is `V(l^+) - V(r^-)`. Thus midpoint and endpoint roots are
handled explicitly, without applying an endpoint-nonroot version of Sturm's
theorem outside its hypotheses.

Start with `(-R,R)`, where `R=2+floor(max_{i<deg q}|q_i|/|lc(q)|)`.
The Cauchy bound puts all roots strictly inside. Bisect an interval with
positive root count. If its midpoint is a root, retain that exact point and
exclude it from both open child counts. The identity
`parent_count = left_count + right_count + midpoint_is_root` is checked.
Discard zero-count children. Accept a one-root interval only when its width
is <=1/4 **and both endpoints are nonroots**. The last condition prevents an
interval for one root from also containing a previously emitted endpoint root.
An explicit stack avoids dependence on Python's recursion-depth limit.

Sturm's theorem certifies the counts; root separation ensures termination
with a polynomial number of subdivisions. This algorithm isolates the roots
of both boundary polynomials together and then classifies all integer gaps.
It does not use an oracle that returns short intervals.

## 4. Growing-degree bit cost, memory, and uniformity

Two primary-source checks establish that exact isolation is an ordinary
polynomial-time subroutine. Emiris–Tsigaridas, *Computations with one and two
real algebraic numbers*, Theorems 3, 8 and 19, give coefficient/gcd control
and Sturm–Habicht isolation including multiplicities. The displayed
`soft-O(D^4 tau²)` bound assumes D=O(tau); padding tau to max(tau,D) satisfies
that convention. Sagraloff–Mehlhorn, *Computing Real Roots of Real Polynomials*,
Theorems 2–3, give square-free integer isolation in
`soft-O(D³+D² tau)` and refinement to 2^-k in
`soft-O(D(D²+D tau+k))`. These are bit bounds, not unit-cost algebraic-real
operations. [Emiris–Tsigaridas](https://arxiv.org/pdf/cs/0512072),
[Sagraloff–Mehlhorn v2](https://arxiv.org/pdf/1308.4088v2).

We do not claim that the simple Python implementation achieves those fast
bounds. Here is a deliberately loose polynomial bound for its slower route.
Let D=deg Q<=2d, tau bound Q's coefficient bits, and
`W=tau+D+log(2H)+1`. The square-free primitive part has coefficient bits
O(tau+D). This also follows from the elementary factor estimate
`height(h)<=2^D M(h)<=2^D M(Q)<=2^D sqrt(D+1) height(Q)` for a primitive
integer factor h of primitive Q; the complementary integer factor has Mahler
measure >=1. Normalized primitive Euclidean remainders are proportional to
subresultant polynomials. Their coefficients are bounded by minors of
O(D)-size coefficient matrices, hence have O(DW) bits. A polynomial long
division between consecutive such remainders has O(D²) rational operations;
before the next content normalization a generous O(D³W) bound covers all
numerators/denominators. There are O(D) divisions. Positive normalization
does not increase primitive coefficient sizes. This is why using *normalized*
remainders is material; no bound for an uncontrolled pseudoremainder sequence
is being assumed.

For clarity, even a crude separation argument suffices for the subdivision
bound. Let q have degree k<=D, integer leading coefficient l, and all complex
roots in |z|<R. Its nonzero integer discriminant satisfies

\[
 1\le |\operatorname{disc}(q)|
 =|l|^{2k-2}\prod_{i<j}|z_i-z_j|^2.
\]

Bound all differences but a smallest one by 2R. It follows that
`log(1/sep(q))=O(D² W)`. Together with the root bound, at most O(D²W)
bisection levels isolate distinct roots and exclude previously recorded
endpoint roots; a further constant number reaches width 1/4. At each level
there are at most D positive-count intervals and their discarded children.
Thus O(D³W) nodes suffice. Dyadic endpoints have O(D²W) bits. One-sided signs
use at most O(D³) arithmetic operations per node, allowing all derivative
evaluations without optimization, on at most O(D³W)-bit integers/rationals.

Using schoolbook arithmetic and even an O(v³) allowance for rational/gcd
operations on v-bit operands gives the loose bound
`O((D+1)^16 W^4)` for this root stage; the exponent is an upper allowance,
not an efficiency claim. Polynomial gcd, exact interpolation, threshold
powers, determinant setup, and gap/endpoint evaluations likewise have
polynomial bounds. Consequently, with

\[
 Z=n+d+\lceil\log_2(2A)\rceil+\lceil\log_2(2H)\rceil+2,
\]

one conservative uniform envelope for the entire enumerator is

\[
 \boxed{\quad O((H^2+S_{\rm all})Z^{30})\text{ bit operations}.\quad} \tag{5}
\]

For example the deliberately loose coefficient bound above gives tau=O(Z³),
so the displayed isolation envelope is at most O(Z^28); the extra exponent
allows ordinary sequential array access/copying and the remaining arithmetic.
No conclusion depends on 30 being sharp. In particular this is a
growing-degree polynomial bound, not a fixed-degree real-arithmetic claim.
Under the promised widths, (5) proves the requested form.

A finite deterministic multi-tape implementation keeps the current label,
line polynomial, polynomial sequences, stack and O(d) rational root intervals
on working tapes of polynomial length in Z. All arrays here have polynomial
length; sequential access can add a polynomial overhead already allowed in
(5). Binary label counters cost O(log H) per update. Emit each triple on an
append-only output tape using O(log H) bits. Thus working space is poly(Z),
and full retained output space is `O(S_all log(2H))`, charged if retained.
There is no table indexed by all H² lines, no size-dependent advice, no real
oracle, and no random tape. The validator's materialized lists are diagnostic
memory, not a requirement of the streaming primitive.

Primitive and irreducibility filtering follows emission: gcd(a,b,c)=1 and
the discriminant b²-4ac is not a nonnegative square. These use polynomial
bit work per emitted triple. Computing rational values, checking zero values,
and any gcd with N are charged separately in a downstream consumer. These
filters do not prove that accepted rows are independent or useful.

## 5. Frozen, bounded validation

The [protocol](H014-enumerator-protocol.json) and both sources were written
and hashed **before** execution. The runner refuses to overwrite its evidence.
Exactly one command was run, with a 55-second internal setup/attempt budget
and external 60-second cap:

```
timeout 60s python3 -B research/findings/H014-enumerator-validation.py
```

The complete deterministic grid and criterion are in the protocol. It includes:

- 27 cube cases from N-only ordinary base polynomials of degrees 3,4,5,
  with H in {1,2,3}. Eight use explicitly labeled T=0/1 overrides to exercise
  structural cases; the other 19 use (1). These are not hidden factors or
  favorable family labels supplied to the enumerator.
- In particular N=10^9 and N=10^9+1, d=3,H=1, give **actual** T=0 under
  (1). Both have three zero-resultant outputs. Reducible/repeated f is
  intentional because the primitive promises to handle it; no number-field
  relation claim is made for those cases.
- 17 generic sublevel tests cover constant/zero polynomials, repeated real
  and nonreal roots, integer boundary roots, irrational roots, a rational
  root 2^-30, negative leading coefficients, tangency, and empty clipping.
- The symbolic wide-interval test `(X-10^30)²<=0` on [0,2*10^30] must return
  only 10^30 without scanning the interval. It used 207 isolation nodes,
  depth 103, two gap tests and one boundary test.
- One integer-root case checks 54 input/exponent pairs, including zero and
  values adjacent to exact powers; one case checks explicit nonmonic rejection.

For each cube, the independent reference scans every triple and constructs
the (d+2)-dimensional Sylvester matrix, then uses exact rational Gaussian
elimination. It separately reconstructs the tiny-N base by ordinary integer
search. Every line-polynomial value on the reference cube is compared with
the reference resultant, and complete output sets are compared, including
duplicate detection. Original power acceptance is checked against the floored
threshold in all non-override cases. Reference work is validation cost, never
an input or charged primitive supplied to the candidate.

**Outcome:** 47 pass, 0 failures, 0 errors, 0 timeouts, 0 unstarted; 3.090900
seconds for setup/attempts/evidence before final-summary serialization.
The external command completed successfully within its cap. The 27 cubes
comprised 1,037 reference triples and 2,469 charged candidate labels.
Summed enumeration time was 2.96949 seconds; summed reference comparison time
was 0.09919 seconds. These include different work and are **not** a speedup
comparison. Process peak RSS was 19,268 KiB on Linux, including validation,
reference lists and evidence; native allocation is not separately attributed.

All raw outputs, exact thresholds, counters and statuses are retained in
[raw JSONL](H014-enumerator-raw.jsonl), with the
[summary](H014-enumerator-results.json). There are no losing seeds to omit:
the program is deterministic. No source modification or rerun followed the
screen. [Candidate](H014-enumerator-stdlib.py),
[independent runner](H014-enumerator-validation.py).

This is a finite correctness screen, not machine refinement or independent
review. Tiny-degree admission ratios are deliberately not interpreted: C0's
3^d(d+1) and A² slack can dominate the damping. No density fit, smoothness
siever, matrix, square root, or factoring benchmark was run. Shared project
checks were not run: shared code/Lean were unchanged, and the user's write
scope excludes shared build artifacts. Validation of the owned prototype is
the explicit frozen test above.

## 6. Independently checked population bound used for accounting

This section rederives the nonnegative-f case instead of assuming H013's
unaccepted count. It does not review H013's signed-coefficient extension,
full-scan constant argument, special units, or optional optimization.

For a polynomial P of degree d and leading coefficient L!=0, write
`P(z)=L prod_j(z-z_j)`. If |P(k)|<=T for a real integer k, some root z_j
satisfies `|k-z_j| <= rho=(T/|L|)^(1/d)`: otherwise the product is larger
than T. A disk of radius rho intersects the real axis in an interval of
length at most 2rho, containing at most 2rho+1 integers. Therefore

\[
 \#\{k\in\mathbb Z:|P(k)|\le T\}\le d(2\rho+1).          \tag{6}
\]

This includes rho=0, integer roots, and repeated roots. For (3), L=f(1)²>=A²
and the integer T is no larger than C0 N^(-6/(5d)), so

\[
 \rho\le3H(d+1)^{1/d}(A/f(1))^{2/d}N^{-6/(5d^2)}
 \le6H\epsilon,\qquad\epsilon=N^{-6/(5d^2)}.
\]

Multiply (6) by the label count; restricting a to (4) only decreases it:

\[
 \boxed{S_{\rm all}\le d(6H+1)(4H+1)(1+12H\epsilon).}       \tag{7}
\]

This is a rigorous **upper** bound before filters. It gives no lower bound
even for all outputs, much less primitive irreducible useful rows. The proof
does not locate a single root; Section 3 and its cost analysis do that work.

For the explicitly generalized threshold
`T_eta=floor(C0 N^(-2(1-eta)/d))`, 0<=eta<=1, the same proof gives
epsilon=N^(-2(1-eta)/d²). Rational fixed eta is implemented by integer
powers exactly as in (2), with polynomial widths. With

\[
 D_N=(\log N)^{1/3}(\log\log N)^{2/3},\quad
 \log H=(a_0+o(1))D_N,\quad \log B=(b_0+o(1))D_N,
 \quad d=(\delta+o(1))(\log N/\log\log N)^{1/3},
\]

put Q_eta=2(1-eta). Then (7) gives the upper-population exponent

\[
 s=\max(3a_0-Q_\eta/\delta^2,\;2a_0).                    \tag{8}
\]

Full enumeration has the **sufficient upper envelope** max(2a0,s)=s,
up to polynomial factors. The cost it actually incurs is
`H² poly(n)+S_all poly(n)`, with mandatory Theta(H²) labels and output work.
We must not call L[1/3,s] an actual population, a necessary output cost, or
an available supply. It can be a loose upper bound.

## 7. Changed end-to-end feasibility accounting

Retain Card C's rational bound and its explicit, unproved joint-smoothness
model. The resultant cutoff corresponds to combined norm-size coefficient

\[
 C=K/\delta+a_0\delta,\qquad K=2(1+\eta),\quad
 p_{\rm smooth}\ \hbox{modeled as}\ L_N[1/3,-C/(3b_0)].    \tag{9}
\]

This probability is an assumption about the selected population, not a
consequence of either norm upper bounds or (7). It might fail in either
direction. Correlated cancellation, units, reducibles, or much smaller norms
need their own stratified supply and smoothness analysis.

Let u be the exponent of actual candidates subjected to this model, including
every failed smoothness attempt. Even granting that every success is useful,
the B-scale collection target would require

\[
 u\ge b_0+\frac{K/\delta+a_0\delta}{3b_0},\qquad
 u\le s.                                                   \tag{10}
\]

Any full implementation that touches these candidates has total constant
c>=u. The optimistic conventional completion model adds c>=2b0; the full
line enumeration adds c>=2a0. Upper-population substitution gives a
sufficient *conditional cost envelope* `max(s,2b0)` **only if** enough
useful rows really exist, processing costs polynomial work per attempt,
and all other completion stages fit. No actual lower population is assumed
in the necessary argument next.

### Fixed eta = 2/5 is closed even with the new enumeration cost

Since u <= max(2a0,3a0-Q_eta/delta²), at least one of the following holds.
If u<=2a0, then a0>=u/2. By AM-GM in delta and then b0, (10) implies

\[
 u\ge b_0+\frac{2\sqrt{Ku/2}}{3b_0}
 \ge 2\sqrt{\frac{2\sqrt{Ku/2}}3},
 \qquad u^3\ge\frac{32K}{9}.                            \tag{11}
\]

If u<=3a0-Q_eta/delta², then
`a0 >= (u+Q_eta/delta²)/3` and hence

\[
 K/\delta+a_0\delta
 \ge (K+Q_\eta/3)/\delta+u\delta/3
 \ge2\sqrt{(K+Q_\eta/3)u/3}.
\]

Use (10) and the same second AM-GM inequality to obtain

\[
 u^3\ge\frac{64(K+Q_\eta/3)}{27}.                       \tag{12}
\]

For eta=2/5, K=14/5, Q_eta=6/5. The two lower bounds are 448/45 and
1024/135 respectively. Thus every case satisfies

\[
 \boxed{c\ge u\ge(1024/135)^{1/3}>(64/9)^{1/3}>c_C.}    \tag{13}
\]

Here `c_C=((92+26 sqrt(13))/27)^(1/3)` is the quoted Coppersmith comparison
constant; Lee–Venkatesan's Remark 4.31 states its square-congruence scope.
[Primary source](https://arxiv.org/html/1805.08873v1).

The derivation uses the upper count only to limit the **possible** number of
attempts. It never treats that upper count as a lower cost or as achieved
density. It allows u<s and can even omit line, linear-algebra, ideal, and
root-extraction costs; adding them cannot repair the contradiction inside
the supplied model. Therefore a tiny admission-ratio experiment at eta=.4
cannot establish this proposed global-constant improvement. A different
joint law, collection target, or stratified smaller-norm mechanism is outside
this rejection. Equation (13) is not a factoring lower bound.

### A stronger cutoff has a nonempty optimistic region, not a theorem

For the new eta=1/10 threshold, take the explicit rational parameters

\[
 a_0=153/200,\qquad b_0=189/200,\qquad\delta=21/10.
\]

Then K=11/5, Q_eta=9/5, Q_eta/delta²=20/49, and

\[
 s=3a_0-20/49=18491/9800>2a_0=153/100,
\]
\[
 b_0+\frac{K/\delta+a_0\delta}{3b_0}
 =\frac{189}{200}+\frac{111473}{119070}
 =s-\frac{1343}{238140}<s,
\]
\[
 c_{\rm envelope}=\max(s,2b_0)=189/100<c_C.               \tag{14}
\]

These exact strict inequalities exhibit a nonempty open optimistic region;
there is no numerical optimizer or parameter sweep. This is analysis of
the **changed line enumerator**, not H013's optional full-scan eta
optimization. The cutoff is now `|Res|^(5d) N^9 <= C0^(5d)`, not (1).
The same proved construction handles it; this round's cube validation used
(1), not a separate eta=.1 density experiment.

Equation (14) is worth investigating only as a stronger-tail *supply*
question after independent review. It assumes that the actual useful
population reaches the required attempt exponent and obeys (9). Neither
is known. It is not permissible to label s as that population, use a single
constructed unit as evidence for it, or assume all admitted rows independent.

### Processing, early stopping, and completion remain paid

Let S=S_all and let R be the number of retained relation records. A full
trial still has

\[
 T_{\rm trial}=P_{\rm field/base}+
 O((H^2+S)\operatorname{poly}(n))+
 C_{\rm smooth/ideal}(S)+F(R)+T_{\rm LA}+T_{\rm root}+T_{\rm gcd}.
                                                               \tag{15}
\]

Enumerating primes through B and trial-dividing each nonzero rational value
and resultant by that base gives a conservative integer-smoothness upper
cost `B poly(n)+S B poly(n)`. Failed smoothness candidates cost work too.
This does not yet decompose ideals or solve exceptional-prime issues. Using
the upper population s, the corresponding processing envelope is s+b0,
not s. At the witness (14) it is
`18491/9800+189/200=13876/4900`, about 2.832, well above c_C. No B factor is
removed in this report. A claimed smaller cost needs an explicit charged
sieve/batch method, including aggregate bit lengths, ideal identification,
memory and all failed inputs. This implementation performs none of that work.

Preprocessing must include polynomial/field selection, the factor base, and
any exceptional-ideal/character data. Postprocessing must preserve signs,
square-class constraints and relation provenance, charge filtering/fill and
dependency lifting, and justify sparse linear algebra on the actual matrix.
Roughly quadratic B-scale algebra is an optimistic model when row weights
remain polynomial and the required rank behavior holds. It is not implied
by the count. Algebraic square-root construction and verified proper-factor
gcds still require their own algorithms and bounds.

H008's reducible qualification remains in force. A primitive height-H
reducible quadratic factors into primitive linears u,v with
`H(u)H(v)<=sqrt(3)H`; their possible factors lie in an O(H²) linear square.
This follows from multiplicative Mahler measure and `M(g)<=sqrt(3)H`.
For a common u, parity columns satisfy `R=V+c 1^T`: even dependencies need
the extra even-cardinality condition, while a possible odd coset must be
retained. Thus no rank-at-most-d assertion applies to all emitted reducibles,
and counting such products as independent quadratic opportunities is invalid.
The exact discriminant filter is cheap, but the loss of supply is not known.

A quota/prefix variant can stop after sufficient **verified useful** rows.
It pays every line visited before then, including empty lines, every boundary
operation, and every failed candidate. Without a lower supply/order guarantee
it may traverse all Theta(H²) lines, exhaust the set, and fail the quota.
Output sensitivity gives no bound on time to the first useful row. The
eta=.4 obstruction above still applies to a quota using the same model:
its attempted subset cannot exceed S_all and must pay for its attempts.

Finally, if a completed trial yields a verified proper divisor with probability
sigma_N, an independent-restart expected bound includes T_trial/sigma_N.
There is no lower bound here on sigma_N, on useful rank, or on successful
completion for arbitrary composite N. Favorable f or one special unit cannot
supply the all-input factoring contract.

## 8. Disposition and next decisive work

**Primitive: provisionally proved and finitely validated.** Exact global
sublevel enumeration really can replace the H³ scan by a charged H² line
search plus its full output. Its correctness and polynomial bit accounting
remain informal mathematics awaiting independent review, not Lean refinement.
This is a concrete construction within this project, not a claim of novelty
for univariate semialgebraic enumeration or polynomial root isolation.

**Fixed eta=.4 factoring proposal: still rejected within Card C's model,**
by the new necessary inequality (13), not by repeating H013's full-scan cost.
**Stronger eta=.1 variant: only an optimistic feasibility witness.** Its
missing step is useful global-tail supply jointly with smoothness and paid
processing; the count (7) is in the wrong direction to provide it.

The next decisive action is an independent review of the exact interval
algorithm, normalized remainder bit bounds, fixed-eta rejection and the
strict witness (14). If accepted, pursue a lower-count/correlation theorem
or a falsifier for that stronger threshold before any full siever. Require
separate costed smoothness/ideal processing, rank, algebraic square-root and
splitting arguments before claiming a global constant. No recursive review
or further experiment was launched by this subtask.

Input, source, protocol and evidence hashes, source URLs and failed retrievals
are recorded in [provenance](H014-enumerator-provenance.json). **Verified
factoring complexity improvement remains NONE.**
