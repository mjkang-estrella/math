# H012 independent cost and proof review

2026-10-08. **Verified new factoring improvement: NONE.**

**Disposition:** accept the frozen finite certificate/cover results as sound.
Do not continue the proposed uniform `C(n)=O(n/log n)` claim for the fixed-slack,
per-residue, full-real-interval cover architecture without answering the
obstruction below. A residue-average argument gives an infinite family of
actual semiprimes, with the frozen smooth-modulus rule, for which a positive
fraction of unit residues require **Ω(n)** connected certificate intervals.
This applies even to an unrestricted certificate pool, not just the four
Gauss directions. It does not bound general factoring, adaptive choices among
different moduli, integer-only coverage, or shared processing across residues.

This is a new mathematical derivation in this review, supplied in full for the
parent's next independent proof review. It is not a Lean theorem or a claim of
literature novelty. The finite run remains a pass of its original continuation
criterion; it is not reclassified as an asymptotic experiment.

## Scope and evidence

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, W001-deterministic Card A and its shared
accounting, and all three frozen H012 artifacts. Wrote only this report and
adjacent H012-review-* files. No shared code, Lean, STATE, original protocol,
original source, or original result was changed. No delegation, packages,
commits, publication, or scheduler was used.

The [review preregistration](H012-review-preregister.md) preceded execution of
the [standalone audit](H012-review-audit.py). Its single invocation completed
in 4.439 seconds, within the 55-second internal / 60-second external budget.
[All outcomes](H012-review-audit.json), including every audited row and all 12
new finite rectangle-identity checks, are retained. No failing or unstarted
stage, rerun, or enlarged budget occurred. The frozen `main` and `run_case`
were never called. The original two predicate functions were loaded without
bytecode writes; independent rational quadratic extrema were the oracle.

Checks passed:

- All 96 saved rows; 9,727 distinct row-local certificates from 9,728 generated
  directions; both congruences and every source-cell centering choice.
- Independent reconstruction of the scaled-basis reduction and candidate
  order, including determinant, reduced-basis conditions, source-cell lists,
  the 9,809 recorded Gauss iterations, exact roots, K/H, and cell endpoints.
- All 314,101 saved candidate/cell decisions, including rejected coverage.
- Independent shortest-path dynamic programming for every saved cover count.
- 34,496 signed/degenerate envelope cases, including H=0 and singleton cells.
- 809 small cover pools: 470 coverable and 339 incomplete; the greedy count
  agrees with the independent optimum on all of them.
- All 12 preregistered small-modulus checks of the exact divisor-sum identity
  used below. These check finite algebra, not its asymptotic consequence.

The reported medians are correct: 11/2, 22/2, and 43/4 cells/selected intervals
at 64/128/256 bits. Selected counts range over 1–2, 2–3, and 3–4 respectively.
The corpus is six public odd numbers conditioned on coprimality with m, not six
certified semiprimes. Its 16 residues per input establish no universal or
average-input distribution claim. No matched factorer was tested.

## Construction and exact predicates

For a unit j modulo m, the two certificate congruences imply
`u*j² = N*t (mod m)`. Conversely this condition and

    v = -u*j - N*t*j^(-1) (mod m²)

imply both original congruences. The inverse modulo m² exists. Therefore the
integer (u,t) lattice has precisely the basis `(m,0),(c,1)`,
`c=N*(j²)^(-1) mod m`, and determinant m. Scaling by `diag(C²,N)` gives the
implemented determinant `m*C²*N`. Decoding divisions are exact. Gauss basis
changes are unimodular; b1, b2, and b1±b2 are nonzero. Sign normalization
preserves the relation. A zero coordinate is allowed; only `(u,t)=(0,0)` is
uninformative and excluded.

The exact rational nearest-integer rule, including negative numerators, is
ties upward. For each recorded source C it satisfies

    -m²*C < 2*(u*C²+v*C+N*t) <= m²*C.

The asymmetric strict/non-strict boundary is the correct tie convention.
Deduplication preserves every generating source-cell index.

Put `w=N*t` and `f(z)=u*z+v+w/z`, for z>0. The first predicate checks both
closed endpoints. An interior stationary point exists only when `u*w>0`,
and then `z²=w/u`. When u>0 it is a minimum with value `v+2√(u*w)`;
when u<0 it is a maximum with value `v-2√(u*w)`. The code reverses the
location inequalities correctly for negative u. Its sign tests before
squaring implement both bounds on these radical values without extraneous
solutions. Endpoint equality, a stationary point on a boundary, u=0, t=0,
and a singleton interval all work. N>0, H>=0, and positive endpoints are
essential preconditions; the routine is not advertised outside them.

The second predicate checks

    q_minus(z)=u*z²+(v-H)*z+w <= 0,
    q_plus(z) =u*z²+(v+H)*z+w >= 0.

Only the concave q_minus (u<0) can have an offending interior maximum;
only the convex q_plus (u>0) can have an offending interior minimum. At a
quadratic's vertex the value is `(4*u*w-b²)/(4*u)`. The code's strict test
`4*u*w-b²<0`, together with its respective sign of u, is exactly right in
both cases. When u=0 both polynomials are linear and endpoints suffice.
The independent audit used rational vertex values, rather than either
implementation's square-comparison logic.

Since f has at most one stationary point, its feasible positive-real set has
at most two connected components. Whole-cell runs inherit that bound.
Furthest-right covering is optimal **among these saved whole-cell runs**:
at the first uncovered cell, replacing an optimum's next interval by the
available interval with the furthest right endpoint cannot increase the
remaining requirement. Ties do not affect cardinality. Counting two runs of
one certificate separately is intentional. This does not certify optimality
over all lattice certificates or over intervals with endpoints inside cells.

The integer-factor domain is correctly covered from ceil(cuberoot(N)) to
floor(sqrt(N)). It is a slightly smaller real interval than the irrational
one in the original question; this is harmless for integer factor coverage,
and immaterial to the obstruction, whose test points are strictly interior.
The script is a diagnostic for its registered sizes, not a total small-input
API: an empty cell list would make its final compression-ratio expression
divide by zero. A future factorer must handle that case before this routine.
It does not affect any frozen row or the envelope/cover predicates themselves.

## Why a constant bound on every certificate is false

There is a valid axis direction `(u,t)=(m,0)` for every j, with
`v=-m*j (mod m²)`. Its envelope is linear. Choosing its v near the negative
midpoint value covers an interval of additive length about `2H/m`, up to
the m² rounding error. At the frozen scale this reaches order
`sqrt(N/m)` from the low end. The multiplicative span from N^(1/3) to that
scale is `N^(1/15)` when m≈N^(1/5), hence grows through Θ(n) dyadic cells.
The low-cell Gauss basis actually supplies this axis when `m*C²<N`.

All 32 rows at 128 bits and all 32 at 256 bits select an axis certificate.
Thus even the concrete pool does not support an everywhere constant-reuse
claim. Exceptional non-axis directions are possible too. An obstruction
must leave these regions/directions alone and find sufficiently many hard
residue/scale pairs elsewhere. The following argument does that.

## Analytic obstruction with total-count and input quantifiers

Write `n=bit_length(N)`. Consider the specified representation: for **every**
unit j, cover the entire positive-real factor-size interval by certificates
with the two H012 congruences, `(u,t) != (0,0)`, and `|f(z)|<=H` throughout
each chosen component. Count components, or distinct certificates separately
per residue; these counts differ by at most a factor two.

**Claim.** For every sufficiently large initial primorial m there are distinct
primes p,q with

    m^(5/2) <= p,q <= 2*m^(5/2),  N=p*q,

such that H012's own modulus rule returns exactly m, and its own
`K=16*ceil(sqrt(N/m³))` has the following property: any such complete cover
requires `sum_j C_j = Ω(phi(m)*n)`. Moreover at least a fixed positive
fraction of unit j individually require `C_j=Ω(n)`. The constants are
absolute, although deliberately very loose. This holds for arbitrary
certificate pools and arbitrary v choices, not just the frozen generator.

### 1. Necessary rectangles

For `[P,rP]`, set `s=√r`. Evaluate f at `P,sP,s²P` and eliminate v and one
of u,w. The resulting bounds, valid for either sign of u or t, are

    |u| <= 2H / (P*(s-1)²),
    |t| <= 2s²*H*P / (N*(s-1)²).

For example the linear combination with weights `1,-(s+1),s` eliminates
v and w and has u coefficient `P*(s-1)²*(s+1)`; its absolute value is at
most `2(s+1)H`. The reverse weights give the t bound. No cancellation or
sign assumption is hidden here.

For all N in `[m⁵,4m⁵]`, the frozen ceiling gives

    H <= 32*sqrt(N*m) <= 64*m³,    H/N <= 64/m².

Thus any certificate covering that interval lies in the symmetric rectangle
with half-widths

    U(P)=128*m³ / (P*(s-1)²),
    T(P)=128*s²*P / (m²*(s-1)²),
    U(P)*T(P)/m = 16384*r/(sqrt(r)-1)^4.

These enlarged rectangles are independent of the actual N within this
range. This uniform enlargement is crucial when subsequently choosing N.

### 2. An exact average over unit lattice slopes

For c uniform among units modulo m, let Z_c(U,T) count pairs

    0<|u|<=U,  0<|t|<=T,  u=c*t (mod m).

Define `A_q(X)=#{a in Z: 0<|a|<=X, gcd(a,q)=1}`. An exact identity is

    E_c Z_c(U,T)
      = sum_{d|m} A_(m/d)(U/d)*A_(m/d)(T/d) / phi(m/d).       (1)

Indeed a possible pair has `gcd(u,m)=gcd(t,m)=d`. Write `u=d*a,t=d*b`
and `q=m/d`. Both a,b are units modulo q. The required c has exactly one
unit residue modulo q, which lifts to `phi(m)/phi(q)` units modulo m.
This proves (1), including nonprimitive pairs; treating every pair as
having probability 1/m would not be valid.

Here is the uniform asymptotic estimate needed, with proof. For fixed
epsilon>0 and fixed B, assume

    m^epsilon <= U,T <= m^(1-epsilon),   U*T <= B*m.

Then

    E_c Z_c(U,T) <= 4*U*T/m + o(1),                          (2)

uniformly over these rectangles as m grows. Inclusion-exclusion gives
`A_q(X)=2X*phi(q)/q+O(2^omega(q))`. Use
`tau(m), 2^omega(m), m/phi(m)=m^o(1)`; the last also follows from
`m/phi(m)<=2^omega(m)`. Split (1) at `d=D=m^(epsilon/2)`.

For d<=D, the sum of the main terms is at most

    (4UT/m²) * sum_{d|m} phi(m/d) = 4UT/m.

The mixed-error sum is bounded by
`m^o(1)*(U+T)/m=o(1)`, and the squared-error sum by
`m^o(1)*D/m=o(1)`. For d>D use `A_q(U/d)<=2U/d`, and similarly for T,
and `1/phi(m/d)<=m^o(1)*d/m`. Its contribution is at most

    (4UT/m)*m^o(1)*sum_{d|m,d>D}1/d
      <= O(1)*m^o(1)/D = o(1).

This proves (2). The estimate does not need an unproved distribution of
continued fractions or quadratic residues, or a squarefree restriction.
The finite identity screen checks (1), not (2)'s limiting argument.

### 3. Hard points for most residue/scale pairs on average

Fix once and for all `r=2^32`, and use the dyadic test points

    Z = {2^k : m^(17/8) <= 2^k <= m^(19/8)}.

Their number is `h=(1/4)*log2(m)+O(1)=Theta(n)`. Every point lies well
inside the required factor-size domain for all N in `[m⁵,4m⁵]`.

For each z call a unit slope c **soft** if either necessary rectangle for
`[z/r,z]` or `[z,r*z]` contains a nonzero lattice pair. All four half-widths
are, for sufficiently large m, between `m^(1/16)` and `m^(15/16)`.
For fixed r the products are fixed constants times m. Equation (2) and
the union bound give

    Pr_c[soft at z] <= 131072*r/(sqrt(r)-1)^4 + o(1)
                     < 1/1000

eventually, uniformly in z. The numerical constant is about 0.00003052
before the o(1). Axis pairs cannot evade this: U,T<m, and c is a unit,
so t=0 would force |u|>=m and u=0 would force |t|>=m.

For an input residue `a=N mod m`, the slope for j is `c=a*j^(-2) mod m`.
For each fixed unit j, multiplication by `j^(-2)` permutes the possible
unit a. We average over a, **not** assume that the squares of j are
uniform over all units. Hence, if S(a) counts soft pairs (j,z),

    E_a S(a) <= phi(m)*h/1000.

By Markov's inequality, all but at most `phi(m)/500` values of a have
`S(a)<=phi(m)*h/2`. For each such good a, at least half of all (j,z)
pairs are hard, meaning neither subinterval is possible for any certificate.

### 4. Good residues occur for genuine post-sieving semiprimes

It is not enough to choose a formal lattice slope or a composite with a
small easy factor. Put `X=m^(5/2)` and fix a prime q in `[X,2X]`. For large
m there are `(1+o(1))*X/log X` primes p in that same interval. The
Brun–Titchmarsh bound gives, for every unit b,

    #{p in [X,2X]: p=b (mod m)}
        <= (2+o(1))*X / (phi(m)*log(X/m)).

Consequently the fraction of these primes in any particular residue is
at most `4/phi(m)` eventually, since
`2*log X/log(X/m)=10/3`. Multiplication by q permutes residues. The
exceptional set of at most `phi(m)/500` bad a therefore contains at
most 4/500 of the choices for `a=p*q mod m`. Choose a remaining p and
exclude the single choice p=q. Thus N=pq is a genuine distinct-prime
semiprime with good a; both factors exceed N^(1/3).

The progression upper bound is the classical Montgomery–Vaughan
Brun–Titchmarsh inequality, checked directly as stated at the start of
[Ford's sieve paper](https://www.ford126.web.illinois.edu/wwwpapers/sigphi.pdf).
Only an upper bound is used; equidistribution for this growing modulus is
not assumed. Ford's displayed prime-counting estimates also suffice for
the total count of primes in `[X,2X]`. The original Montgomery–Vaughan
publisher PDF redirected to an abstract and returned HTTP 403 on direct
download; I do not claim to have read that inaccessible PDF.

Finally, `m <= floor(N^(1/5)) < 2m`. Since m is an initial primorial, the
next primorial exceeds 2m, and no doubling of m fits. The frozen modulus
rule therefore returns this exact m. Coprimality with N holds. This is
an infinite admissible input/modulus family, not an independently chosen
unrealizable congruence or just a single difficult j.

The same transfer also supplies unbalanced examples: take p in `[m²,2m²]`
and fix a prime q in `[m³,2m³]`. The per-residue prime-density constant is
then eventually less than 5, so at most 5/500 of p choices have a bad product
residue. All other parts of the proof are unchanged; both factors still
exceed N^(1/3), and now p=Theta(N^(2/5)). Thus the obstruction is not
peculiar to balanced semiprimes.

### 5. Count components and certificates

If a valid connected component `[L,Q]` contains a hard point z and has
`Q/L>=r²`, either `z/L>=r` or `Q/z>=r`. It therefore contains `[z/r,z]`
or `[z,r*z]`, a contradiction. Every component covering a hard point
has ratio <r² and contains at most `2*log2(r)+1=65` dyadic test points.

For the good a just obtained, any complete cover thus satisfies

    sum_j C_j >= phi(m)*h/130 = Omega(phi(m)*n).

At least one third of unit j have at least h/4 hard points: otherwise
the total hard count would be less than `phi(m)*h/2`. Each of those j
needs at least h/260 components. A single certificate has at most two
components, so counting distinct certificates per residue instead
changes only a factor two. **This refutes a uniform O(n/log n) bound
and its corresponding total-count bound for this representation.**

### Exact limitations and relation to the rebalanced m

This is a lower bound on the **per-residue full-range representation**.
It is the sum of selected certificate records that W001 uses for its
giant-step budget. It is not a lower bound on distinct modular giant
values after arbitrary cross-residue deduplication. A certificate can
work for several j, and different exponents can yield the same residue.
Any revised shared representation must price its metadata, detection,
and collision extraction. The current proposal supplies no such method.

The proof supplies both balanced and unbalanced semiprimes; it does not
claim they are difficult to factor. A factorer given either family's
factor-size promise only needs a constant-ratio interval about the relevant
power of N and is outside this full-range cover lower bound. A general
algorithm that adaptively stops, proves many
residue/size pairs impossible, or first succeeds on a balanced subproblem
may also avoid constructing the full cover. Those are different obligations.

The counting proof is not confined to m exactly N^(1/5). Replace
`X=m^(5/2)` by any `X=m^(5/2+o(1))`, take primes in `[X,2X]`, and replace
the test-point band by `[X*m^(-3/8), X*m^(-1/8)]`. With `H<=A*sqrt(N*m)`
for any fixed A, the same rectangle proof works after changing the fixed r.
Brun–Titchmarsh still has a bounded residue-density constant. Thus logarithmic
rebalancing alone does not remove the geometric obstruction for a prescribed
m. For the usual primorial-and-doubling rule applied to a target
`N^(1/5)*L(N)` with the proposed logarithmic factors, choose X so that the
target at X² is, for example, 1.1m. Its value at 4X² is eventually below
2m; the same modulus is then selected throughout that prime-product window.
This uses those explicit, slowly varying logarithmic targets, not an arbitrary
function with an unproved regularity property. An adaptive search over many
different m is not obstructed by this argument and would need a new paid
construction theorem.

The proof allows exceptional broad directions and proves no bound on every
individual component. Continued-fraction geometry may describe the exceptions,
but no conjecture about bounded partial quotients for smooth denominators is
needed. This is substantially sharper than a small rectangle area being
mistaken for a pointwise lattice-emptiness theorem.

## Costs and recovery obligations

Let L=Theta(n) be the number of cells, A<=4L the pool size for one residue,
and M(n) the cost of O(n)-bit multiplication. Coefficients and all individual
envelope/reduction operands have O(n) bits. Python integers do not overflow,
but their operations are not constant cost.

The saved `selected_peak_bits` measures only two squared basis norms per
Gauss iteration. Its maxima are 151/306/613 bits. It omits later dot products,
rounding numerators, inverses, centering, envelope squares, and allocation.
The audit independently observed maxima 86/170/340 bits for its selected
envelope expressions. Neither set is a full peak-memory or bit-cost meter.
For example the initial norm can be order `(m*C²)²`, explaining approximately
2.4n norm widths; O(n) width does not make each operation O(1).

- **Generation:** L independent Gauss reductions and 4L decoded directions,
  plus inverses, exact centering, hashing, and deduplication. Classical
  two-dimensional Gauss reduction has O(n) iterations on these O(n)-bit
  inputs. Charging ordinary quadratic multiplication/division gives a safe
  O(n³) bound per reduction and O(n⁴) per residue. A faster proved reduction
  implementation can change this bound; the current timings do not supply it.
- **Certification:** A*L=O(n²) candidate/cell pairs; each invokes both
  predicates. This is O(n²) substantial arithmetic operations, not O(n²)
  bit operations. With fast arithmetic it is O(n² M(n)); a conservative
  schoolbook estimate is O(n⁴) bit work per residue. The script has no
  maximal-interval or endpoint-sorting implementation.
- **Selection:** constructing runs scans O(A*L) saved coverage entries.
  Each actual envelope supplies at most two runs, so the available list
  has O(A) runs. The implemented repeated full scan takes O(A*C_j), at
  worst O(n²), comparisons on O(log n)-bit cell indices. Greedy correctness
  does not make this implementation linear.
- **Storage and timing:** the prototype retains all row pools and coverage
  lists, O(A*L) integer indices per row, rather than streaming residues.
  Its 0.383-second figure stops before final JSON serialization and disk
  output. Memory is not measured. Those exclusions do not affect the finite
  certificate assertion but matter to any full-work comparison.

For the counterfactual `C=n/ell`, `ell=log n`, the selected-collision term per
residue is about n⁴/ell. An n³-per-candidate implementation leads to n⁴
generation and does not establish the advertised logarithmic saving.
Conversely, O(n²) all-cell certification is not by itself an impossibility:
with a supplied fast-arithmetic implementation, `n² M(n)` can be below
n⁴/ell. Faster maximal-interval arithmetic could also reduce certification,
but no such code/bound is part of H012 and none is silently credited here.
In any case faster preparation cannot overcome the interval-count obstruction
while retaining the same uniform full-cover claim.

The downstream identity is sound. The two congruences make

    g(x)=[u*(m*x+j)²+v*(m*x+j)+N*t]/m²

an integer polynomial. If p|N, p=m*x+j, and gcd(p,m)=1, then p|g(x), so
`i=(u*p+v+t*(N/p))/m²` is an integer. For prime p and unit alpha, Fermat
gives `alpha^(u+v+N*t) = alpha^(m²*i) (mod p)`. Recovery solves

    u*p²+(v-i*m²)*p+N*t=0.

This is nonzero when `(u,t)!=(0,0)`. The u=0 case is a valid linear
recovery problem; t=0 gives a quadratic with a discarded zero root.
Every proposed factor must still be tested. A collision with the wrong i
need not factor N, and exact equality modulo N must retain all associated
certificate metadata. A product gcd equal to N requires localization and
recovery, not acceptance as a proper factor.

For the signed baby range [-K,K], the stride preparation must cover differences
through **2K**, not just K; this only changes constants. Charge the known
factor-or-stride-order preparation, small-factor reduction, exponentiations,
sorting, polynomial products/evaluation, gcds, and collision extraction. The
shared conservative `O(G*n³+K*n²)` search model and packed polynomial widths
`O(d*(n+log d))` remain relevant; O(n)-bit certificate coefficients do not
make a degree-d polynomial an O(n)-bit operand. The safe collision-tree
memory bound `O((G+K)*n*log(G+K))` is still exponential at these parameters.

For clarity, the counterfactual cost balance in W001 is algebraically correct:
with `phi(m)=O(m/ell)`, `G=O(phi(m)*C)`, and
`K=O(sqrt(N)/m^(3/2))`, its search term is

    O(m*C*n³/ell + sqrt(N)*n²/m^(3/2)).

Balancing gives `m ~ N^(1/5)*(ell/(C*n))^(2/5)` and search cost
`O(N^(1/5)*n^(13/5)*(C/ell)^(3/5))`. Only if a uniform, paid
`C=O(n/ell)` cover existed would this yield
`O(N^(1/5)*n^(16/5)/ell^(6/5))`: one additional ell^(3/5) saving over
the general reference. Pool generation/selection and the small-factor/order
terms must be added, not absorbed without their bounds. This would change
neither the N exponent nor establish a GNFS gain or polynomial bit complexity.

## Direct literature check and next action

[Harvey–Hittmeir, 2105.11105](https://arxiv.org/pdf/2105.11105), Theorem 1.1,
gives the general deterministic `O(N^(1/5)*n^(16/5)/(log n)^(3/5))` bound.
Its reduction to prime/semiprime inputs and Remark 4.5 were checked directly;
the latter identifies the collision stage as a bottleneck even when lattice
reduction is accelerated. This is the relevant general reference, not GNFS.

[Gao–Feng–Hu–Pan, 2512.19076v1](https://arxiv.org/html/2512.19076v1),
Theorem 1.1, states the balanced-semiprime `n^(13/5)` variant. Algorithm 4.3
and Algorithm 4.8 require a given constant-ratio interval for p. Algorithms
4.6 / Proposition 4.7 explicitly handle the m² stride with known
factorization of m, at the stated cost
`O(N^(1/6)*n²/sqrt(log n)+sqrt(k)*n³)`. These statements and the collision
cost analysis were read directly; they are not a proof of H012's compressed
cover. The v1 result should not be relabeled as an all-input improvement.

**Next action:** have the parent obtain a fresh independent mathematical review
of (1)–(2), the hard-point charging argument, the Brun–Titchmarsh transfer to
actual semiprimes, and the exact count/representation scope. Do this before a
larger scaling sweep or additional Lean work. If the argument survives, close
the fixed-slack uniform full-range reuse lead. Reopen only for a concrete
change that escapes a named hypothesis—e.g. paid cross-residue sharing or
an adaptive factor-size search—with its own uniform correctness and full-cost
claim. A focused Lean extraction invariant remains useful algebra, but cannot
supply a missing fast cover. No empirical extrapolation is needed for this
disposition, and no factoring lower bound follows.

## Evidence hashes

Originals, independently checked against the report and embedded hashes:

    certificate_reuse.py  181e97caeef68b373b639fdb3f510b0811a7c902eb83e2f6ca1ea13cb04f0f13
    H012.md               17f456aa1727cff5657d7de00e66251bce3d4b27e2de2d09b5574956c00bc456
    result.json           77b7d6573586a7eda648473c1cb850ee35bbb3f9fff6a269ecc70e59378f9a07

New review evidence:

    H012-review-preregister.md  3b6dd46a7c10e911aef0736fe689909f99ee83a3b3cbba7017ca43bca1ebf16f
    H012-review-audit.py        98e08a61ab8f0e29762cf4f0ff6cced709421fa8c215827dcdba99dd58723d06
    H012-review-audit.json      84c5a6c51db81afbe0e3239bd3cfa2fc69712f8247d2ab731d442e0ead67778b
