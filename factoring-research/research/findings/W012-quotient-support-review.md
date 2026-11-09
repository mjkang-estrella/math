# W012 quotient/support review

2026-10-08. Independent review of Cards A and B of the frozen parent proposal.
Disposition: **accepted as exact reductions, with implementation and residue-scope
qualifications; global query-count gain unproved**. Verified factoring complexity
improvement: **NONE**. No candidate experiment, parameter sweep, optimization
implementation, package installation, shared code/Lean/state edit, delegation,
commit, or publication was performed.

The parent remains the principal researcher. This review does not import W011's
dynamics envelope. Card C's literature, full-hull bounds, clipped arcs and
navigation algorithms are assigned elsewhere and are not independently audited
here. In particular, no full-hull lower bound is used against adaptive queries.

## Findings that affect the proposal

1. Card A is correct for every positive modulus, including `m=1`, every unit
   residue, signed basis entries and signed factor pairs. The orientation
   `u1*t2-u2*t1=m` is essential to the displayed signs. The image is exactly one
   affine lattice of index `m^3`, not a strict subset still needing a free sieve.
2. Card B's strict exclusion and midpoint termination are correct for the
   unrestricted query. The exact polynomial-time query is supported by the
   primary Khachiyan--Porkolab theorem. Its proof is an algorithmic bit-complexity
   result, not an assertion that a convenient solver is installed here.
3. Exclusions must be clipped to the queried interval. For a query restricted
   to `L_j`, they exclude only factor candidates in residue `j`; infeasibility
   has the same residue-specific scope. Erasing that interval for all residues
   would be unsound.
4. After the midpoint gcd fails to find a factor, `gcd(N,h)=1`, so the proposed
   normalization `g=gcd(N,h^2)` equals 1. Actual baseline queries use
   `a=N, b=h^2`; their continuous optimum is the integer `2Nh`.
5. After both gcd checks fail, the objective gap satisfies the stronger sharp
   bound `delta=s-2Nh>=h`, rather than just `delta>=1`. This still gives no
   uniform improvement in the number of integer candidates removed.
6. There is an infinite, exactly proved family of odd nonsquare composites and
   admissible central intervals for which one midpoint query removes **exactly
   one integer**, its optimizer gcd is 1, and there are no integral quadratic
   boundary points. Thus the one-integer local guarantee is sharp. This is not
   a lower bound on the number of queries on any complete execution, and does
   not obstruct an amortized or batched improvement.

## A. Exact lattice audit

### A1. Domain and coefficient lattice

Use integers `N`, `m>=1`, with `gcd(N,m)=1`, and an integer `j` satisfying
`gcd(j,m)=1`. Positivity of `N` is unnecessary for this part. For Card B require
`N>1`. Negative representatives of a residue and negative basis entries are
allowed. A signed modulus should first be replaced by its absolute value;
modulus zero is outside the construction.

For `m>1`, the homomorphism

    Z^2 -> Z/mZ,  (u,t) -> u*j^2-N*t

is onto because `N` is a unit. Its kernel `Lambda_j` therefore has index, and
positive covolume, `m`. Explicitly, let `c` be the residue `j^2*N^(-1) mod m` in
`[0,m-1]`. The rows `(1,c),(0,m)` form an oriented basis: the congruence is
equivalent to `t=c*u mod m`. This also supplies a direct polynomial-bit
construction, without factoring `N` or `m`. Reduction is optional and payable.
For `m=1`, take `c=0`; the lattice is `Z^2`.

Let `B=[[u1,t1],[u2,t2]]` be any such basis with determinant `m`. An arbitrary
independent pair of rows in `Lambda_j` is not sufficient: it may span a proper
sublattice. The determinant condition rules this out.

### A2. The two congruences for each row

For `m>1`, `j` is also a unit modulo `m^2`, so

    v = -(u*j^2+N*t)*j^(-1)  (mod m^2)

exists uniquely as a residue. Reducing modulo `m`, membership of `(u,t)` gives

    v*j = -2*u*j^2  (mod m),  hence v=-2*u*j (mod m).

This proves the derivative congruence without dividing by 2; even and
non-squarefree moduli cause no exception. For `m=1`, both congruences are
vacuous and there is exactly one residue modulo 1. Every integer representative
`v` is permitted. Shifting a representative by `m^2` times an integer is harmless.

Conversely, the two original congruences imply `N*t-u*j^2=0 mod m` by
substituting the derivative congruence into the value congruence. Thus the
projection of the certificate lattice onto `(u,t)` is exactly `Lambda_j`,
not a larger or smaller lattice. Its fibers in `v` have spacing `m^2`.

The construction depends on the residue of `j` modulo `m`, despite using a
lift in the formula modulo `m^2`. Indeed, with
`f(X)=u*X^2+v*X+N*t`,

    f(j+m*k)=f(j)+m*k*(2*u*j+v)+u*m^2*k^2.

Both the value and derivative conditions persist after any change of lift.

### A3. Integral quotient coordinates

The same Taylor identity gives `f(P)=0 mod m^2` whenever `P=j mod m`.
If `P*Q=N` then

    P*(u*P+v+t*Q)=f(P).

As `P` is a unit modulo `m^2`, `m^2` divides `u*P+v+t*Q`. This applies to
negative `P,Q` as well. More strongly, exact equality `P*Q=N` is unnecessary:
`P*Q=N mod m^2` already gives the divisibility. For `m=1` it is automatic.

### A4. Inverse map, signs and image determinant

In vector notation, `m^2*i=B*(P,Q)^T+v`. Since `det B=m`, inversion gives
exactly the parent's formulas:

    P = m*(t2*i1-t1*i2) -(t2*v1-t1*v2)/m,
    Q = m*(-u2*i1+u1*i2)+(u2*v1-u1*v2)/m.

The constants are integers: modulo `m`,

    t2*v1-t1*v2 = -2*j*(u1*t2-u2*t1) = 0,
    u2*v1-u1*v2 = 0.

Thus this is an injective affine map `T: Z^2 -> Z^2`, with linear part

    M=m*[[t2,-t1],[-u2,u1]],   det M=m^2*det B=m^3.

Its image `S` is an affine lattice of index `m^3`. There is no requirement that
the entries of the basis or constants be positive. If a basis has determinant
`-m`, reorder its rows and the corresponding `v,i` before using these formulas;
substituting it unchanged into formulas with denominator `m` is wrong. In the
unoriented formula the denominator is the actual determinant `D`, and the
linear numerator is `m^2*adj(B)`.

### A5. Equality with the proposed set L_j

For `m>1`, choose a lift `J=j mod m` and an integer `q0` such that
`J*q0=N mod m^2`. Such `q0` is obtained by one extended-Euclidean inverse.
Every point with the two prescribed mod-`m` residues is uniquely

    P=J+m*r,   Q=q0+m*s,   r,s in Z.

Its product congruence is equivalent to

    q0*r+J*s=0 mod m.

If `c0=-q0*J^(-1) mod m`, the whole proposed set therefore has parameterization

    (P,Q)=(J,q0)+r*(m,m*c0)+t*(0,m^2),  r,t in Z.

It is a nonempty affine lattice with determinant `m^3`. Notice that this proof
counts the one correlated lift condition, not two independent marginal tests.

By A3 every point of this set has integral quotient coordinates, hence belongs
to `S=T(Z^2)`. The two nonempty affine lattices have the same finite index, so
this containment is equality. This proves both directions of the image claim.

For `m=1`, `L_j=Z^2` with all congruences vacuous, and `T` is an integral affine
unimodular map; the assertion holds with determinant 1. No inverse convention
for the zero ring is needed. Changing `v` by `m^2*k` merely replaces `i` by
`i-k` in the map and preserves its image. All index pairs are already in `L_j`;
the unspent condition remains the nonconvex equality `P(i)*Q(i)=N`.

### A6. Bit sizes

For the explicit basis in A1 and `0<=v_i<m^2`, all basis entries are at most
`m` in magnitude, entries of `M` are at most `m^2`, and the integral translation
has magnitude `O(m^2)`. Extended gcd and fixed-size integer arithmetic construct
these in time polynomial in the input bit lengths. Reducing `N` and `j` before
the modular computations bounds intermediates as well.

For an arbitrary chosen basis and arbitrarily shifted `v_i`, count their actual
encoding lengths. Correctness tolerates enormous representatives; a
`poly(log N)` cost claim does not. No useful short-quotient bounds or cheap
choice of residue follow from this affine-bijection proof.

## B. Support query correctness and complete baseline

### B1. Feasible set and exact primitive

For integers `2<=L<=U<=isqrt(N)`, the set

    C={L<=x<=U, 1<=y<=N, x*y>=N}

is compact and convex: on `x>0` it is the epigraph of the convex function
`N/x`, intersected with four halfspaces. It has an integer point, for example
`(L,ceil(N/L))`. Positive `b` ensures that an unrestricted integer optimizer
uses `y=ceil(N/x)`. An interval with `L>U` is empty and must be skipped.

For a lattice query use `T` from A4 and optimize on `T^(-1)(C) intersect Z^2`.
The real preimage is convex and bounded because `T` is an invertible affine
map. Its integer points can be empty; the primitive must report infeasibility
as well as return an exact optimum and an attaining integer point when nonempty.

To fit a coordinate-minimization theorem, introduce `z=a*P(i)+b*Q(i)` and
minimize `z` over integer `(i1,i2,z)`, with the five inequalities defining `C`.
This is a convex, quantifier-free semialgebraic set in dimension 3, degree at
most 2, with a constant number of predicates. The affine equality leaves it
lower dimensional, which is allowed. Replacing each nonstrict inequality by
`(<) OR (=)` needs at most 11 atomic predicates including the objective
equality. The ordinary query uses `(x,y,z)` in the same way.

### B2. Primary theorem audit and its application

Primary source: Khachiyan and Porkolab, *Integer Optimization on Convex
Semialgebraic Sets*, Discrete & Computational Geometry **23** (2000), 207--224.
[Publisher PDF](https://link.springer.com/content/pdf/10.1007/PL00009496.pdf).
The frozen PDF's printed DOI is `10.1007/s004549910014`; its retrieval URL uses
`PL00009496`. They identify the same inspected document, not two sources.

Theorem 1.2, printed p. 208, gives time

    ell^O(1) * (r*d)^(O(k^4) * product_i O(n_i))

and separately bounds Boolean-formula evaluations, for a convex set described
by a first-order real formula. Here `ell` bounds coefficient bit length, `r`
counts atomic predicates, `d` is degree, `k` is the number of free variables,
and `n_i` are quantified-block dimensions. The empty product is 1. Theorem 1.1
bounds an optimal integer solution's encoding when one exists. Section 4,
printed pp. 222--223, reduces optimization to feasibility by binary search,
constructs rational rounding, and handles deficient dimension explicitly.
Thus this is a bit-length-sensitive algorithm, not a unit-cost optimization
oracle. These statements were read in the primary text and checked against
rendered pages 2, 16 and 17 of the PDF.

Application here (this review's reduction): B1 has `k=3,d=2,r<=11`, no quantified
variables, and a constant-size Boolean expression. Consequently the paid query
cost is `ell^O(1)` bit operations. The theorem applies to the convex **set**;
the polynomial `N-P*Q` need not itself be globally convex or quasiconvex. One
cannot replace the region by `P*Q=N` and retain convexity in general.

With bounded representatives from A6, coefficient lengths are

    ell=O(log(N+1)+log(m+1)+bitlen(a)+bitlen(b)).

All constants, transformed quadratic coefficients, objective coefficients and
the cost of constructing them count. A general basis adds its and `v`'s actual
bit lengths. For the midpoint rule `a,b<=N`; if `log m=O(poly(log N))`, these
inputs are polynomial in `log N`. The polynomial degree and implementation
constants are not numerically specified by this review. No optimizer was
installed, implemented, timed or called; the certificate script is not one.

### B3. Exclusion, exact integer endpoints and boundary cases

For every factor `P` whose point `(P,N/P)` is feasible for the queried set,

    a*P+b*N/P >= s,
    R(P):=a*P^2-s*P+b*N >= 0.

Multiplication by `P>0` preserves the inequality. Hence precisely the strict
negative region of `R` is certified factor-free within that query's scope.
With `D=s^2-4*a*b*N`, the identity

    4*a*R(X)=(2*a*X-s)^2-D

gives a robust integer formula. If `D>0`, put `t=isqrt(D-1)`. The strict
negative integer region is exactly

    ceil((s-t)/(2*a)) <= X <= floor((s+t)/(2*a)).

Intersect this with `[L,U]`. Integer ceil/floor division handles signs exactly.
If `D<=0`, there is no strict negative region. In a valid nonempty query with
positive `a,b`, AM--GM also implies `D>=0`; a negative computed value signals
bad input or an incorrect optimizer rather than a useful exclusion.

Boundary candidates exist only if `D` is a square and `(s+sqrt(D))/(2a)` or
`(s-sqrt(D))/(2a)` is integral. Include both signs and deduplicate if `D=0`.
Check each relevant integer candidate by gcd or division; equality `R(P)=0`
alone does not prove that `P` divides `N`. A failed boundary candidate need not
be deleted for termination, but any deletion must follow a valid divisibility
check. Never exclude equality just by rounding the open interval outwards.

For any returned optimizer `(x,y)`, check `d=gcd(x,N)` and return it only when
`1<d<N`. This may succeed even if `xy>N`. Indeed `R(x)=b*(N-xy)`, so an optimizer
strictly above the hyperbola lies inside the exclusion region; that is
consistent with a proper gcd that is smaller than `x`.

### B4. Midpoint strictness and algorithm

For a nonempty current interval, choose the integer midpoint
`h=floor((L+U)/2)`. It satisfies `2<=h<=isqrt(N)<N`. A nonunit gcd with `N`
therefore immediately gives a proper factor. Otherwise `gcd(N,h)=1` and
`gcd(N,h^2)=1`, so use `a=N,b=h^2`.

For every positive `x` and `y>=N/x`,

    N*x+h^2*y-2*N*h
      >= N*(x-h)^2/x >= 0.

Equality in both inequalities requires exactly `x=h,y=N/h`. This point is in
the real feasible set, including when `h` is an endpoint or `[L,U]` is a
singleton. It is not an integer point when the gcd has failed to find a factor.
Because the integer feasible set is finite and nonempty, its minimum is
strictly larger than `2Nh`. Write

    s=2Nh+delta,  delta an integer >=1.

Then

    R(X)=N*(X-h)^2-delta*X,  R(h)=-delta*h<0.

There is a stronger useful bound for an unsuccessful query. Let `(x,y)` be a
returned optimizer after its gcd also fails, and put `r=xy-N`. Then `r>=1`:
`r=0` would make `x` a proper factor. For `d=x-h` the exact identity gives

    delta*x=N*d^2+h^2*r,
    (delta-h)*x
      =(N-h^2)*d^2+h^2*(r-1)+h*d*(h*d-1) >= 0.

Here `N>=h^2`, and the last term is nonnegative for every integer `d`: either
`d<=0` or `d>=1`, with `h>=2`. Thus **delta>=h**. Equality forces `d=0,r=1`
and occurs in C's family. This improves the normalized objective-gap bound,
but not the universal integer-removal guarantee. If the optimizer gcd succeeds,
no such lower bound is needed; the query has already produced a factor.

Thus the clipped strict integer range `[A,B]` contains `h`. After checking
the optimizer gcd and integral boundaries, replace `[L,U]` by the nonempty
members of `[L,A-1]` and `[B+1,U]`. These intervals are disjoint, preserve every
undetected factor candidate and contain at least one fewer integer in total.
An infeasibility response for the ordinary query is an error, since B1 gave
an explicit feasible integer point.

Starting from `[2,isqrt(N)]`, there are at most `isqrt(N)-1` support calls and
the same order of queue operations. For composite `N` the queue cannot empty
without finding a factor: a least factor lies in the initial interval and
cannot have been correctly excluded. This proves an all-composite splitter
with `O(sqrt(N))*poly(log N)` bit cost when the paid theorem algorithm is used.
There is no stronger global query bound in this review.

An explicit output-size check is `s<=N*h+h^2*ceil(N/h)<=2Nh+h^2`, so `s` and
the quadratic discriminant have `O(log N)` bits. Each remaining child interval
has at most half its parent's candidate count, since the exclusion contains
the midpoint. A depth-first queue therefore uses `O(log N)` stored intervals;
this controls storage without changing the worst-case number of queries.

Even and square checks are useful polynomial-bit preprocessing, but logically
optional for this splitter's correctness: the queue proof already covers them.
Primality testing is unnecessary under a composite promise. For a complete
factorization procedure on general input, handle `N<=1`, primality, exact
division and recursive splitting explicitly and pay their costs. A factor
tree has `O(log N)` nodes; this does not turn the stated exponential-in-bit-
length splitting bound into a polynomial one.

### B5. Residue scope and all-input cost

For a nonempty lattice query, the same strictness argument works: its integer
points are a subset of the ordinary query's and cannot attain the nonintegral
real minimum. But only factors with `P=j mod m` were feasible for it. Its
exclusion or infeasibility cannot be used to remove other residue classes.

A complete variant can maintain a separate residual candidate set per unit
residue and choose a midpoint **among that residue's remaining integers**.
If no such integer remains, skip the interval for that residue. Then a failed
query removes at least one relevant candidate. Empty affine-lattice queries
exclude the entire queried interval for that residue. The upper cap `y<=N`
does not lose genuine factors, even if it makes a particular class empty.

Selecting `m`, checking `gcd(N,m)`, constructing bases, generating unit residues,
all queries and all failures are paid work. Literal scanning of residues
`0..m-1` costs `m` gcd tests, not just `phi(m)` idealized visits. A cheap useful
subset of residues is not given by the lattice theorem. If a chosen `m` has a
proper gcd with `N`, that is an ordinary successful preprocessing factor;
otherwise the hypotheses for the desired unit-residue construction must hold.

There are at most `phi(m)*(ceil(isqrt(N)/m)+1)` relevant candidates under a
literal separate-class implementation, as a loose upper bound, plus paid
class generation. This counting observation is not a new exponent gain or a
free wheel construction. With arbitrary adapted coefficients the honest
expression is setup cost plus `sum_q poly(ell_q)` plus query scheduling,
boundary/gcd work and storage, not automatically `Q_N*poly(log N)`.

## C. Sharp scoped obstruction to a uniform gap-width claim

This is an algebraic family, not a sampled or timed candidate run. Let

    h=6*t, t>=1,
    k=2*h-1,
    N=h*k-1=2*h^2-h-1=(h-1)*(2*h+1),
    [L,U]=[h-1,h+1].

`N` is composite and odd. As `N=2 mod 3`, it is not a square. The interval
lies in `[2,isqrt(N)]` because

    N-(h+1)^2=h^2-3h-2>0  (h>=6).

The midpoint gcd is 1 since `N=-1 mod h`. The integer point `(h,k)` has
`hk=N+1`, hence belongs to `C`, and has objective

    N*h+h^2*k=2Nh+h.

For any positive integer `x!=h`,

    (x-h)^2/x >= 1/(h+1).

For completeness, on the right write `x=h+d,d>=1`; the inequality follows
from `(h+1)*d^2-(h+d)=(d-1)*((h+1)*d+h)>=0`. On the left,
`x=h-d`, `1<=d<h`, and `(h+1)*d^2-(h-d)>0`.

Moreover `N>h*(h+1)` for `h>=6`. Thus for every feasible integer point with
`x!=h`, its objective minus `2Nh` exceeds `N/(h+1)>h`. At `x=h`, the smallest
admissible integer ordinate is `ceil(N/h)=k`. Therefore **the unique integer
optimizer is `(h,k)`**, throughout the full positive-integer hyperbolic region
as well as the displayed clipped query. There was no optimizer search.

Here `delta=h`, so

    R(X)=N*(X-h)^2-h*X,
    R(h)=-h^2<0,
    R(h-1)=N-h*(h-1)=h^2-1>0,
    R(h+1)=N-h*(h+1)=h^2-2h-1>0.

The two real roots are strictly between `h-1,h` and `h,h+1`, respectively.
The strict integer exclusion is exactly `{h}` and neither boundary is
integral. The optimizer gcd is `gcd(h,N)=1` (also `gcd(k,N)=1`). Even/square
preprocessing does not remove this family. The factor `h-1` remains in the
queried interval. The tangent is central in the sense that
`h/sqrt(N)->1/sqrt(2)`, rather than tending towards an asymptote.

This is not an artifact of supplying a short interval. Set instead
`U=isqrt(N), L=2*h-U`. From `N>(h+1)^2` and
`(2*h-1)^2-N=2*h^2-3*h+2>0` we get `h+1<=U<=2*h-2`, so
`2<=L<=h-1` and the integer midpoint is still exactly `h`. This interval
contains `2*(isqrt(N)-h)+1=Theta(sqrt(N))` candidate integers. The global
optimizer proof above applies unchanged, and still excludes only `{h}`.

A fixed illustration, checked by arithmetic only, is `h=6,N=65,[L,U]=[5,7]`:
`s=786`, `R(5)=35`, `R(6)=-36`, `R(7)=23`. These values illustrate the symbolic
proof, not a performance measurement or a distributional claim.

There is also a **reachable first-query** family for the literal baseline,
so reachability need not be assumed even for a single slow query. Keep
`h=6*t,t>=1`, but set

    k=4*h-3,
    N=h*k-1=4*h^2-3*h-1=(h-1)*(4*h+1).

It is again odd, composite and `2 mod 3`, hence nonsquare. Because

    N-(2*h-1)^2=h-2>=0,  (2*h)^2-N=3*h+1>0,

we have `isqrt(N)=2*h-1`. The baseline's initial interval `[2,2*h-1]` has
integer midpoint `h`. The same uniqueness proof applies: `N=h*k-1`, and
`N-h*(h+1)=3*h^2-4*h-1>0`. Its support value is `2Nh+h`, both optimizer gcds
are 1, the only excluded integer is `h`, and neither boundary is integral.
Thus a first query over the entire initial factor range can have the sharp
one-candidate outcome after the proposed even/square checks. Additional paid
preprocessing, such as trial division or general perfect-power detection, is
not claimed to leave every member of this family untouched.

**Precisely what fails:** no universally valid claim that each such midpoint
query excludes two integers, or a polynomially growing number of integers,
can follow from convexity and integrality alone. The local one-candidate
guarantee is sharp even for an admissible central interval of an odd nonsquare
composite.

**Precisely what remains open:** the first family's clipped interval is not
claimed to be reached by the queue; the second family does prove reachability
of one singleton outcome on the first query. Neither produces a hard-instance
lower bound or a long sequence of singleton removals. In the first family's
three-integer version a subsequent endpoint gcd immediately finds a factor.
A small-factor stage may remove these families. There is
no lower bound here for adaptive early stopping, a clipped hull, a different
slope selection, batched supports, residue queries, or factoring generally.

## D. Delivery, limits and next decisive work

The exact reduction and baseline survive this review. The unsupported step is
an all-input bound on the *total paid number* of queries and their coefficient
sizes, plus acquisition of any useful residues or supporting directions. A
`Q_N` bound merely below `N^(1/5)` by an unspecified factor is not by itself an
exponent improvement: a claim against that reference should give, for example,
`Q_N<=N^(1/5-epsilon)*poly(log N)` for fixed `epsilon>0`, with all other costs
paid and the reference's scope matched. This review does not independently
reaudit the parent's deterministic factoring baseline.

Next decisive proof: bound how often small `delta=s-2Nh` can occur along the
actual queue or show a paid operation that combines many supports. The exact
gap polynomial `N*(X-h)^2-delta*X` is available for that analysis. The family in
C must be accommodated by amortization rather than ruled out by a uniform
width assertion. Do not replace this task by an assumed normal-fan selector,
integer-conic feasibility, or full-hull output-size lower bound. No next
numerical run is recommended or authorized by this review.

Evidence consists of this proof, the fixed standard-library algebraic
certificate and its output, frozen repository inputs, and the publisher PDF
with text extraction and the three inspected rendered pages. The certificate
checks polynomial identities and two fixed signed/modulus boundary examples;
it performs no candidate search, enumeration of factors, optimization run or
parameter sweep. It is not a Lean proof or a formal machine cost refinement.

The `-inputs-manifest.json` and `-sources-manifest.json` files record provenance.
The `-delivery-manifest.json` and `-delivery.sha256` files hash the final
deliverables. All writes are named `research/findings/W012-quotient-support-review*`.
No shared-state disposition is made on the parent's behalf.
