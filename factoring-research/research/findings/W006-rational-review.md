# W006 rational-map review — valid transition, fixed menu rejected for scalar capture

2026-10-08. Independent T3 child validation; parent owns acceptance and further
construction. **Verified new factoring complexity improvement: NONE.**

**Disposition: REVISED, with a decisive rejection of the frozen menu's uniform
scalar-capture route.** The finite-ring identities, bounded transition cost,
odd/twice-odd power laws and properly stopped sign-invariance arguments survive.
The parameters 2 and 5 are not merely characteristic-zero conjugates of power,
Chebyshev or Lattes maps. Nevertheless, for every prime p = 5 mod 12, *every*
defined composition using a in {0,1,3,2,5}, even with adaptive choices, has
cumulative scalar basin exactly 2/(p-1). Depth cannot increase it. This is an
infinite local obstruction, not a claim about all parameters, denominator
factoring, the norm-5R packet route, or factoring generally.

The expressly conditional screen was **OMITTED before candidate construction
or execution**: the symbolic obstruction already supplies its decisive
fixed-menu scalar-capture falsifier. All 60 cases remain UNKNOWN/UNSTARTED in
[the ledger](W006-rational-review-unstarted.json). No graph, timing, image-size
or empirical basin observation is claimed. The exact finite graphs on the
other primes are unmeasured, rather than inferred from this rejection.

Source identities are preserved in [inputs](W006-rational-review-inputs.json)
and the [bounded source/read ledger](W006-rational-review-sources.md).
The [metadata verification](W006-rational-review-verification.json) and
[delivery hashes](W006-rational-review-delivery.sha256) identify this handoff.
No shared code, Lean, dependencies, registry, parent notes, STATE or sibling
project was edited; no delegation, commit or publication occurred. No scratch
source code was changed, so scripts/check.sh was not triggered or run.

## 1. Domain and all displayed rational-map identities

Let A=Z/NZ, N>1 odd, S=A[i] with i^2=-1, and H={h: h*bar(h)=1}. Elements of
H are units and h^(-1)=bar(h), also for repeated prime powers and the split
quadratic algebra. Scalars a are reduced modulo N before arithmetic.

For z=h^2, A0=z+a and D=az+1, multiplicativity of the norm gives

    Norm(A0)=1+a(z+bar(z))+a^2=Norm(D)=d.

A unit norm is equivalent to being a unit in S: the forward implication
uses bar(D)/d, and the converse follows by taking norms of an inverse.
Thus the literal gcd(d,N) branch is sound. A proper gcd is a verified factor;
gcd=N is an allowed exhausted attempt, not a claim that D is the zero element
or that no further factor could be extracted. In a split algebra a nonzero
zero divisor has zero norm; modulo p^e the norm valuation can also hide a
partial coordinate valuation. Cancellation on either such branch is invalid.
When d is a unit, both numerator and denominator are units, and

    F_a(h)=h*(h^2+a)/(a*h^2+1)  belongs to H.

The two displayed factorizations are correct as polynomial identities:

    h*(h^2+a)-(a*h^2+1)=(h-1)*(h^2+(1-a)*h+1),
    h*(h^2+a)+(a*h^2+1)=(h+1)*(h^2+(a-1)*h+1).

Division asserts their rational identities only on the unit-D domain.
In particular, +/-1 are defined fixed points only when a+1 is a unit.
The generic phrase “two fixed points” does not apply to a=-1 or to primes
where a=-1 after reduction. Parameter exceptional primes cannot be discarded.

For completeness, the fixed-a prime-field denominator count is explicit.
If a is neither 0 nor +/-1 and p is nonsplit, there are no bad points:
zero norm would mean D=0 in F_(p^2), forcing h^2=-1/a and hence a^2=1.
If p is split, write h=(w,w^(-1)) with w in F_p^*. The denominator norm is
(a*w^2+1)*(a*w^(-2)+1). There are four bad points when (-a|p)=1, and none
when (-a|p)=-1; the two root pairs are disjoint because a^2 is not 1.
At a=0 there are none, and at a=+/-1 the two bad points are described in
section 3. Over p^e, badness is exactly badness after reduction modulo p.

A useful independent coordinate expansion, with h=u+iv and u^2+v^2=1, is

    d=(a-1)^2+4a*u^2,
    u'=u*(4u^2+(a-1)*(a+3))/d,
    v'=v*(4u^2-(a-1)^2)/d.                         (1)

To check it, multiply h(h^2+a) by a*h^(-2)+1. Its numerator is
h^3+2a*h+a^2*h^(-1); collecting coordinates gives (1). This also proves
all the local ingress tests below without cancelling a zero divisor.

There is no hidden group-homomorphism theorem here. Over an algebraic torus,
endomorphisms are monomials, whereas the generic displayed rational map has
nontrivial finite poles. Sign equivariance is a much weaker property.

## 2. Exact ingress law and the decisive menu obstruction

Fix an odd prime p, let epsilon=(-1|p), m=p-epsilon=|H_p|, and count initial
points uniformly in H_p. “Cumulative scalar basin” means first hit of
{+1,-1}, including time zero, before a nonunit denominator. No renormalizing
by the surviving population is permitted.

For a not congruent to +/-1 or 3, put

    Q_a=(3-a)*(a+1).

If v is nonzero, (1) shows that a defined transition becomes scalar exactly
when 2u=+(a-1) or 2u=-(a-1). At these points

    v^2=Q_a/4,                 d=(a-1)^2*(a+1).

Consequently these are valid preimages precisely when Q_a is a nonzero
square in F_p. There are four distinct nonscalar preimages in that case,
and none when Q_a is a nonsquare. Thus the exact one-step cumulative count is

    B_1(a,p)=2+4*1_{(Q_a|p)=1}                    (2)

on the stated nonexceptional domain. Equivalently, the discriminant
(a-3)(a+1) must have character epsilon in the split/nonsplit description.
Using “discriminant square in F_p” in both descriptions would be wrong.

The formula also proves that nonmonomial local gains really can occur:
at p=7,a=5, Q_a=2 mod 7 is a square, so six of the eight initial points
hit by time one. The other two are +/-i, the invariant two-cycle below;
therefore the eventual basin is exactly 6/8. The a=0,1,3 controls each have
basin 2/8 there. This is a symbolic specialization of (2), not a candidate
run or a finite factoring result, and does not resolve the uniform claim.

If Q_a is a nonsquare, the only defined preimages of the target set are
the target set itself. Induction then proves the sharp all-depth result

    B_k(a,p)=2 for every k>=0,  including the eventual basin.       (3)

The degenerate cases a=1 and a=3 also satisfy (3), by section 3. Now suppose
p=5 mod 12. Quadratic reciprocity gives (-1|p)=1 and (3|p)=-1. For the frozen
menu, the Q values are respectively

    a=0: 3;   a=1: 4;   a=3: 0;   a=2: 3;   a=5: -12.

The a=1,3 degeneracies have no extra ingress. The other three values have
nonsquare Q since -1 and 4 are squares. This includes p=5, where a=5 reduces
to a=0. Therefore every menu member has no defined transition from outside
{+1,-1} into it. The same assertion holds for *any* sequence of menu choices,
including choices based on the entire current point: there is simply no
allowed local edge entering that set. Sign-invariant choice is needed for
the separate blinding proof, not for this obstruction.

With the prescribed initial check, cumulative capture is exactly

    Pr[hit +/-1 at any depth before denominator failure]=2/(p-1).  (4)

It is not inverse-polynomial in log p. Arbitrarily many iterations of one
sample do not help; L fresh uniform samples give probability at most
2L/(p-1) of any scalar hit. Cold-sampler failure can only reduce this branch.

Infinitely many such primes exist even without importing an analytic prime
distribution theorem. If a finite list contained them all, take x twice
their product. Then x is even, 3 does not divide x, and x^2+1=5 mod 12.
Every prime divisor of this odd number is 1 mod 4 and is not 3; hence it is
1 or 5 mod 12. At least one divisor is 5 mod 12, and it divides none of x,
contradicting the list. The finite protocol already contains p=5,17,29,41;
their fractions 1/2,1/8,1/14,1/20 follow symbolically, not from execution.

This decides the proposed fixed-menu *uniform scalar-basin* question more
strongly than a finite screen could. It leaves denominator extraction open:
a nonscalar trajectory may encounter a nonunit denominator and split a
composite. The theorem therefore is not a rejection of every factoring use
of the literal transition. It also does not count useful norm-5R field packets.

One additional universal cheap counterexample is h=+i or -i. For any scalar
a with a-1 a unit, F_a(h)=-h; otherwise its denominator is nonunit. No scalar
parameter can give a defined scalar output from these points. This disproves
full attraction for any all-defined schedule, but alone would not disprove
inverse-polynomial basin mass; (4) is the materially stronger obstruction.

## 3. Controls, chart exceptions, and repeated powers

**a=0.** D=1 and F_0(h)=h^3 everywhere. On cyclic H_p its kth iterate is
h^(3^k). It has exactly 2*gcd(3^k,m) initial points landing in +/-1 by time
k, and eventual basin size 2*3^v_3(m). These formulas include time zero.
On H_(p^e), replace m by p^(e-1)(p-epsilon). This is the familiar odd-order
annihilation control; no exponent-acquisition work is saved.

**a=1.** Cancellation gives h only where h^2+1 is a unit. Its norm is 4u^2.
Over H_p the excluded points are exactly +/-i; every other point is fixed.
The scalar basin is exactly the initial two points. Over p^e the same
implementation excludes all points whose u is divisible by p, rather than
just exact +/-i. Replacing the literal map with total identity would change
the denominator outcomes and is not the frozen candidate.

**a=-1.** Cancellation gives -h only where 1-h^2 is a unit; its norm is
4v^2. Over H_p, +/-1 are excluded from the transition domain and all other
points are two-cycles. The initial scalar check still finds those two points,
but they are not fixed points of the partial map. Over prime powers the
exclusion is p|v. Cancelling through these holes loses specified outcomes.

**a=3.** With T(h)=(h-1)/(h+1), cross multiplication proves

    T(F_3(h))=T(h)^3.                             (5)

As a rational identity on P^1 this is a conjugacy to cubing. As an actual
finite-ring computation it additionally requires the original D to be a unit
and the inverses in each chosen chart to exist. At h=-1 use the inverse
chart; across CRT components a single affine chart need not be available.
The equation does not authorize skipping an uncancelled denominator test.

Crucially, the target +/-1 becomes 0/infinity under T, not +/-1. Neither
0 nor infinity has another preimage under cubing. Thus the field scalar basin
is exactly two points for every odd prime, irrespective of cubing's image
compression elsewhere. In real conic coordinates t=v/(u+1), the induced map
is t -> -t^3; the split conic omits the two parameters t^2=-1. Landing on an
omitted parameter is a denominator failure, not a successful scalar hit.

Equation (1) gives the even sharper valuation identity on the unit domain:

    v'=-v^3/(4-3v^2).

For each prime divisor p, unit-denominator steps preserve whether p|v;
if p|v they multiply its truncated p-adic valuation by three. Over p^e the
exact kth scalar basin count is

    2*p^(e-ceil(e/3^k)),

and the eventual count is 2*p^(e-1). Hensel lifting of u^2=1-v^2 supplies
exactly two u values for each v divisible by the displayed power of p.
These trajectories have unit denominator throughout. All other points
cannot become scalar modulo p. Since the direct control already checks
gcd(v,N) initially, this p-adic concentration supplies no new v-gcd split:
a partial divisibility was already a proper factor, and no new prime can
begin dividing v. Denominator factors are again a distinct channel.

Local H_(p^e) is cyclic of order p^(e-1)(p-epsilon): in the split case it is
the usual odd prime-power unit group; in the nonsplit unramified quadratic
algebra its norm-one principal units have cyclic successive lifts and order
p^(e-1), coprime to the residue group order p+1. One can see cyclicity by
lifting any norm-one element 1+p*i+O(p^2): for odd p its p-power valuations
increase by one, giving an element of order p^(e-1). The residue group is
cyclic, and lifting its prime-to-p part completes the product.

Perfect-power handling remains necessary for a factoring theorem: for a
single distinct prime, scalar roots of unity are only the two global signs
and yield no mixed-sign split. Proper gcds can nevertheless reveal a partial
prime-power factor. Paid perfect-power detection/extraction or explicit
valuation accounting must precede any all-composites performance claim.

## 4. Generic a: conjugacy and prior-art scope

Over characteristic zero, with a not +/-1, the rational map has degree three.
Its derivative and fixed multipliers are

    F_a'(h)=[a*h^4+(3-a^2)*h^2+a]/(a*h^2+1)^2,
    multipliers at 0,infinity: a,a,
    multipliers at +1,-1: b,b,     b=(3-a)/(a+1).

Direct substitution gives the family symmetry

    T o F_a o T^(-1)=F_b.

For a=0 this identifies F_3, as above. For a not 0,+/-1,+/-3, the derivative
has four distinct simple critical points: its quadratic discriminant in h^2
is (a^2-1)(a^2-9), and neither 0 nor infinity is critical. This critical
multiplicity pattern rules out conjugacy to degree-three power maps (two
double critical points) or degree-three Chebyshev maps (a double critical
point at infinity and two simple ones). At a=-3, set S(h)=(h-i)/(h+i);
direct expansion gives S(F_-3(h))=S(h)^(-3). It is the inverse-cubing
exception, not a generic new mechanism. At a=+/-1 the degree drops to one.

No rational a yields a genuine Lattes map in characteristic zero. Here is a
short deduction, not an assertion from an unsuccessful literature search.
For a degree-three Lattes map, Milnor's Theorem 3.1 and Corollary 3.9 imply
that a fixed multiplier has absolute value 3^(r/2), where
r is in {1,2,3,4,6}. A rational fixed multiplier is real rational, so its
absolute value can only be 3,9 or 27. Apply this to both a and b. Testing
a in {+/-3,+/-9,+/-27} leaves only a=-3 with both absolute values allowed;
that map is already inverse-cubing, with periodic critical points, and is
not Lattes. Values a=0,+/-1 are also excluded directly. This proves the
claim for rational parameters, including every fixed integer in the menu.
It does not classify all algebraic/complex parameters or exceptional finite
characteristic reductions.

For 2 and 5 specifically, b=1/3 and -1/3, giving nonzero attracting fixed
multipliers over C, also incompatible with the exceptional families.
Complex attraction supplies no finite-field capture probability.
Finite-characteristic coincidences remain real: at p=5, the menu's a=2
is -3 and its a=5 is 0. The characteristic-zero exclusions do not label
those primitive cases as new nonmonomial controls.

The involutions h -> -h and h -> 1/h commute with F_a; their four-element
symmetry group is not itself a new construction. Cubic automorphism loci
are treated in [West, section 3.3](https://arxiv.org/pdf/1408.3247).
[Milnor, sections 2-3](https://www.math.stonybrook.edu/preprints/ims04-01.pdf)
provides the exceptional-map definitions and multiplier restriction used
above. These are characteristic-zero comparisons, with no claimed earliest
priority or transfer of a basin law to Z/NZ.

The trace s=h+h^(-1) obeys another directly derived identity:

    F_a(h)+F_a(h)^(-1)
      =s*(s^2+(a-1)*(a+3))/(a*s^2+(a-1)^2).

For a=0 this is s^3-3s, the Chebyshev/Lucas trace of cubing. For generic a it
is a rational trace map, not a proved group-order annihilator. Powering the
norm-one torus retains the p-1/p+1 control from W001. If instead one searches
collisions of two iterates and takes gcds, the resulting method is a
Pollard-type walk; mere nonmonomiality establishes no collision law.
[Brent, sections 5-7](https://maths-people.anu.edu.au/~brent/pd/rpb051i.pdf)
explicitly uses a random-map assumption for the familiar square-root-scale
heuristic. That assumption is not proved for this rational family here.

## 5. Forced parameter, nonunits, and a random-parameter repair that fails

The parent's polynomial identity is correct:

    z*(z+a)^2-(a*z+1)^2
      =(z-1)*(z^2+(1+2a-a^2)*z+1).

Since z is a unit, if z-1 is also a unit, scalar output forces

    (a-1)^2=z+2+z^(-1)=(h+h^(-1))^2=4u^2.        (6)

Conversely (6), with the unit original denominator, makes F_a(h)^2=1.
In H over odd N this is a scalar root of unity: F=F^(-1)=bar(F) forces
its imaginary coordinate to be zero. Polynomial cancellation is not valid
when z-1 is nonunit. In fact Norm(z-1)=4v^2, so z-1 is a unit exactly when
v is. The parent's initial gcd(v,N) already handles this branch: proper gcd
is a factor, and v=0 modulo N is the scalar event. Testing only the norm
and seeing gcd=N could miss a proper partial valuation in v.

Writing s=2u, the known choices a=1+s and a=1-s give F=+1 and -1 wherever
defined. For the plus choice, A0=(h+1)*(h^2+1)/h and
D=(h+1)*(h^2+1); for the minus choice, A0=(h-1)*(h^2+1)/h and
D=-(h-1)*(h^2+1). Thus those asserted signs and their domain qualification
are correct. These choices use the sign-dependent root s, and do not supply
an invariant selector from z. Randomizing just a global +/- choice would
still expose the mixed CRT sign pattern for more than one prime.

On the further unit-u branch, a root t of 4u^2 selected using z only, and
a=1+t, would give F_a(h)=t/(2u), a scalar root of unity. This exhibits
exactly why an independent root would be useful. The algebraic requirement
is a modular square-root computation. A z-only input has the extra conic
data z as well as its trace; no equivalence to an arbitrary standalone
N,S-only square-root contract is silently assumed. What is missing is an
actual fast selector on this induced input distribution, with a paid useful
success law. Calling its output “a parameter” does not compute it.

There is a sharper warning against replacing the frozen menu by independent
uniform parameters. Fix h in H_p with u*v nonzero. Exactly two of the p
scalar parameters give a defined scalar output, a=1+/-2u, so the conditional
one-step hit probability is exactly 2/p. For u=0 it is zero. This remains
an upper bound 2/p after any nonhit history when the next parameter is freshly
uniform. Thus even adaptive stopping gives

    Pr[scalar hit by k] <= 2/m+2k/p.               (7)

As a polynomial in a, d has degree two and nonzero leading coefficient;
at most two parameters have nonunit denominator over a prime. Hence the
probability of scalar hit or denominator failure by k is at most
2/m+4k/p. For u*v nonzero the denominator discriminant is -16u^2v^2,
so exactly two bad parameters occur in the split case and none in the
nonsplit case; they are disjoint from the two scalar-producing parameters.
For u=0 only a=1 is bad. A uniform-a repair therefore only buys a linear
number of rare local opportunities, not useful polylogarithmic capture.
No random-parameter experiment was authorized or run.

## 6. Root-sign action, stopping, and the sampler boundary

Let K={r in A: r^2=1}; it has 2^omega(N) elements for odd N, one independent
sign per distinct prime power. It acts freely on H by multiplication. For
the same random tape and r in K,

    (rh)^2=h^2,     D(rh)=D(h),     F_a(rh)=r*F_a(h).

Thus every denominator gcd value, proper factor and exhaustion outcome is
unchanged. An adaptive parameter rule that is a function of sign-invariant
history chooses the same a in coupled paths. Induction proves equivariance
of every reached state. If the stopping event and cap depend only on this
invariant history, the stopped-state subprobability measure is K-invariant,
including its mass lost to failure. Uniform initial h is essential.
Use a fixed iteration/operation cap for this law. An acceptance cutoff based
on observed wall time or sign-dependent arithmetic traces needs its own
invariance proof; the omitted screen's measurement caps are not sampler rules.

The direct gcd(v,N) test is invariant, since r is a scalar unit. The event
v=0 is invariant too. At the **first scalar hit before extraction**, K acts
transitively on all scalar norm-one states, so conditional on a positive-mass
scalar hit every one of the 2^omega(N) signs has equal probability. Exactly
the two global signs fail the gcd(u-1,N) split. This proves the displayed
mixed-sign factor 1-2^(1-omega(N)), without assuming squarefree N.

Necessary stopping qualification: gcd(u-1,N) itself is not invariant under
the K-action. Its factor-vs-trivial outcome distinguishes the scalar signs.
Conditioning on that successful extraction excludes the two global signs;
one cannot then assert that the successful output law is still invariant.
Stop symmetrically at the scalar event first, apply the extraction law
second, and count a trivial scalar result as a failed attempt. Similarly,
certificate acceptance must not retain only selected scalar sign patterns.

For a fixed checkpoint with an invariant state law, let P_proper be the
probability 1<gcd(v,N)<N and P_scalar the probability v=0 modulo N.
Direct extraction succeeds with probability

    P_proper+(1-2^(1-omega(N)))*P_scalar.

For a fully stopped schedule use disjoint first-terminal events: a proper
denominator gcd, a proper v gcd, or a first scalar hit before either. Sum
the first two masses and the scalar mass times the same sign factor.
All exhausted trajectories and time caps remain failures. Arbitrary adaptive
histories can correlate CRT components; uniform marginal signs do not imply
independent basin events. Fixed public schedules have local product structure
before global conditioning, but global stopping must still be accounted for.

The W005 sampler's accepted rotation is exactly uniform only conditional on
its certificate branch. Retain its authoritative notation and probabilities:

    n=bitlength(N), L=2(n+1), B=2(n+1)^3,
    s=[1-(1-N/2^n)^L]^2, delta=1-s*(alpha+beta),
    C_B=alpha/(alpha+beta)*(1-delta^B),
    F_B=beta/(alpha+beta)*(1-delta^B), E_B=delta^B.

Here alpha is the unit-norm pair probability and beta the proper-norm-gcd
probability. They are proof quantities, not factorization-dependent algorithm
inputs. For the defined direct schedule with conditional masses D,V,S above,
its cold success probability is

    F_B+C_B*(D+V+(1-2^(1-omega(N)))*S).

This is a probability identity, not a positive uniform lower bound.

For certificates, W=x*(1+2i)*F(h) has norm 5R when x^2=R. Multiplying x by
r changes W's law by multiplication of F(h) by r, which the invariant
stopped law absorbs. This argument extends W005's root-choice independence
to unequal fibers, provided all visible metadata is jointly invariant.
The inner solver gets only N,R,W and fresh independent randomness, never h,
the accepted sampler pair, a reconstructible tape/seed or an unsafe inverse
trace. Passing sign-invariant history requires its joint-law proof; passing
the entire h history does not qualify. Norm 5R must be a unit, so the W005
joint-wrapper assumption gcd(N,30)=1 is retained, although the bare H-map
only needs odd N. Its field-packet success probability remains unproved.

## 7. Independent audit of powered-blindnorm.md

For any integer E>0, uniform h has uniform image under h -> h^E because
the map is a homomorphism with equal fibers. When E is odd, every r in K
is its own E-th preimage. For E=2*E_odd the parent's displayed element

    z_r=(1+r)/2+i*(1-r)/2

has norm ((1+r)^2+(1-r)^2)/4=1, vanishing cross term, and square r.
Hence z_r^(2*E_odd)=r. Both images contain K and have the required invariant
law. This is an existence proof, not permission to enumerate hidden signs.

More precisely, on H_(p^e), the image contains -1 iff

    v_2(E)<v_2(p-epsilon).

All odd-prime values p-epsilon are divisible by four, so odd and twice-odd
E satisfy this uniformly. It need not hold for four-divisible E: p=11,
m=12 and E=4 give an image of order three, omitting -1. Some further even
exponents may work on a restricted input, but the uniform guarantee fails.
E must be selected independently of the fresh h, as the parent requires.

For odd/twice-odd E the local image size and prime-field scalar probability
are exactly

    q_p=m_p/gcd(E,m_p),     alpha_p=2/q_p.

For squarefree N=pq, CRT uniformity makes the local events independent.
Exactly-one-vanishing probability is alpha_p*(1-alpha_q)+alpha_q*(1-alpha_p).
If both vanish their signs are independent uniform +/- signs, and the
outer-root comparison or direct gcd(u-1,N) succeeds with probability 1/2.
The parent's total alpha_p+alpha_q-(3/2)*alpha_p*alpha_q is correct, conditional
on a uniform H sample. Multiplying the imaginary coordinate by unit x does
not change its gcd with N; this is a direct order-based control.

A precise repeated-power completion is available. Put

    m_(p,t)=p^(t-1)*(p-epsilon),
    alpha_(p,t)=2*gcd(E,m_(p,t))/m_(p,t),  1<=t<=e_p.

Reduction H_(p^e) -> H_(p^t) is onto and its powered image is uniform.
Thus alpha_(p,t)=Pr[v=0 mod p^t]. For N=product p^e, the exact single-check
success probability after powering, conditional on uniform h, is

    1-product_p(1-alpha_(p,1))
      -2^(1-omega(N))*product_p alpha_(p,e_p).     (8)

Indeed the first product is the unit-v failure; the full-scalar event has
the second product as its mass, and only its two global signs fail. All
other gcds are proper, including partial powers. For one distinct prime
(8) becomes alpha_(p,1)-alpha_(p,e), with zero mixed-sign contribution.
For squarefree pq it specializes exactly to the displayed parent formula.

The claimed general form F(h)=h*G(h^2) is correct when G is a well-defined
H-valued function on squares. For a partial G its domain and failure rules
must be invariant and charged. It is not enough to assert an arbitrary
acceptance predicate without its stopped-law proof.

## 8. Bit work, representation degree, and success cost

Let n=bitlength(N). Residue pairs, temporary products, a, d and Euclidean
coefficients all have O(n) bits when reduced normally. A transition uses
O(1) scalar/ring multiplications, reductions, gcds and one inverse. Classical
bit arithmetic with the standard amortized Euclidean implementation gives
O(n^2) per step; a coarser O(n^3) Euclidean envelope remains polynomial if
one does not supply that implementation. “One inverse” is not a unit-cost
bit operation. The parent's O(n^2) envelope is realizable, not a complexity
certificate for an unspecified Python implementation.

For k supplied steps the map work is O(k*n^2). Streaming space is O(n+log k)
plus parameter-generation state; the parent's O(log N) statement presumes
k is polynomially bounded and a constant-space public schedule. Arbitrary
stored adaptive history, full evidence and a huge input parameter are not
free. Reading/reducing a long parameter and constructing the schedule belong
in C_schedule. A full trial can conservatively be priced

    O(n^6)+O(k*n^2)+C_schedule+C_extraction+C_inner,

using W005's accepted capped O(n^6) sampler envelope; omit C_inner only for
the direct control. It has at most 8n(n+1)^4 raw sampler bits. The finite
caps and C_B,F_B,E_B cannot be replaced with costless perfect sampling.

For powers the work is O(bitlength(E)*n^2)+C_E after sampling, and storage
must also account for the exponent or its explicit stream. Constructing and
reading E are charged. The odd-integer lcm up to B has bit length O(B),
indeed order B asymptotically, not order log B. Binary powering saves literal
repeated multiplications; it does not find a useful order divisor.

For a nondegenerate rational map the formal degree after k compositions is
3^k; a literal evaluation uses only k transitions. Dense expansion would
pay for exponentially many coefficients and is not required here. Equally,
formal degree gives at most that many algebraic preimages of a point with
multiplicity, no lower bound on rational preimages in H_p, their distinctness,
or their probability. Equations (3)-(4) are explicit cases with high degree
and no scalar-basin growth. Over composite rings different reductions and
literal denominator holes need separate treatment.

If independent cold trials have mean cost C and proper-factor probability
sigma, restart cost is C/sigma. Neither symmetry nor a polynomial trial cost
provides a useful lower bound on sigma. Reusing one h, correlating restart
parameters, or conditioning on previous failures does not license an iid law.
No finite graph observation or its omission changes this obligation.

## 9. What survives and the next decisive computation

An explicit cheap norm-preserving, sign-equivariant transition survives as
a mathematical primitive. A useful new factoring computation with proved
yield does **not** survive this audit. The specific fixed menu cannot supply
uniform scalar capture, a=3 adds no new v-gcd support, and fresh uniform-a
replacement has the 2/p ingress barrier. Denominator factors and the
norm-5R packet branch remain executable but have no newly established
useful-mass lower bound. They are not accepted as speedups by omission.

The negative results impose concrete changes, not an unnamed root oracle:

1. A scalar-capture continuation must provide an actual finite N,z-history
   parameter program outside the frozen menu and outside independent uniform
   parameter refresh. It must prove growth of the *first-hit set* under its
   specified transitions while paying every nonunit and failure. Its required
   event is the explicit equation (6). Feeding the program 2u or calling an
   independent square-root selector merely supplies the unresolved computation.
2. A materially different executable extraction is to keep two iterates of
   the fixed rational map and compare them instead of targeting +/-1. For
   example, a slow/fast walk applies F_2 once/twice per round, checks each
   original denominator, and takes gcd(N,Norm(h_slow-h_fast)); on gcd=N it
   can also check the two coordinate differences, with all tests charged.
   A proper gcd is verified; a full collision is failure/restart. This uses
   O(T*n^2) work and O(n) state for T rounds. It is a concrete Pollard-type
   control, not a new gain, and no such experiment was run or authorized here.
   Its decisive mathematical question is whether the actual stopped walk
   produces a *proper* hidden-component collision at a provably better paid
   scale than the known square-root heuristic, including simultaneous
   collisions and denominator failures. Image size or cycle counts alone
   would again be insufficient.

The immediate handoff is therefore the exact ingress criterion (1)-(4) and
the uniform-parameter barrier (7), for the parent's next construction to
bypass explicitly. The independent coefficient/cyclotomic and reflection
directions are unaffected. No end-to-end factoring claim follows.
