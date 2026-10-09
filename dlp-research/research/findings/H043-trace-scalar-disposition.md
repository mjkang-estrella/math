# H043 trace family: explicit conversion, no scalar bridge

2026-10-09 UTC. Raw Claude Opus5.5 report: H043-trace-scalar-opus-raw.md,
including the retained T3 task ID and the proposer's incomplete required
reading. Root checked its algebra and primary sources; native Astra reviewed
the mathematics and native Sol reviewed costs/recovery. No numerical run,
benchmark, Lean theorem or H034 reset. Best supported exponent1/2;
verified complete-work improvement NONE.

## What the public operator does and does not imply

H042 supplies E'_b: V^2=u f(b-u), where f(x)=x^3+a_E*x+b_E, p>3,
and b=x(2A). If A=-[2^-1]T, then b=x(T). Its exact corrected h-sum is

    -a_p(E'_(x(T)))-chi(-1)-2chi(x(T)-x([2^-1]T)).

This is computable from the public point T. That observation does NOT prove
it useless: an efficiently computed representation can still facilitate an
otherwise difficult inverse problem. It also does not prove that every scalar
decoder must be a homomorphism or respect the group law. The requirement is
an explicit efficient recovery algorithm with justified complete costs, which
could use nonhomomorphic structure. None was supplied in this pass.

## Explicit Weierstrass conversion and degree

For f(b)!=0, substitute u=1/s, V=W/s^2, followed by t=f(b)s and Y=f(b)W.
The quartic becomes

    Y^2 = t^3-f'(b)t^2+3b f(b)t-f(b)^2.

The maps extend birationally to the smooth completions; their affine
denominators require the usual exceptional-point handling. Constructing the
coefficients costs O(1) FIELD operations, not O(1) bit work, point counting,
canonicalization or discrete-log recovery. Model conversion is no longer a
missing primitive.

Over an algebraic closure write f(x)=product_i(x-e_i). The cubic roots are

    r_i=f(b)/(b-e_i)=b^2+b e_i+(e_i^2+a_E).

Their pairwise differences give discriminant disc(f)*f(b)^2. The elliptic
invariants therefore give

    j(E'_b)=256 H(b)^3/(disc(f)*f(b)^2),
    H(b)=f'(b)^2-9b f(b)=-3a_E*b^2-9b_E*b+a_E^2.

At a root e of f, H(e)=f'(e)^2!=0; numerator and denominator have no common
root. The rational j-map has degree6, also when a_E=0. This is a point-family
map, not a degree6 polynomial in the unknown scalar n.

There is likewise a polynomial description modulo p of the trace, but its
variable is b. With h=(p-1)/2 and chi(0)=0, H042's point count gives

    a_p(E'_b) = -chi(-1)-sum_(x in F_p) ((b-x)f(x))^h    modulo p.

The right side has degree at most h in b. It is not a low-degree expression
in n when b=x([n]G), nor a new cheap labelled inverse. Building/manipulating
its dense coefficients would require its own charged algorithm. The degree
bound is not a universal circuit or evaluation lower bound.

## One particular correspondence really is zero

On C_b: y^2=f(b-z^2), let sigma(z,y)=(-z,y) and tau(z,y)=(-z,-y).
The hyperelliptic involution iota acts by -1 on the Jacobian, and tau=iota*sigma.
Let pi:C_b->E and pi':C_b->E'_b be the two degree2 quotient maps. Pullback
and norm on degree-zero divisor classes satisfy

    pi'^* pi'_* = 1+tau_*,
    sigma_* pi^* = pi^*,
    (1+tau_*) pi^* = (1-sigma_*) pi^* = 0.

Applying pi'_* shows [2](pi'_* pi^*)=0. On the odd-order target subgroup,
its image is also q-torsion, so the composite vanishes because gcd(2,q)=1.
Thus this named correspondence does not transport the secret into E'_b.
This is not a theorem excluding every other correspondence, representation
or nonhomomorphic decoder. Conversely pi^* retains the original odd-order
subgroup: pi_*pi^*=[2], so its restriction to that subgroup is injective.

Root read [Diem's theorem and introduction](https://arxiv.org/pdf/math/0606607).
For fixed genus2 the cited algorithm has soft-O(p) expected time and
soft-O(p^(3/4)) storage, conditional on a cyclic degree-zero class group or
known basis and element orders, with an appropriate bounded-degree model.
Those are upper bounds, not lower bounds. The target here is the embedded
order-q subgroup, not an arbitrary full Jacobian of order about p^2; the split
family does not automatically satisfy the group-structure prerequisite.
The cited guarantee supplies no improvement over the order-q square-root
reference when q is comparable to p. It does not rule out a better algorithm
on this structured family.

## Unproved collision and statistical arguments

A trace alphabet of O(sqrt(p)) gives an O(p^(1/4)) birthday upper scale for
IID trace outputs: uniform output maximizes the no-collision probability.
It does not establish a matching lower bound or a precise collision law,
and dependent/adaptive sampling needs separate analysis. Several affine
queries are not automatically injective. The induced distribution and useful
collision rate remain relevant. Equal traces supply no equation in known point labels;
even constructing an isogeny is an additional paid task, not a scalar bridge.

For a supplied nonzero class polynomial of degree h_D, composing its equation
with the degree6 j-map gives at most6h_D geometric b-values, and at most12h_D
finite points of E above them, after excluding singular/denominator branches.
This algebraic counting upper bound is independent of a near-uniform density
claim. Constructing the class polynomial, handling reduction/CM applicability,
root extraction, rationality, subgroup checks and unknown logarithms all
remain paid. It does not give a decomposition algorithm or useful relation
rank; the submitted factor-base suggestion remains incomplete.

The raw ramification sketch is not an accepted statistical exclusion. In
fact its assertion of ramification at every point of E[2] is already false
at O for this pullback. To see good reduction there, let z_0=-x(R)/y(R) be
a local parameter at O and b=x(R). Starting from the roots r_i above, put
t=b^2+b s and Y=(b/z_0)w. The local equation is

    w^2=(b z_0^2) product_i(s-e_i-(e_i^2+a_E)/b).

The coefficients are base-field symmetric, regular at O, and reduce to f(s),
because 1/b vanishes and b z_0^2 tends to1. The special fiber is smooth.
Astra independently checked this local model. No full monodromy theorem is
claimed here, and bad-fiber arithmetic cannot be replaced by a guessed set.

Root read the stated definitions in [Fouvry–Kowalski–Michel](https://arxiv.org/pdf/1405.2293).
Their criteria impose geometric monodromy, twist-isomorphism and tuple
conditions for the relevant sheaves; naming an analogous criterion does not
check them for this elliptic-base pullback. Domain, conductor growth under
multiplication, exceptional points, normalization and parameter dependence
also matter. Even a valid fixed-tuple correlation upper bound would not
automatically exclude all statistical or adaptive decoders. No such exclusion
is accepted from this sketch.

## Decision

Retain the explicit cubic model and the zero composite on the target subgroup,
with the corrected local-good-reduction counterexample. These are focused
paper verifications of the submitted route, not a new attack or novelty claim.
No executable experiment is admitted: the next necessary contribution is a
concrete scalar recovery operation, not another evaluator benchmark or a
general rejection of coordinate methods. The other H043 independent solver
and full-work investigations remain separate and live.
