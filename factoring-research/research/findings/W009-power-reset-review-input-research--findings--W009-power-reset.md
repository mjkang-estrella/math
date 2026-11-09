# W009 — a reciprocal fold resets perfect-power structure

2026-10-08. Parent derivation, PROVISIONAL pending independent validation.
No candidate run or improved factoring bound. This directly tests the powered
fold proposed after the simple-pole envelope, including repeated powers whose
inner maps no longer have a simple pole.

## Actual changed computation and the intended saving

At a current rational circuit P acquire two distinct nonzero finite sampled
values y,w, paying the existing chart protocol. Choose a positive integer e
by a specified N-only rule, and evaluate

    R=F_(y,w) composed with P,   F_(y,w)(z)=(z-y)*(z-w)/z,
    P_new=R^e.

The homogeneous evaluator is
[(U-yV)(U-wV) : U*V], followed by binary powering of both coordinates.
Its added cost is O(log e) modular multiplications and paid acquisition of e.
The proposed saving would be to retain and compound power-subgroup constraints
across many folds, thereby increasing later useful collisions. Powering alone
does not enlarge the current zero or pole fibers.

The exact question is whether successive powers make a formally growing
perfect-power index e_1*...*e_k available at only sum log(e_j) work. The
following argument says the intervening fold destroys that accumulation.
It does not exclude a finite-field correlation at high degree.

## Four fibers forbid a prime-to-characteristic perfect power

Work over an algebraically closed field of odd characteristic p. Let P be
any nonconstant rational function, and let y,w be distinct nonzero constants.
For every prime ell != p, the proposed statement is

    F_(y,w)(P) is not an ell-th power in the rational function field.   (1)

First suppose P is separable of degree D. F has simple zeros at y,w and
simple poles at 0,infinity. Thus its pullback could have all divisor
multiplicities divisible by ell only if ALL ramification indices in each
of these FOUR distinct P-fibers were divisible by ell.

Each such fiber has degree D and at most D/ell geometric points. Its
contribution to sum_x(e_x-1) is at least D*(1-1/ell). The four disjoint
fibers therefore contribute at least

    4D*(1-1/ell) >= 2D.

Riemann--Hurwitz gives sum_x(e_x-1) <= 2D-2 for a separable map P^1 -> P^1;
wild ramification only increases the different, so cannot repair the
contradiction. This proves (1) for separable P.

For inseparable P, write P=S^(p^a) with S separable over the algebraic
closure. Taking p^a-th roots of y,w expresses F(P) as a p^a-th power of
the corresponding F(S). Multiplication of divisor valuations by p^a
does not change their divisibility by ell. The same contradiction applies.

Equivalently, an ell-th root of F would define the degree-ell superelliptic
cover T^ell=F(Z), branched at four points, of genus ell-1. A nonconstant
rational parametrization by P^1 would be impossible. The ramification proof
above makes clear why four fibers, not two or three, are decisive.

## Exactly which characters remain geometrically exceptional

A nonconstant rational function over an algebraically closed field is a
d-th power iff every divisor multiplicity is divisible by d; nonzero
constants have d-th roots there. Let H=F(P)^e. By (1), the gcd of the
divisor multiplicities of F(P) has no prime factor other than p. Therefore,
for every d dividing p-1,

    H is a d-th power geometrically iff d divides e.                  (2)

Consequently after ANY sequence of legal powered folds, the characters
whose pullback is geometrically trivial are exactly those with eta^e=1
for the OUTERMOST exponent e. Their number is gcd(e,p-1). Earlier
prime-to-p exponents do not multiply this index through the intervening
reciprocal folds. Repeating e=2 does not create a geometric 2^k-power map.

This corrects a possible overinterpretation of losing the simple-pole
certificate: loss of that particular certificate does not mean arbitrary
power constraints persist. The four-fiber argument supplies a new certificate
for every nontrivial character of the INNER folded map, independently of
the earlier powered history.

These are geometric statements. A high-degree non-power rational function
can accidentally take values only in a subgroup on F_p. Equation (2) is
NOT an impossibility theorem for that functional behavior. Such correlations
belong to the nonexceptional character sums; their size still matters.

## Quantitative spectral consequence, with all costs visible

Let D be the degree of P as a rational map. The folded map R=F(P) has
degree 2D; if R=A/B is reduced, deg(A)+deg(B)<=4D. For any nontrivial
multiplicative character psi of order d, the polynomial A*B^(d-1)
encodes psi(R) with zero values at both roots and poles. Its finite
geometric zero count is at most 4D and (1) ensures it is not a d-th power.
Weil's multiplicative character bound therefore proposes

    |M_R(psi)| <= delta=(4D-1)/sqrt(p),                              (3)

for uniform AFFINE input, where M_R uses the unnormalized nonzero finite
output law. The bound is valid but can be useless at large D.
This invokes the same Theorem 3.1 independently checked in the simple-pole
review; the new non-power argument, not that old review, is the dependency
requiring audit here.

For H=R^e let s be its residual mass, v_H its second moment and
g=gcd(e,p-1). M_H(eta)=M_R(eta^e) gives the exact energy decomposition

    E_mul(H)=g*s^4/(p-1)+remainder,
    0 <= remainder <= delta^2*(v_H-g*s^2/(p-1)).                    (4)

The exceptional contribution can be increased by a large g, but does not
grow just because many folds have been applied. D itself grows by 2e
on a powered stage, so the degree-dependent error in (3) must not be
priced as O(log e) or dropped. Large finite-field effects beyond that
error range remain possible and are not ruled out.

## What this resolves and the constructive escape

The concrete mechanism of accumulating geometric subgroup indices by
interleaving generic reciprocal folds and small fixed powers fails by
(1)-(2). Taking larger outer exponents still needs a useful
gcd(e,p-1), the earlier order resource, or a separate proof of large
nonexceptional correlations. Neither is supplied here.

To preserve a nontrivial perfect-power index, a replacement inner update
must change the four-fiber obstruction. For a rational outer map whose
zero/pole divisor has r distinct supporting values with multiplicities
coprime to ell, pullback divisibility requires

    r*D*(1-1/ell) <= 2D-2.                                         (5)

For ell=2, four such values are impossible; at most three are possible.
For ell>=3, already three such values are impossible (equality also fails
because of the -2). Two-value maps include powers of a Möbius coordinate,
which return to cyclic-group kernels. Three-value square-preserving
constructions can come from genus-zero covers, but must be checked for
actual planted fibers, distinct local zeros, and acquisition work.
Reducing branch values by setting y=w makes a double root and changes the
sampler rather than extending the accepted two-anchor law.

A concrete three-value alternative is investigated next: collapse the two
sampled zero values deliberately and pair the fold with the existing power.
It has a different divisor pattern and must supply a real collision/absorption
law; neither (5) nor a genus-zero parametrization is a factoring algorithm.
The independent scalar-product direction is outside this root-density analysis.

