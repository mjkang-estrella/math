# H047 nonsplit residual pairs: projection collision lacks scalar extraction

2026-10-09 UTC. Bounded coordinate-construction screen. Supported ECDLP
exponent1/2; verified complete-work improvement **NONE**. No experiment.

## Concrete proposed operation

Let E:y²=f(x) over Fp, p>3, with full rational group of odd prime order q.
Choose labelled finite anchors A,B with distinct abscissae. Let l(X) interpolate
their ordinates and choose nonzero c in Fp. Intersect E with

    y = l(x) + c(x-x(A))(x-x(B)).

Squaring and subtracting f gives a degree-four polynomial, with prescribed
roots x(A),x(B). Dividing by their factors leaves a quadratic. Dispatch repeated
roots, tangencies and other degeneracies explicitly. If the residual quadratic
is irreducible, adjoining a root gives conjugate points R,pi(R) over Fp².
Here pi is p-power Frobenius, not scalar multiplication by p.

The function y-l(x)-c(x-x(A))(x-x(B)) has pole order exactly four at O:
its quadratic x term has order four, while y has order three. In the four
simple-zero case its divisor is (A)+(B)+(R)+(pi R)-4(O). Thus

    T=R+pi R=-A-B

already has an affine label in G,Q. This is standard divisor/group-law
content, supported by [Galbraith, Theorems 7.9.8–7.9.9](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch7.pdf),
read by the proposer and root. Frobenius and its rational fixed points are
standard; see [Chapter 9, Example 9.6.14](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf).
No new complexity theorem is attributed to either source.

The attempted extra detector stores U=R-pi R, with pi U=-U, and searches
for signed collisions between residual pairs. Fixed-degree interpolation,
quadratic factorization, consistent extension representation, Frobenius,
subtraction, storage and exact confirmation are all executable and paid.
Neither residual splitting frequency nor distribution of U is assumed uniform.

## Exact failure of the immediate label-recovery bridge

Suppose U_1=U_2 and put D=R_1-R_2. Rearrangement gives pi D=D, hence D is
rational. Adding each point to its conjugate then gives

    2D=T_1-T_2.

Because the full rational group has odd prime order, halving is unique there:

    D=[2^(-1) mod q](T_1-T_2).

This is a point with an affine label already determined by the anchor traces.
It is not a new zero relation with a nonzero unknown-scalar coefficient.
Computing the same labelled point by extension coordinates is not itself a
way to recover its discrete logarithm. For U_1=-U_2, the analogous rational
point is R_1+R_2 and the trace identity uses T_1+T_2. Requiring full equality
R_1=R_2 also forces T_1=T_2, an ordinary collision of labelled trace points.

The full odd-order rational-group assumption matters for unique halving;
do not transfer that step to arbitrary cofactors without handling rational
two-torsion. The calculation does not exclude nonlinear use of residual
coordinates, a further specified constraint, or an improved way of producing
ordinary useful trace collisions. None of those extra operations or cost laws
was supplied in this attempt.

## Disposition and process

Park this immediate antisymmetric-projection extraction rule. It adds paid
extension work without an established useful scalar equation, so timing its
collision rate would not test an improved solver. The cheapest falsifier is
the exact trace equation above, before any sampling. No broad theorem against
multiple residual points or coordinate-aware algorithms is claimed.

Proposer: native Astra /root/h007_additive_relations, explicit fallback for
Claude's failed H047 coordinate task. Claude returned only repeated API errors;
this result is attributed to Astra. The failed handle and original brief are
in H047-independent-briefs.md. Root independently checked pole order, residual
conjugacy, the two projection equations and the exact scope of scalar extraction.

No scripts/imports/experiments, seeds, new curves, Lean claims or Audit changes.
H034 cap untouched. Project validation is recorded in STATE and does not
certify this paper proof. Next decisive evidence would be a different explicit
recovery constraint with paid operations and a credible complete-work advantage.
