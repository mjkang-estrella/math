# H026 fast-product bridges: missing inputs and narrow obstructions

2026-10-08. Native Astra independent initial search, root primary-source and
mathematical check, then NEW native Sol scope audit all completed. No new paid
elliptic evaluator survived; no experiment admitted. This is not a general
lower bound on compact circuits or single-point evaluation.

## Actual literature interfaces

Bostan–Gaudry–Schost accelerates an explicitly supplied polynomial-matrix
recurrence, with matrix dimension, coefficient degree and invertibility conditions
part of its input/cost model. The factor list x(jG) does not by itself supply
such a matrix; generating or interpolating its coefficients is paid work.
Root checked the introduction, recurrence setup and algorithmic description;
Astra also read the primary construction.
[Primary paper](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf).

Bostan–Yurkevich computes polynomial-matrix products on geometric arguments.
Its Algorithm3 and parameterized analysis retain matrix size and degree; the
block-polynomial construction and geometric multipoint evaluation are not free.
Substituting elliptic translations requires an explicit valid recurrence or
coordinate bridge. Root checked Algorithm3 and its parameter analysis; Astra
read the same primary algorithm.
[Primary paper](https://arxiv.org/pdf/2012.08656).

The known structured elliptic product evaluator in H019 already gives a
soft-square-root interval route; bisection does not improve its full-range
exponent. Reproducing that construction or the corrected H025 dyadic identity
without a cheaper paid primitive does not supply a new ECDLP improvement.

## One fixed-dimensional linearization fails

Let E be a nonsingular elliptic curve in characteristic p>3, G a rational
point of odd prime order q, and alpha transcendental over the constant field.
As rational FUNCTIONS of P, set

    R_n(P)=product_(j=0..n-1)(alpha-x(P+jG)),  R_0=1.

For1<=n<q, at P=-(n-1)G the final factor has a pole of order2. Each earlier
factor is regular and nonzero there: alpha-x((j-n+1)G) cannot vanish because
alpha is transcendental. Every preceding R_m is regular at that point.
Taking the largest index in any nontrivial constant-field linear relation
therefore yields a pole that cannot cancel. Hence R_0,...,R_N are linearly
independent over the constant field containing alpha, for N<q.

This rules out placing these rational functions in a fixed-dimensional linear
space over THAT constant field for arbitrarily growing N. It does not exclude
coefficients depending on P: the trivial recurrence multiplying by the next
factor already has that dependence. Nor does it exclude compact nonlinear
circuits, other recurrences, or faster evaluation at one fixed P. Specializing
alpha may introduce cancellation and invalidates this proof's nonvanishing
premise. Do not repeat the old function-versus-single-point quantifier error.

## Two specific coordinate substitutions fail at low degree

Suppose a nonconstant rational function z satisfies the FUNCTION identity
z(P+G)=gamma*z(P), with nonzero gamma in the constant field. Translation by G
has geometric orbits of length q, and the zero/pole divisors of z are invariant
with their multiplicities. Thus q divides deg(z), and deg(z)>=q. Iterating
also requires gamma^q=1. Constant-field extension or inseparability does not
remove the divisor argument. Letting gamma depend on P does remove its premise.

If z(P+G)=z(P)+1 as a function identity and q!=p, iterating q times gives the
contradiction q*1=0. Neither statement concerns an encoding required to hold
only on a finite rational-point set. In particular, degree>=q is NOT a lower
bound on evaluation/circuit complexity: high-degree functions can have short
circuits. These results reject only the specified low-degree multiplicative
or additive coordinate substitutions, not every geometric or nonlinear bridge.

## Disposition and review

An actual matrix/circuit with efficiently constructed coefficients, costed field
extensions, zero handling at detected roots and index recovery would be a new
candidate to examine. None emerged in this pass. Testing an unspecified fast
product oracle would not advance the goal, so no numerical run or broad Lean
work is admitted. Known evaluator/ordinary square-root reference unchanged;
verified complete-work improvement NONE.

Astra proposed the two scoped obstructions; root checked the poles/divisors and
read the primary interfaces. Independent Sol explicitly checked cancellation,
constant-field extensions, inseparability, gamma^q=1 and the P-dependent
coefficient escape, returning GO only for the narrow claims. No delegated
agent executed experiments, edited files or created children. No formal Lean
theorem is asserted by this informal independently checked finding.
