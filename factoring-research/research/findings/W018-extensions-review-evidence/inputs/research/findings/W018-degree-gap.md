# W018 follow-through: a degree gap for bounded integer-valued grid polynomials

Parent derivation, 2026-10-08; NOT yet independently reviewed or Lean-proved.
Verified new complete factoring improvement: NONE. W018's powered-base
preparation removes one denominator-order obligation, so growing-degree
integer-valued approximants deserve another look. This note tests that actual
escape rather than assuming W014's fixed/polylog-degree obstruction covers it.

## Elementary finite-difference lemma

Let H,d be positive integers with 2<=d<=H/8. Let R be a rational polynomial
of exact degree d, integer-valued at every integer in [0,H], and suppose
|R(j)|<=V on that grid. Then

    V >= H^2/128.                                        (1)

Proof. Set m=floor(H/d), so d*m<=H and m>=H/(2d). The d-th finite difference
at step one is d! times the leading coefficient. It is a nonzero integer c,
since it is an integer linear combination of R(0),...,R(d). At step m the
same leading-coefficient identity gives

    Delta_m^d R(0)=m^d*c.

The absolute binomial weights of the d-th difference sum to 2^d. Hence

    m^d <= |Delta_m^d R(0)| <= 2^d*V,
    V >= (H/(4d))^d.

Because H>=8d, the latter is at least

    H^2 * 2^(d-6)/d^2 >= H^2/128.

The last inequality is d^2<=2^(d+1), valid for every integer d>=2: check
d=2,3, and induct using (d+1)^2<=2d^2 for d>=3. This proves (1) without a
real-interval norm inequality, fixed degree, or a Markov derivative estimate.
Only the explicitly used grid values must be integers.

## Apply it after subtracting an integer tangent line

Suppose A is rational-coefficient and integer-valued at 0,...,H, and

    |A(j)-q*N/(X+j)|<=E,       N,X,q>0, E>=0.

Choose integers c,a nearest respectively to q*N/X and -q*N/X^2. Put
R(h)=A(h)-(c+a*h). The exact reciprocal identity is

    q*N/(X+h) = q*N/X - q*N*h/X^2
                + q*N*h^2/(X^2*(X+h)).

Therefore on the grid

    |R(j)| <= V0 := E+1/2+H/2+q*N*H^2/X^3.              (2)

If V0 < H^2/128, (1) rules out EVERY degree from 2 through H/8. Consequently

    degree(A)<=1, OR degree(A)>H/8.                       (3)

Unlike the earlier derivative argument, this addresses a large intermediate
range of growing degrees. For the balanced W014 parameters
N~X^2, H~X^(3/5), q=O(X^(1/5)), E=O(X^(2/5)), condition (2) holds for
sufficiently large X (with fixed implied constants). Thus merely increasing
degree to X^(1/5), for example, does not escape to a useful bounded integer
polynomial; it is still in the excluded interval.

For a sparse progression p=X+m*h, the identical argument replaces the final
term of V0 by q*N*m^2*H^2/X^3. It must be applied in the sparse h-grid,
not in the original p-grid. A large stride can remove the small-curvature
premise, but that stride and coverage are paid inputs in W016/W018.

## Computational meaning and precise limits

In the existing explicit-degree consumer, a degree greater than H/8 costs
at least that many dense coefficient/root-processing slots (or the specified
degree-dependent routine's corresponding cost). That is worse than the
O~sqrt(H) candidate-product comparator on the same supplied progression.
This statement concerns the explicit implementation, not an unconditional
lower bound on sparse or circuit representations of all high-degree polynomials.

For example binomial(h,H) is succinct and vanishes on 0,...,H-1 despite its
large degree. It shows why (3) has a high-degree alternative. A candidate using
such circuits must provide cheap public negative-offset evaluation, denominator
preparation, collision processing and integer recovery; the current dense
root routine cannot simply be assigned polylogarithmic cost. This note proves
no lower bound on all such new routines.

The removed assumption to target next is global integer-polynomial behavior
on a full grid. Piecewise polynomials, nonpolynomial integer circuits and
certified retained domains are different computations; each must pay its
pieces, carries, membership/coverage and output recovery. W018's base primitive
may still help them. The degree gap does not resolve those constructions or
the factoring goal.
