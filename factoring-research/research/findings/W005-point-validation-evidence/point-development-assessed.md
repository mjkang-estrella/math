# W005 A — parent derivation beyond the point formula

Date: 2026-10-08. **PROVISIONAL; independent validation requested.**
This continues the lead mechanism in [W005](../hypotheses/W005.md).
No numerical experiment, curve computation or Lean execution was used.

The explicit section genuinely removes the first rational-point search:
P=(4t^2,2tsw) on y^2=x(x+b^2)(x+Delta), with
b=t(r-1/r), w=t(r+1/r), Delta=s^2-4t^2. Whether it is generically
infinite order is still for review. That does not settle the square lifts.

Write d_+=s+2t and d_-=s-2t. The inverse quartic coordinates factor as

    X=(r+1)*(d_+*r+d_-)/(4r),
    Y=s_j-X=(r-1)*(d_+-d_-*r)/(4r).

Thus finding u^2=X and v^2=Y is the simultaneous cover

    A^2=r*(r+1)*(d_+*r+d_-),    A=2r*u,
    B^2=r*(r-1)*(d_+-d_-*r),    B=2r*v.

For s>2t>0, its six distinct branch places are
0, infinity, -1, -d_-/d_+, 1, d_+/d_-. The square classes are
independent (their simple zeros differ). At 0 and infinity the two
extensions ramify together with inertia 2, not 4 over an algebraic closure.
The degree-four cover has 2g-2=-8+6*2=4, hence genus 3.
This is a smaller geometric problem than the fixed-trace genus-7 norm
cover, but not a rational parametrization or efficient point algorithm.
The second trace now varies, so this is not a contradiction of W004.

It has three genus-one quotients: the A curve, the B curve, and

    C^2=(r^2-1)*(d_+*r+d_-)*(d_+-d_-*r),    C=A*B/r.

The first two are isomorphic by r -> -1/r and the ordinate scaling r^2:
F_A(-1/r)=F_B(r)/r^4. This extra structure is a concrete possible
replacement for unstructured high-genus searching, not a granted solver.
Using a Jacobian decomposition requires its maps, rational-point recovery,
height bounds and useful-input success law to be paid.

## The immediate local obstruction

On the intended branch r=1 mod N, one has X=s=5R mod N and Y=0 mod N.
For an unknown prime p|N with 5 nonsquare mod p, no rational square u^2=X
with p-integral u can exist. This obstruction holds regardless of how many
elliptic additions are advertised for the displayed section family.

More strongly, for the literal choice r=1+N/K with K=N*s^2+1, at every
odd prime p|N the second factor d_+-d_-*r equals 4t modulo p and is a
unit. Since 4r is a unit,

    v_p(Y)=v_p(r-1)=v_p(N).

Any odd exponent in N therefore prevents Y from being a rational square.
This kills the literal section's square lift on every squarefree composite.
It is an exact valuation obstruction, not a finite failure count.

**A genuine modification, not an automatic repair:** replacing r-1 by
t*N^2/K^2 gives

    Y=(t*N/K)^2 *
      (1-(s-2t)*N^2/(4K^2))/(1+t*N^2/K^2).

The displayed factor has unit reduction 1 and even N-adic valuation, so
the immediate parity obstruction disappears. It still has to be a rational
square exactly, with K checked for units and for the original interval.
Its being a square modulo N is not sufficient. X still reduces to 5R,
so the nonsquare-5 obstruction remains.

Changing the original modular coefficients to t=cR,
s=(1+c^2)R with rational c and 1+c^2=a^2 (known rational a)
removes the nonsquare constant. But on this section u^2=X then gives
(u/a)^2=R modulo N immediately. The lift is now explicitly the desired
modular-root computation, not a free auxiliary task. Choose unit
denominators and nonzero distinct modular roots before using this observation.

## Constructive questions retained

1. Can the elliptic quotient symmetry be used to generate points of the genus-3
   cover with controlled local class and charged height, rather than only
   generate norm points? Supply an actual map/algorithm if so.
2. Can one move to another r residue class with both local square conditions
   without prescribing a hidden modular root? A conic parameter chosen using
   sqrt(R), sqrt(5R), or a hidden factor is inadmissible.
3. The norm curve's bad reduction blocks a generic-ECM justification, but a
   different curve can arise by fixing u and solving
   Z^2=f(u^2)*f(v^2). Its reduction has branch roots +/-sqrt(R),
   +/-2sqrt(R), so it has good reduction on unit branches; varying only the
   lifted s with s=5R does not vary its geometric j invariant modulo p.
   The proposed invariant is j=4*73^3/81. Check this and twist multiplicity.
   Varying t=cR changes the cross-ratio to ((c-1)/(c+1))^2.
   Is the resulting explicit point-bearing family merely an existing
   torsion-parametrized ECM family? Establish primary prior art before
   treating it as a fresh order-supply mechanism.

The point formula, genus reduction, valuation obstruction and variable-c
escape are distinct claims. None provides a new complete factoring bound.
