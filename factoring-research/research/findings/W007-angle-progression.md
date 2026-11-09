# W007 — an explicit angle-progression attempt, symbolically rejected

2026-10-08. Parent constructive calculation, PROVISIONAL pending any later
audit. No candidate search or experiment; no new factoring bound. This is
an attempted actual formula for the additive triple, not a point oracle.

Represent a rational point (A,B) on A^2+B^2=10 as a rational rotation of
(1,3). Trigonometric notation is only shorthand for rational circle
identities: write A=sqrt(10) cos(theta), B=sqrt(10) sin(theta). Then

    tau(theta)=(25*cos(4theta)-7)/32.

For the base angle theta0 of (1,3),

    cos(4theta0)=7/25,    sin(4theta0)=-24/25.

Try the one-parameter construction

    theta1=theta0+phi, theta2=theta0-phi,
    theta3=theta0+2phi,

with cos(phi),sin(phi) rational, so every A_i,B_i is rational at constant
arithmetic cost. Let c=cos(4phi), s=sin(4phi), also rational. Substitution
into tau(theta1)+tau(theta2)=tau(theta3) simplifies exactly to

    c*(7c+24s-7)=0,    c^2+s^2=1.

The c=0 case would require cos(2phi)^2=1/2, impossible for a rational
rotation. The line 7c+24s=7 meets the unit circle in exactly

    (c,s)=(1,0), or (-527/625,336/625).

The first gives only zero split values. The second is the fourth power of
the rational unit (4+3i)/5. Its other fourth roots differ by units
{1,-1,i,-i}, which do not change any of these tau values. Taking that
rotation explicitly gives

    (A1,B1)=(-1,3),
    (A2,B2)=(13/5,9/5),
    (A3,B3)=(-13/5,9/5),

hence

    (t1,t2,t3)=(0,-504/625,-504/625).

This violates the nonzero/disjoint-fiber requirement. The complete proposed
rational rotation progression therefore supplies no acceptable additive
triple, at any parameter height. It recovers the known eight-root example.

The failed assumption is that the simplest shared-angle identity would
produce a nontrivial additive relation among split values. It instead
forces a symmetry of the known zero fiber. A different computation would
need at least an independently varying rotation or a new circle-product
identity; naming the resulting higher-dimensional equation is not a
generator. Do not expand a height sweep of this rejected progression.
This bounded rational probe remains secondary to finite-field acquisition.

