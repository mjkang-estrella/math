# W007 — varying earlier coefficients instead of searching one fixed fiber

2026-10-08. Parent constructive continuation. PROVISIONAL; independent task A
audits only the original fixed degree-eight cover and basic laws. This note
changes the acquisition computation and must not be claimed as part of A's
completed work. No numerical search or new factoring bound.

## An explicit joint construction condition

Keep P_2(X)=X(X-1)(X-2)(X+1). Define the rational split-value set S by

    t in S iff P_2(X)-t has four distinct rational roots.

Writing s^2=1+t, complete splitting is equivalent to rational A,B with

    A^2=5+4s, B^2=5-4s, hence A^2+B^2=10,

with the repeated-root exceptional values removed. Conversely every such
circle point gives t=((A^2-B^2)/8)^2-1. The circle has the rational
parametrization obtained by rotating (1,3):

    A=(1-u^2-6u)/(1+u^2),
    B=(3-3u^2+2u)/(1+u^2).

This is a paid constant-size rational computation, not a rational-point oracle.

Instead of fixing a_2=-504/625 and searching one fiber of that P_3, choose
three members t_1,t_2,t_3 of S satisfying

    t_1+t_2=t_3.

Require t_1,t_2,t_3 nonzero, t_1!=t_2, and all four fibers at
0,t_1,t_2,t_3 simple. Nonzero t_1,t_2 and t_1+t_2=t_3 already make those four
values distinct once t_3!=0 and t_1!=t_2. Set

    a_2=t_3,   a_3=-t_1*t_2,
    P_3=P_2*(P_2-t_3),
    P_4=P_3*(P_3+t_1*t_2).

Then the exact identity

    P_3+t_1*t_2=(P_2-t_1)*(P_2-t_2)

makes P_4 the product of FOUR disjoint completely split quartic fibers:
P_2, P_2-t_1, P_2-t_2, P_2-t_3. It therefore has sixteen distinct rational
roots and a four-stage evaluator. This is an explicit sufficient AND, for
this particular nested shape with fully split intermediate fibers, necessary
condition. The existence/acquisition of a nontrivial additive triple is not
asserted. t_1=0, t_2=0, t_1=t_2 and t_3=0 are not acceptable shortcuts.

The fixed genus proposed in the original brief would not by itself obstruct
this varying-a_2 construction. Conversely, replacing a fixed curve by a
higher-dimensional equation does not supply a point or a scalable algorithm.

## Connection to a concrete primary-literature construction

If two monic degree-d polynomials split over Q and differ by a nonzero
constant, their root lists have equal power sums through degree d-1, by
Newton identities. Conversely such equal power sums force equality of all
nonconstant coefficients. Thus each completely split new fiber is an
ideal Prouhet-Tarry-Escott pair after clearing denominators. This is an
elementary equivalence, not a new result.

A primary paper to inspect is Ajai Choudhry, "Ideal solutions of the
Tarry-Escott Problem of degree seven", arXiv:2207.12726. Its abstract reports
parametric ideal size-eight solutions; the parent has NOT inspected its
formulas or claimed they give this nested construction. A second bounded
source is Coppersmith–Mossinghoff–Scheinerman–VanderKam,
"Ideal solutions in the Prouhet-Tarry-Escott problem", arXiv:2304.11254.
Do not infer a uniform all-size construction from their finite sizes.

There is a precise compatibility test for using a symmetric size-eight pair.
Translate the common root center to zero. Write the first even polynomial as

    Q(Y)=Y^4+B Y^3+C Y^2+D Y+E,   with Y=X^2.

It is a composition of two monic quadratics exactly when

    D=(B/2)*(C-B^2/4).

Indeed expanding (Y^2+uY+v)^2+w(Y^2+uY+v)+z gives B=2u and
D=u(C-u^2); conversely v can be chosen and w,z recovered.
A general ideal size-eight pair need not satisfy this condition. The second
quartic has the same B,C,D and therefore satisfies it whenever the first does.

Equivalently, the four squared positive-half roots admit a pairing with
equal pair sums. If x_1^2+x_2^2=x_3^2+x_4^2=H and the y-half roots have the
same property, their second-power sums already agree. Matching fourth-power
sums also matches sixth-power sums, since for x^2+y^2=H,

    x^4+y^4=H^2-2x^2*y^2,
    x^6+y^6=H^3-3H*x^2*y^2.

This reduces the symmetric ideal constraints to matching sums of two
squared coordinate products while maintaining rational circle points.
It is a more specific construction target than "find an ideal PTE solution".

A bounded source-and-algebra audit should decide whether a published
parametric family satisfies, or can explicitly be specialized to, this extra
composition condition without collapsing the two root sets. If so, give the
actual coefficients and denominator/degeneracy conditions. If not, identify
the additional equation instead of claiming that PTE prior art solves it.
Either outcome is still a finite-stage result, not scalable factoring.

## Costs and what would change the research conclusion

If an explicit rational additive triple or compatible published family is
obtained, its coefficient circuit can be reduced modulo N after gcd-testing
denominators. No list of sixteen roots is needed to evaluate P_4, although
root distinctness modulo an unknown p still needs proof or exception handling.
For general depth, useful local coverage, noncollapsed roots, circuit size,
coefficient acquisition and a separating factor law all remain required.
Finite degree-eight/sixteen formulas are a way to test actual algebraic growth,
not evidence of polynomial-time factoring or an improvement over NFS.

No experiment is authorized here. In particular do not replace this gate by
a broad rational-height sweep whose growing search cost is hidden.

