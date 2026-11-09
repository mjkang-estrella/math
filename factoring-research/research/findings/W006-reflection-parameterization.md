# W006 B — explicit parameterization of the two-reflection generator

Date: 2026-10-08. PROVISIONAL parent calculation, symbolic only.
This supplies an actual generator for W006 B's final orthogonality equation;
it is not a useful-output or complexity theorem.

Given primitive integer quaternion A, Norm(A)=N odd, put B0=i*A.
Choose nonzero integer C and an integer parameter vector E. Define

    c=Norm(C), d=Norm(E),
    a=<A,C>, b=<B0,C>, f=<A,E>, e=<B0,E>, h=<C,E>,
    S=a*b*d+c*e*f-2*b*f*h,
    D=S*C+c*(b*f-a*e)*E.                                (P1)

Reject C=0 or D=0. Reflect B0 first in C, then in D. Use exact rational
arithmetic, checking every norm denominator; proper gcds with N are factors.
The resulting B2 has norm N, and the claim is that <A,B2>=0 identically.
Check final integrality coordinatewise before using the accepted twin
extraction, or directly use the modular denominator-cleared pair where valid.
Input direction heights, generation, every rejection and all arithmetic count.

Derivation: B1=R_C(B0), z=<A,B1>=-2ab/c. Define the quadratic form
Q(V)=z*Norm(V)-2<A,V><B1,V>. The condition R_D(B1) perpendicular to A
is Q(D)=0. C is a known rational point because reflecting again returns B0.
Its polar form satisfies B_Q(C,E)=b*f-a*e, while Q(E)=-2S/c.
The standard second intersection of the line through C in direction E is
Q(E)*C-2B_Q(C,E)*E. Multiplying by -c/2 yields (P1), without needing an
unknown prime or any root computation.

This replaces solving a quadratic equation by a fixed-degree formula.
It still supplies rational points rather than guaranteed integral, useful
twins. For b-bit C,E and n-bit input, the constant-degree construction has
poly(n+b) time and O(n+b)-bit expressions before any unbounded loop.
A fixed coordinate box and lexicographic or uniform sampling would be an
actual finite procedure; no useful density for such a box is granted.

There is a specific possible obstruction, not yet a theorem: modulo p|N
the orthogonal norm-N quadric is degenerate. A parametrization through the
known trivial twin might always land on the same opposite component whenever
all its chart/denominator values are units. Mixed components may occur only
when a scalar already has a proper gcd with N. This would mean that the
polynomial formula does not hide an unproved exact-shell oracle, but still
cannot produce useful CRT component mixing on its generic branch.

The requested audit should decide that statement by explicit quaternion or
local-matrix identities, including repeated primes and nonunit parameters.
Do not infer it from generic geometric language or from a small failed sample.
In particular, the larger claim that every rational orthogonal transformation
with unit denominators is useless is false: earlier D exhibited two-sided
transformations on already factored inputs. Here the claim concerns the
specified parameterization and its chart, not every transformation.

If the generic branch collapses, the constructive replacement must change
how components are acquired, not merely increase the direction box or compose
more reflections that fix A. A full norm-N sampler exists cheaply, but its
accepted independent-pair match law is still Theta(N^(-1/2)); a changed
correlation law or a different computation is needed.
