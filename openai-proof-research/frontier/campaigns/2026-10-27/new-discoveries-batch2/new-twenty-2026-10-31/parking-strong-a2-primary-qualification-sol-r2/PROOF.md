# Personal second qualification: ordinary proof and generic construction

MathDB 323531. GPT-6.1 Sol high/default, no children, mathematical software or formal execution. This checks a disclosed proof, not independent invention. Credit 0.

## Audit of the supplied first proof

I read inputs/review-r1-PROOF.md before FULLCANDIDATE.md and checked every step by hand. No mathematical error found. The c weights are 10 and -2, both 1 modulo 3; swap exchanges the coordinates. The pure monomials prove independence. Nonzero common zeros would imply x^6=-3y^6 and y^6=-3x^6, hence 8x^6=0. Thus the pair is an hsop under the actual source definition, not merely a pair of covariants. The real form y=conjugate(x), contragredient rotation, and swap give genuine irreducible real A2 with h=3. The map preserves that real form.

For F=Theta-id, yF1-xF2=xy(x^3-y^3)^3/4. Axis fixed points solve t^9=4; off-axis points have y=rho*x, rho^3=1, and x^9=1. This gives exactly 1+18+27=46 rather than 100. The cases are disjoint and exhaustive. The derivative at the origin is -I and at each nonzero axis point is diag(9,-1), up to swap. At off-axis points the local ideal is (F1,(x^3-y^3)^3), since x,y are units. The divisor x^3-y^3 is smooth there and F1 restricted to its line has nonzero derivative 9 in a radial coordinate. Consequently the local quotient has length 3. Total lengths are 1+18+27*3=100. At (1,1), DF has all entries 9/2; it has rank one. No inference from singularity alone was substituted for this count/local-length argument.

Simultaneous compatible basis change preserves the ideal. Homogeneity supplies Z9 stability. The universal conjunction fails in its cardinality clause, without needing to negate the parking bijections separately. This does not refute Intermediate, Generic Strong or Weak.

## Short generic pencil, with the missing hsop intersection paid

Use the actual dihedral coordinate convention of the original Section 5.1, p22. For any m>=3 put d=3m+1 (k=3) and, for t!=-1, set

 T_t(x,y) = ((x^(3m+1)+t*x^(m+1)*y^(2m))/(1+t),
             (y^(3m+1)+t*y^(m+1)*x^(2m))/(1+t)).

Both monomials in the first component have c-weight 1 mod m, and swap exchanges components. The pure powers give an injective equivariant copy of V*. On an axis their only common zero is the origin. Off axes common zeros require X+tY=Y+tX=0, where X=x^(2m), Y=y^(2m). Thus t^2!=1 is sufficient and necessary for the hsop condition (t=1 gives a nonzero common factor, t=-1 is outside this normalization). The pencil's hsop parameter locus is precisely C minus {1,-1}.

Every T_t fixes v=(1,1). The radial and transverse eigenvalues of DT_t(v)-I are respectively

 3m,  m*(3-t)/(1+t).

Hence its determinant is 3*m^2*(3-t)/(1+t). It is not constant on the hsop parameter locus and vanishes at t=3, which remains an hsop. At t=0 the map is the pure-power map: every fixed point is simple. Thus the global nonreduced parameter set is proper and nonempty inside the hsop locus; the determinant above detects its intersection on a fixed-point section, without needing an equation for the entire global discriminant. Non-constant determinant along this section alone would not suffice without checking t=3 is hsop. We checked that explicitly.

Apply the actual Jacobian criterion in supplied Evidence p20: for an hsop, a fixed point with eigenvalue 1 of DT is nonreduced. Finiteness also follows directly at t=3 from

 y*T_3,1-x*T_3,2=xy*(x^m-y^m)^3/4.

The fixed points comprise origin, 6m axis points, and m ratio lines with 3m nonzero roots on each: 1+6m+3m^2, less than (3m+1)^2 by 6m^2. For m=3 these are exactly the assigned degree-10 polynomials and the count 46. This is one family, not additional credit. The disclosed witness supplied the monomial pattern; I claim no independent invention of it.

This is a complete elementary collision construction uniformly across rank-two dihedral types, with the source Jacobian criterion supplying the endpoint. It is not a bare dimension-count argument and does not establish an all-rank theorem. Rank one is a genuine obstruction to any every-rank claim: alpha*x^(2k+1)-x has only simple roots for every nonzero alpha. I have not proved a general rank>=2 interpolation theorem. That additional theorem is unnecessary for refuting this universal conjecture.

## Why k=1 and k=2 differ in A2

Rotation weights and swap describe ALL equivariant maps in these degrees, not just a restricted symmetric subfamily. In degree d=3k+1, a monomial x^(d-j)y^j has weight 1 iff j=0 mod3. The other component is its swap.

At k=1 write theta1=A*x^4+B*x*y^3 and theta2 its swap. A=0 fails hsop on an axis. If A=B, both components share x^3+y^3, also failing hsop. Otherwise

 y*theta1-x*theta2=(A-B)*xy*(x^3-y^3).

The projective fixed directions (axes and three ratio lines) are simple. At each such direction the restriction of Theta is a nonzero scalar times the fourth power, because hsop prevents its being zero there. The nonzero radial fixed roots are simple (radial derivative 3), and a simple projective direction gives a nonzero transverse derivative of Theta-id. More explicitly in a local chart (r,z), the ideal is generated by a radial equation and r times the directional equation, multiplied by units at a nonzero fixed point. Its Jacobian is invertible when those two derivatives are nonzero. Origin has derivative -I. So every allowed degree-four map is reduced.

At k=2 write theta1=A*x^7+B*x^4*y^3+C*x*y^6 and theta2 its swap. Again A!=0 is necessary. If A=C, Theta=(x,y)*(A*(x^6+y^6)+B*x^3*y^3), sharing a nonconstant scalar factor with a nonzero complex zero, so not hsop. Otherwise

 y*theta1-x*theta2=(A-C)*xy*(x^6-y^6).

The eight projective fixed directions are simple, radial restrictions are nonzero by hsop, radial derivative is 6, and the same local-chart argument proves reducedness everywhere. Thus the degree-seven common-factor problem is real for the entire A2 equivariant space. At degree ten the extra coefficient separates the collision equation from the resultant obstruction; the displayed pencil makes that separation explicit.

## Proposition 4.4

For the assigned witness, v=(1,1) is on the reflecting flat x=y and has ambient length 3. Restriction to the flat gives t^10-t and a simple root at 1. Restriction-simple does not imply ambient-simple: the missing normal derivative vanishes. This disproves the multiplicity-one clause of the printed supplied Proposition 4.4, not necessarily its set-theoretic injection. The later table conflict cannot be resolved by calling this a failure of the hsop premise.
