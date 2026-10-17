# Reconstructed moving-point obstruction

Myeongjin Kang; no affiliation. CC BY 4.0 prose; MIT original code.
This is a supporting calculation, not a G4 solution or refutation.

Use the pinned degree-three manuscript's exact notation:
L=Q_5(zeta), pi=1-zeta, F(x,y)=(x-1)^5-xy^4+y^5+zeta,
A=(V[x,y]/F)_(pi,x,y), and D=L[t]/((t-1)^5+zeta).
The source proves N_D/L(t)=pi and supplies beta in K2(L;Z/5),
with coefficient boundary [zeta], and the norm detector lambda_L on K3(L;Z/5).

Set K=L(z). On C_K, intersect the affine chart with y=z. Its coordinate
field is E=K[x]/F(x,z). To verify that it is a field, take the pi-Gauss
DVR in K. The monic polynomial F(x,z) reduces to x^5-xz^4+z^5.
Since z is a nonzero element of F5(z), substituting s=x/z reduces its
irreducibility to s^5-s+1. The root's Frobenius orbit over F5 has length
five, and an irreducible polynomial over F5 remains irreducible over
F5(z). Thus the reduction is irreducible and separable. The monic
polynomial is irreducible over K. The corresponding unramified extension
of the Gauss valuation has residue field F_{5^5}(z) and residue degree 5.
The constant field has 3125 elements, NOT 125.

The closed point q_z is omitted from Spec B0[1/pi], where
B0=A[z]_(m_A A[z]): y-z lies outside m_A A[z] (its z coefficient is -1),
so it is inverted in B0 and vanishes at q_z.

There is a different valuation, at z=0. The finite free algebra
L[z]_(z)[x]/F(x,z) has residue field D, because F(x,0) is the source
Eisenstein polynomial. Its discriminant is a unit at z=0: that
characteristic-zero polynomial is separable. It is therefore a DVR
unramified over L[z]_(z), with uniformizer z and residue field D.
Here x is a unit and reduces to t.

Consider a=beta_E * [x] * [z] in K4(E;Z/5). The localization boundary
at z=0 is, up to the fixed product convention sign, beta_D * [t].
Compatibility of finite transfer and localization gives

 lambda_L(partial_z Tr_E/K(a))
   = +/- lambda_L(Tr_D/L(beta_D * [t]))
   = +/- v_L(N_D/L(t)) = +/-1 in Z/5.

The last equality is precisely the stipulated source norm detector.
The desired suspended distinguished class has the same detector value:
partial_z Tr_D(z)/K(beta_D(z)*[t]*[z])=+/-Tr_D/L(beta_D*[t]).
Hence this iterated detector does NOT annihilate all coefficient classes
at omitted points, even though their pi-Gauss residue degree is 5.
The two valuations must not be conflated.

This does not produce a localization relation equating the two supported
classes. It also does not show that a is the reduction of an integral
K4(E) class. Its coefficient boundary is +/-[zeta]*[x]*[z] in K3(E),
whose vanishing has not been established. Thus an integral-localization
refinement is a separate possibility, not defeated by asserting that a
already lifts. No claim that c*[z] is zero in K4(B0) is made.
