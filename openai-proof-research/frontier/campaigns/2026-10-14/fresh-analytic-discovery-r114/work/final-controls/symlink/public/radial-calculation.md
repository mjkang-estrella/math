# Source353: critical radial orbit and angular feasibility

Original author calculations, made BEFORE any target freeze. No target is frozen, no candidate is nominated, and no mathematical or contribution gate is assigned. This note does not claim a new construction of an affine-maximal graph. It analyzes the specific normalized graph already supplied by the pinned source. All its source operations are stipulated true, not audited.

The principal source is [the October 5 smooth dimension-ten construction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-Nonquadratic-Affine-Maximal-Graph-in-Dimension-Ten-October-5-2026/build/source/main.tex), Proposition `prop:reduction`, Lemmas `lem:local`, `lem:autonomous`, `lem:box`, and Proposition `prop:global`. The exact bytes and complete-tree Git blob are in the private receipt. The earlier r28 affine-completeness calculation is an antecedent, not rediscovered here.

## 1. The exact paid system

The source supplies positive smooth radial F,P on R^9, F(0)=P(0)=1, y=F'>0 and y'>0 for r>0, satisfying

    y^8 y' = r^8 F P^(-12/11),
    (y^8 P')' = -11 r^8 P^(-1/11).

It supplies the entire smooth affine-maximal graph u(x,t)=sqrt(F(|x|)^2+t^2), with positive Hessian. Put s=log r and

    A=rF'/F, B=rF''/F', D=(-rP'/P)/B.

For z=(A,B,D), the autonomous vector field V is

    A'=A(1+B-A),
    B'=B(9+A+(12/11)BD-9B),
    D'=(11-D)A-8D+BD(1-D/11).                 (1)

Primes in (1) mean s derivatives. The source already proves that the normalized orbit stays in the cooperative box

    0<=A<=9/2, 0<=B<=7/2, 0<=D<=33/7.         (2)

This paid invariant region, not a newly supplied global existence argument, is essential below.

## 2. Monotone approach to the critical corner

The source origin integrals give the following expansions, including their differentiated versions, since they are smooth functions of r^2:

    F=1+r^2/2+O(r^4), P=1-11r^2/18+O(r^4),
    F'=r+(7/66)r^3+O(r^5),
    A=r^2+O(r^4), B=1+(7/33)r^2+O(r^4),
    D=(11/9)r^2+O(r^4).                       (3)

For example F P^(-12/11)=1+(7/6)r^2+O(r^4), and integrating the first source equation gives (F'/r)^9=1+(21/22)r^2+O(r^4). Thus all three components of dz/ds are positive sufficiently near r=0.

Along the orbit, dz/ds solves the linear variational equation v'=DV(z)v. The off-diagonal entries of DV are nonnegative on (2), as explicitly computed in the source. Multiplying by an integrating factor in each scalar equation shows that positive initial components stay positive on every finite time interval. Hence A,B,D are strictly increasing. They are bounded by (2), so they converge to a stationary point. Stationarity follows from continuity of V: a nonzero limiting derivative would contradict convergence.

At the limit A>0, B>1 and D>0. The first two stationary equations give A=1+B and D=(11/12)(8B-10)/B. Substitution into the third gives exactly

    V_3 = 55(2B-7)^2/(36B).

Consequently the limit is

    z_*=(9/2,7/2,33/7).                        (4)

The orbit remains strictly below this corner at finite time. Indeed the difference from the stationary corner solves a linear equation whose coefficients are averages of DV on the segment joining the orbit to the corner. That segment lies in the box, so the same positive-cone argument preserves every initially positive difference.

## 3. The zero eigenvalue and its quadratic coefficient

Let e=z_*-z, so e has positive components and tends to zero. The Jacobian at (4) is

    J=[ -9/2,  9/2,       0      ]
      [  7/2, -27/2,     147/11 ]
      [ 44/7, 132/49,   -12     ].

Its characteristic polynomial is lambda(lambda+15)^2. Choose

    v=(1,1,110/147)^T,
    ell=(14/25,6/25,147/550).

Then Jv=0, ell J=0 and ell v=1. Let a=ell e>0 and w=e-av, so ell w=0. Positivity of ell and e makes a comparable with |e|. This eliminates a possible purely stable orbit; no generic center-manifold assertion is being used in its place.

Write V(z_*+h)=Jh+Q(h)+C(h), with Q and C homogeneous of degrees two and three. Direct substitution gives

    Q(v)=(0,20/7,-2530/3087)^T,
    ell Q(v)=7/15.                            (5)

Therefore

    e'=Je-Q(e)+C(e),
    a'=-ell Q(e)+ell C(e),
    w'=Jw+O(a^2).                             (6)

All constants here are fixed for this normalized three-variable polynomial system. These identities are checked using rational arithmetic in checks.py; the asymptotic argument is independent of those finite checks.

## 4. Stable elimination with an explicit slow-variable argument

On ker ell the semigroup of J satisfies

    ||exp(tJ)|| <= C(1+t)exp(-15t), t>=0.

This follows from the characteristic polynomial and the splitting by the rank-one projection v ell; the restriction has (J+15I)^2=0. From (6), |a'|<=C a^2 at late times. Thus a(s)>=c/(1+s), after shifting the initial time, by integration of |(1/a)'|<=C. Also |(log a)'|<=Ca tends to zero. Given epsilon>0, for s>=u>=s0 sufficiently late,

    a(u)<=a(s)exp(epsilon(s-u)).

Variation of constants in the stable equation gives w(s)=O(a(s)^2): use this last inequality in its integral, choose 2epsilon<15, and bound the initial exponentially decaying term using a(s)>=c/(1+s). All estimates are on the actual orbit, not on an unproved invariant graph.

Substituting e=av+O(a^2) into (6) and using (5) now yields

    a'=-(7/15)a^2+O(a^3).                      (7)

For large s this gives two-sided multiples of a^2 for -a', so a is comparable with 1/s. Integrating (1/a)'=7/15+O(a) then gives

    a(s)=15/(7s)+O(log s/s^2),
    e(s)=15v/(7s)+O(log s/s^2).                (8)

In particular

    A=9/2-15/(7s)+O(log s/s^2),
    B=7/2-15/(7s)+O(log s/s^2),
    BD=33/2-110/(7s)+O(log s/s^2).             (9)

The coefficient in the last line uses (7/2)(110/147)+33/7=22/3.

## 5. Consequence for the particular normalized radial solution

Integrating d log F/ds=A and d log P/ds=-BD, the remainders in (9) are integrable at infinity. There are finite positive constants c_F,c_P, depending only on this normalized source solution, such that, as r tends to infinity,

    F(r)=c_F r^(9/2)(log r)^(-15/7)
          [1+O(log log r/log r)],
    P(r)=c_P r^(-33/2)(log r)^(110/7)
          [1+O(log log r/log r)].              (10)

The constants satisfy

    c_P=[(7/2)(9/2)^9 c_F^8]^(-11/12),        (11)

by the exact determinant equation and F'=AF/r, F''=BF'/r. This is not an effective evaluation of c_F. All assertions concern precisely the existing radial example and all sufficiently large real radii, without passing to a subsequence.

Equation (10) shows why assigning a fixed nonzero coefficient to the naive r^(9/2) asymptotic would be incorrect for this orbit. It does not obstruct any nonsymmetric affine-maximal graph. The global existence and critical box were already paid by the source; monotone flow comparison, stable variation of constants and scalar integration finish this radial calculation. This note does not offer (10) as a substantial campaign candidate or retroactively freeze it after proving it.

## 6. A distinct angular calculation, and exactly what it does not prove

To test whether the radial construction leaves an accessible nonradial construction, linearize the source's exact reduced equations

    det D^2F = F P^(-12/11),
    tr((D^2F)^(-1)D^2P)+11P/F=0             (12)

at its singular homogeneous profile F_0=C r^a, P_0=D r^(-c), with a=9/2, c=33/2 and the determinant normalization. This is a calculation at the singular profile, NOT a linearization at the complete smooth source orbit, whose logarithmic corrections were just computed.

Let Y be a spherical harmonic of degree l on S^8, L=l(l+7), and take relative perturbations

    delta F=F_0 A_0 r^lambda Y,
    delta P=P_0 B_0 r^lambda Y.

For any real or complex exponent q define

    S(q)=(4q^2+108q-14L)/63,
    T(q)=(220q^2-1452q+154L)/189.

These formulas follow by separating the radial and tangential eigenvalues of D^2F_0: a(a-1)F_0/r^2 and aF_0/r^2. The radial and tangential eigenvalues of (D^2F_0)^(-1)D^2P_0, after dividing by P_0/F_0, are 55/3 and -11/3. Contracting the two Hessians therefore gives the exact two-by-two indicial system

    [ S(a+lambda)-1,       12/11          ] [A_0] =0,
    [ -T(a+lambda)-11, S(lambda-c)+11     ] [B_0]

Its determinant, multiplied by 3969, is

    16 lambda^4+480 lambda^3+(3600-112L)lambda^2
       -1680L lambda+196L^2-3528L
    =4[(2 lambda(lambda+15)-7L)^2-882L].       (13)

Thus lambda(lambda+15)=(7/2)(L +/- sqrt(18L)). In the first degrees:

    l=0: lambda=0,0,-15,-15;
    l=1: lambda=-1,-14,(-15+sqrt(505))/2,(-15-sqrt(505))/2;
    l=2: lambda=0,-15,6,-21.

The l=1 exponent -1 is translation of x. The l=2 exponent zero, with B_0/A_0=-11/3, is precisely a trace-free linear change of the x coordinates: differentiate F_0((I+epsilon S)x), P_0((I+epsilon S)x) with symmetric trace-free S. Such a change is an already available affine symmetry, not a new branch. For l>=3, L>18, so each of the two values of lambda(lambda+15) is positive; each quadratic has one positive and one negative root.

The finite indicial calculation does not solve (12) globally. It supplies neither an inverse on weighted spaces along the logarithmically corrected smooth core, nor matching between origin regularity and infinity decay, nor control of the nonlinear determinant and positive Hessian along a purported family. A non-affine global deformation would require those operations, after quotienting the affine modes. We have not supplied them. Positive or negative indicial exponents alone do not prove existence or nonexistence of such a deformation. No full deformation target was frozen, no weaker local/linear statement replaces one, and no method obstruction is nominated.

## 7. Primary comparison

[Trudinger--Wang, Inventiones 2000](https://maths-people.anu.edu.au/~wang/publications/1-Invent00.pdf), Section 7, equations (7.1)--(7.15), was read. Its affine coordinate change turns the singular example into a power profile. Equation (7.11) already has a double root in dimension ten. Its final measure estimate extends that singular solution weakly across the origin. It supplies neither the smooth radial existence proved by the stipulated source nor the missing global nonradial matching in Section 6. The original weak-extension argument is not being recast as a smooth perturbation theorem.

The companion source's 3<=n<=9 statement is a rigidity result, with completeness and positive Hessian; it does not provide a dimension-ten linear inverse. The r28 note already obtains affine completeness of the smooth source example from its exact warped metric and a divergent radial length integral. Combining that antecedent with (10) would describe the same existing example more precisely. No new compatibility operation or candidate is asserted on that basis.
