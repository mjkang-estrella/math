# Actual symmetric-cubic obstruction to operator-small reshuffling

This is a method obstruction, NOT a counterexample to the frozen global estimate.

Let n>=3, d=n−1, V={x∈R^n:sum_i x_i=0}, P its orthogonal projection, v_i=P e_i, and

T0=sum_(i=1)^n v_i^tensor3,
T=sqrt(n/(n−2)) T0.

For x,y∈V the associated product is mu(x,y)=sqrt(n/(n−2))P(x⊙y). The Gram matrix of the v_i is G_ij=delta_ij−1/n. Thus

B(T0)=sum_ij G_ij² v_i v_j*=((n−2)/n)I_V,
B(T)=I_V.

Indeed the entrywise square G∘G=(1−2/n)I_n+(1/n²)11*, and P kills the latter summand.

The associator is exactly

A(x,y,z)=(<y,z>x−<x,y>z)/(n−2).

To check this, expand P(x⊙y)=x⊙y−<x,y>1/n twice in (xy)z−x(yz); the coordinatewise triple products cancel. Summing in an orthonormal basis of V gives

||A||HS²=2d(d−1)/(n−2)²=2(n−1)/(n−2),
D=I_V/(n−2),
C=trD=(n−1)/(n−2).

The tensor trace vanishes: sum_j T(e_j,e_j,·)=sqrt(n/(n−2))sum_i ||v_i||² v_i=0. Hence J*I_V=0 and S(I_V)=0, whereas B=I implies K(I_V)=I_V. In particular

||S−K||_(HS→HS)>=1, although ||D||op=1/(n−2)→0.

This is an actual sequence in the required symmetric-cubic class, so one cannot use small D operator norm as a substitute for small two-index associator norm. It also explains the extra channel-fixed directions in channel-density.md: I_V is an exact fixed direction orthogonal to all original slices.

## Why this does not obstruct the full global bound

There is an orthonormal basis w_1,...,w_d of V satisfying

w_i=v_i−v_n/(sqrt n+1), i<=d.

Indeed all their inner products are delta_ij, using <v_i,v_j>=delta_ij−1/n. Let W be the isometry with columns w_i and V0 the matrix with columns v_i, i<=d. Then ||V0||op<=1 and ||V0−W||F<=1 (the difference has rank1). Telescoping the three mode actions on the diagonal cubic gives

||sum_(i<=d) v_i^tensor3−sum_(i<=d) w_i^tensor3||F<=3.

Each mode difference costs at most ||V0−W||F, because the diagonal cubic has Gram I and the other mode operators have norm<=1. Also ||v_n^tensor3||F<=1. Finally

||T−T0||F=(1−sqrt(1−2/n))sqrt(n−1)<=1.

The last inequality follows from 1−sqrt(1−2/n)<=2/n and 2sqrt(n−1)/n<=1. Therefore

dist(T,O_V)<=5,

dist(T,O_V)²<=25,

uniformly in n, while C tends to1. One extra latent orthogonal factor, rather than deletion of the full range of the matrix I_V, pays for this example. Extending that construction to all extra approximately fixed channel modes is the genuine remaining compatibility problem.

## The old normalized triple-trace iteration stalls here

For n>3, the triple-trace correction U has

U=((n−3)/(n−2))T.

Indeed L_x=sqrt(n/(n−2)) P diag(x) P on V. Expanding the three projections in Tr(L_xL_yL_z), all terms with two or three rank-one projections vanish because x,y,z have coordinate sum0; the three terms with one rank-one projection each contribute −sum_i x_i y_i z_i/n. Therefore Tr(L_xL_yL_z)=a³(1−3/n)sum_i x_i y_i z_i, with a²=n/(n−2), giving the stated ratio.

The natural scalar symmetric normalization of U back to B=I returns T itself. Thus the r67 triple-trace plus scalar normalization scheme has nonassociative fixed points with arbitrarily small Dirichlet operator norm. Its SMALL TOTAL error theorem is unaffected, since C→1 rather than0. Merely replacing total smallness by operator-density smallness cannot turn that iteration into a global proof. A trace-paid rank modification or some different operation is necessary.
