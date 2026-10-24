# Frozen r218 author target

Flat prescribed-class nonselection for uniformly tamed almost complex structures on the four-torus.

Let X=R^4/Z^4 have its fixed coordinates x1,x2,x3,x4, standard Euclidean metric g, standard orientation, and volume one. Put eij=dxi wedge dxj, U=e12+e34, V=e13-e24, W=e14+e23. All cohomology is real de Rham cohomology, identified on this fixed manifold without a moving diffeomorphism gauge.

Choose any smooth function p:S1->[0,infinity) with integral 1 and with a nonempty open zero set, and any smooth nonzero function f:S1 x S1->[0,1] such that p(x)f(x,z)=p(z)f(x,z)=0 for all x,z. Regard f as f(x1,x3) on X and put c=integral_X f dV>0. Such choices exist. Set s(0)=0 and s(t)=exp(-1/t^2)/4 for 0<t<=1, a_t=s(t)(f-s(t)c), r_t=sqrt(1+a_t^2), and F_t=(U+a_t V)/r_t. Let J_t be the orthogonal almost complex structure defined by g(J_t u,v)=F_t(u,v).

The assertions, for every such choice p,f, are:

1. J is smooth on [0,1] x X, gives the standard orientation, J_0 is the standard complex structure with fundamental form U, and every positive-order t derivative of J_t at zero vanishes. The fixed closed symplectic form U uniformly tames every J_t: U(v,J_t v)>=|v|_g^2/2 for all t,x,v.

2. The class [U] belongs to the J_t-compatible cone for every t in [0,1]. For t>0 this is realized by the smooth family
   A_t(x)=s(t)+(1-s(t))p(x), q_t=(A_t(x1)+A_t(x3))/2,
   eta_t=A_t(x1)e12+A_t(x3)e34+2s(t)^2(f-c q_t)e13.
   These eta_t extend smoothly to a closed, semipositive J_0-invariant form eta_0=p(x1)e12+p(x3)e34, which vanishes on the nonempty open set {f>0}; eta_0 is not asserted symplectic. The endpoint compatible fibre instead contains U.

3. For each t>0, EVERY smooth J_t-compatible symplectic form alpha with [alpha]=[U] has a unique self-dual decomposition alpha^+=q(U+a_t V), where q is a smooth positive function satisfying
   integral_X q dV=1,
   integral_X q f dV=s(t)c,
   |alpha|_g<=4q pointwise.
   Consequently for every delta>0,
   integral_{f>=delta} q dV<=s(t)c/delta.

4. For every sequence t_n>0 tending to zero and every choice alpha_n of smooth J_{t_n}-compatible symplectic forms in [U], the coefficient measures of alpha_n have a weak-* convergent subsequence. Every such limit is a closed J_0-invariant nonnegative measure-valued two-form, represents [U] as a distributional de Rham class, and is supported in {f=0}. In particular, no such sequence converges distributionally to ANY smooth J_0-compatible symplectic form. Thus for every epsilon in (0,1], there is no distributionally continuous choice t -> alpha_t on [0,epsilon] with alpha_t J_t-compatible symplectic and [alpha_t]=[U] at all t; in particular there is no C0-continuous or smooth such choice.

5. The anti-invariant cohomology spaces are H^-_{J_0}=span([V],[W]) and H^-_{J_t}=span([W]) for t>0. Thus h^- changes from 2 at zero to 1 at every positive parameter, while b+=3 and the fixed flat metric and all smooth norms of J_t remain bounded on the compact parameter interval.

6. Class freedom does permit an explicit smooth compatible family through U: zeta_t=U+2a_t e13 is J_t-compatible and symplectic for all t, including zero, and
   [zeta_t]=[U]+2s(t)c(1-s(t))[e13].
   The obstruction in (4) therefore concerns a specified class on a fixed manifold, despite common uniform taming and nonempty compatible fibres, and not free-class parameter-dependent existence.

This is the entire frozen target. No statement about integrability for t>0, prescribed volume, higher dimensions, other manifolds, arbitrary paths, or effective estimates beyond the displayed formulas is included. This is a research author target; correctness, contribution, acceptance and count are not assigned here.
