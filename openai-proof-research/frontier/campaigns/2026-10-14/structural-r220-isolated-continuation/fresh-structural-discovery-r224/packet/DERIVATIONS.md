# Source348: integrated reduction and the relative sectional-cone problem

Research r224. PREFREEZE calculations, not a frozen author-proof nominee. All pinned Source348 operations are stipulated true. The three source conclusions, their analytic and algebraic proofs, and the overlapping original I30 metric-stability construction are not proposed as discoveries here. No correctness or contribution grade is assigned.

## 1. Category, energy and normalization

Throughout the prospective family problem, M is a closed connected smooth simply connected four-manifold, metrics are smooth, and sectional curvature means sectional curvature of every real two-plane. Write

E_g = Ric_g - (R_g/4)g,    D(g) = integral_M |E_g|_g^2 dmu_g.

The norm is the full covariant two-tensor norm, not a curvature-operator norm; D is the integral, not its square root. For a positive constant c, the connection and covariant Ricci tensor of cg equal those of g, R_cg=c^{-1}R_g, E_cg=E_g, |E_cg|_cg^2=c^{-2}|E_g|_g^2, and dmu_cg=c^2 dmu_g. Thus D(cg)=D(g). Lengths and sectional curvature scale by sqrt(c) and c^{-1}. Pullback by a diffeomorphism also preserves D and sectional nonnegativity.

For positive average scalar curvature put

N(g) = (Rbar(g)/12) g,    Rbar(g) = Vol(g)^{-1} integral R_g dmu_g.

Then Rbar(N(g))=12. For nonnegative sectional curvature and simply connected closed M, Rbar cannot vanish: otherwise every sectional curvature vanishes everywhere, giving a complete flat simply connected closed manifold, impossible. This argument does not extend to arbitrary nonsimply-connected M; flat tori are excluded by the stated category.

The three normalized Einstein models have Ric=3g. Their volumes are 8pi^2/3 (S4), 2pi^2 (CP2), and 16pi^2/9 (S2 x S2 with both curvatures 3). A metric on one of these smooth manifolds need not be isometric or close to a model merely by knowing the manifold's name. No covering or quotient extension is made in this note.

## 2. Strongest integrated source operation, including time zero

The boundary and positive companions jointly supply exact classification of the limiting nonnegatively curved positive Einstein metric. Their role is stronger than a list of model names: the Bianchi/Weyl gradient equation, weak norm equation across block zeros, moment/volume obstruction, full weighted Hessian decomposition, coupling certificates and equality mechanism keep the product boundary in the classification. In particular, a strictly positive margin for the highest Hessian-type operator cannot be assumed at the equal product. Its nonnegative bound degenerates there.

The L2 companion gives constants independent of an initial curvature maximum after Rbar=12 normalization. With eta=sqrt(D), almost-Schur gives ||R-12||_2 <= 4 eta in the paper (the primary almost-Schur proof gives the sharper sqrt(12) eta). Since the scalar and trace-free terms are orthogonal,

||Ric-3g||_2^2 = D + (1/4)||R-12||_2^2 <= 5D

using the source constant. This is an L2 estimate, not a pointwise Ricci bound. The source obtains volume, diameter, Sobolev and entropy control, then a moving high-curvature-tail estimate and a first-crossing argument. One obtains a common T>0 and |Rm(g(t))|<=A/t for 0<t<=T. The moving Einstein defect

L(t)=Ric(g(t)) - [3/(1-6t)]g(t)

has ||L(t)||_2<=C eta. The negative sectional defect has integral at most Ct. At positive time, smooth compactness and the limit equation yield an Einstein limit (1-6t)h. Rescaling the negative-sectional integral and then taking t down to zero gives sec(h)>=0. This last limit operation does not assert sec(g(t))>=0 for each approximating flow.

There is already eligible original history supplying the missing time-zero metric bridge; ignoring it would incorrectly nominate a paid construction. In I30 the fixed-rescaled flow k=(1-6tau)^{-1}g(tau), tau=T/2, satisfies:

* ||L(t)||_infinity <= C eta/t by parabolic smoothing;
* d_k >= d_g - a, a=C eta(1+|log eta|), using early distance shrinking to s=eta^2 and then integrating the defect;
* for every measurable fixed U, |sqrt(mu_k(U))-sqrt(mu_g(U))| <= C eta.

The measure estimate is stronger for small sets than a uniform total-variation bound. From the one-sided distance inequality, B_k(z,r) is contained in B_g(z,r+a). A ball missing from a comparison ball has measure bounded by

C(r^6 + a r^3 + eta r^2 + eta^2),

using small-ball expansion for k, Bishop comparison for g, and the square-root measure estimate. Noncollapse makes its radius at most

R=2a+C(r^6+a r^3+eta r^2+eta^2)^(1/4).

At r=eta^(1/4), R=O(eta^(3/8)); chaining gives all-pair distortion O(eta^(1/8)). Fixed-time elliptic model repair is then applied. I30's unchanged target is a D^(1/16) GH estimate. These operations have been read, not adopted as a new grade and not reopened here. Failure of a direct two-sided distance integration is therefore not an unpaid gap.

For family work, the compatible consequence needed is qualitative: as D tends to zero, the fixed-time normalized metric enters any prescribed smooth neighborhood, modulo diffeomorphisms, of the three normalized Einstein orbits. This is already in the source compactness argument. No extra initial curvature or injectivity hypothesis is added to obtain this entrance statement.

## 3. Ordinary metric families: a compatible slice construction

Let h be one normalized model and K=Isom(h). The ordinary slice description of a neighborhood of its diffeomorphism orbit is an associated bundle

Diff(M) x_K S_h,

where S_h has a K-equivariant chart exp_h(v), v in a sufficiently small star-shaped neighborhood in the normal space ker(div_h). A K-invariant choice can be made by averaging norms over compact K and shrinking the neighborhood. The important point is that a family need not admit a single globally chosen diffeomorphism to h. If v is replaced by k.v and phi by phi k^{-1}, the expression below is unchanged:

[phi,exp_h(v)] -> [phi,exp_h((1-s)v)],  0<=s<=1.       (3.1)

This is a well-defined deformation to the orbit, and fixes every point of the orbit. It acts on arbitrary compact parameter families and relative subfamilies already in the orbit. Thus monodromy of local gauge choices alone is not the obstruction. The actual associated-bundle gluing proof and metric slice proof were read in Corro--Kordass, with the original Ebin endpoint unavailable; this is a classical comparison operation, not a claim of new slice theory. Functional-analytic intermediates cited by that exposition remain unread and are listed separately.

For normalized metrics compose (3.1) with N; average scalar stays positive in a small neighborhood. Normalization fixes the orbit. Continuity of curvature and volume in a C2 neighborhood implies that D along this slice contraction tends uniformly to zero as the slice radius tends to zero. This statement gives a modulus of smallness, not a proved linear energy bound for arbitrary metrics.

Combine fixed-time source smoothing with this contraction. On a compact smooth parameter family, ordinary Ricci-flow dependence gives a continuous path to the fixed-time slice; scalar evolution dR/dt=Delta R+2|Ric|^2 and the scalar maximum principle keep its average positive, so N is defined; an initial normalized Einstein metric evolves as (1-6t)h and remains h after N. The energy of the first path is <=C D initially, since the trace-free part of L is E and D is scale invariant. The slice part stays in an arbitrarily small ordinary-metric neighborhood if D was chosen sufficiently small. This is the strongest compatible unconstrained-metric construction. The general parabolic dependence theorem is classical but its original proof was not independently acquired here; this discussion is a reduction, not an independently submitted theorem relying on an unread endpoint.

Two distinct curvature questions remain if one asks for the same deformation inside sec>=0. First, the source smoothing path controls an integral negative part, not membership in the sectional cone. Second, even a metric slice very near the product has boundary planes of curvature zero, so ordinary radial contraction has no automatic cone-preservation property. For the round and Fubini--Study models strict sectional positivity makes sufficiently small C2 neighborhoods harmless; this removes the second question there, but it does not repair the initial smoothing path for all nonnegative input metrics. On the product both questions persist.

## 4. Exact product energy and honest nonempty parameters

Let g=q1+q2 on S2 x S2, where Ki and Vi are the Gaussian curvature and area of the factors. Ric has eigenvalues K1,K1,K2,K2, so R=2(K1+K2), E has two eigenvalues (K1-K2)/2 and two opposite eigenvalues, and

|E|^2=(K1-K2)^2.

Gauss--Bonnet on the two oriented spheres gives integral Ki=4pi. Consequently

D(q1+q2)=V2 integral K1^2 + V1 integral K2^2 -32pi^2
 =V2 integral (K1-4pi/V1)^2 + V1 integral (K2-4pi/V2)^2
   +16pi^2(V2/V1+V1/V2-2).                         (4.1)

All integrals on the right are on the indicated factor with its own measure. This proves simultaneously that D=0 precisely when both curvatures are constant and equal. It also separates area imbalance from the two curvature variances. Mean scalar is

Rbar=8pi(1/V1+1/V2).

For round factors with curvatures 3(1+u) and 3(1-u), |u|<1, mean scalar is exactly 12 and

D=64pi^2 u^2/(1-u^2).                              (4.2)

Thus the parameter u is genuinely free near zero under all joint hypotheses. This is the original-history unstable product example, not a fresh result.

There is much more freedom than (4.2). Fix the round sphere h of curvature 3 and take qi=e^{2fi}h. Then

Ki=e^{-2fi}(3-Delta_h fi),                         (4.3)

where Delta=div grad has nonpositive eigenvalues. Arbitrary sufficiently C2-small smooth fi give Ki>0. Product sectional curvature is nonnegative, with mixed planes zero. Formula (4.1) and smooth dependence give D=O(||f1||_C2^2+||f2||_C2^2), and N preserves D. Choosing a nonconstant spherical harmonic of degree 2 yields actual non-Einstein examples; the curvature linearization is -(Delta+6)f=12f for this harmonic, hence the first variation of curvature is nonconstant. The free functions are therefore real, not forbidden by the Einstein endpoint or normalization.

The explicit path qi(s)=e^{2(1-s)fi}h has positive factor curvature whenever qi(0) does: its curvature numerator is

3-(1-s)Delta fi = s*3 + (1-s)(3-Delta fi)>0.

Taking products and normalizing gives an explicit cone-preserving contraction for this parametrized subclass. This does not by itself give a relative contraction fixing every Einstein metric, as shown next.

## 5. Gauge repair in the product subclass, and what it actually resolves

The naive conformal path fails the relative requirement even at zero input energy. In stereographic coordinates on a round sphere, the dilation z -> a z, a>0, has conformal factor

e^{2f_a(z)} = a^2(1+|z|^2)^2/(1+a^2|z|^2)^2.

For a!=1 the factor is nonconstant, but e^{2f_a}h is a pullback of h and has constant curvature 3. Hence (e^{2f_a}h)+h is itself an Einstein product and D=0. Equation (4.3) gives Delta f_a=3(1-e^{2f_a}). At an intermediate exponent theta in (0,1),

K(e^{2theta f_a}h)=3 e^{-2theta f_a}(1-theta+theta e^{2f_a}).       (5.1)

As a function of z0=e^{2f_a}>0, the factor is (1-theta)z0^{-theta}+theta z0^{1-theta}. Its derivative is theta(1-theta)z0^{-theta-1}(z0-1), so it is not constant on any nontrivial interval. Since f_a is nonconstant, (5.1) is nonconstant. Formula (4.1) then gives strictly positive product energy at that intermediate metric. This disproves a relative fixing property and an estimate D(path)<=C D(input) for this particular ungauged interpolation, not for all possible deformations.

A compatible stronger alternative fixes this defect locally on the explicit product subclass. For an area-normalized conformal factor q=e^{2f}h with area V0=4pi/3, remove its degree-one spherical harmonics by a small conformal diffeomorphism. The three nonrotational Möbius parameters have, at the identity, conformal-factor derivatives spanning the three degree-one harmonics: the field grad_h(x_j) satisfies Lie_grad(x_j) h=2 Hess_h(x_j)=-6x_j h, so the derivative of f is -3x_j. Their moment Jacobian is -3 times the positive definite matrix (integral x_i x_j). The finite-dimensional implicit function theorem therefore imposes

integral f x_j dmu_h=0, j=1,2,3,

uniquely in a local choice of these three parameters. Rotations preserve this condition and h. The area condition integral e^{2f}=V0 implies |integral f|<=C||f||_2^2 for small f. On the orthogonal complement of constants and degree-one modes, -(Delta+6) has eigenvalues at least 12, since -Delta has eigenvalues 3l(l+1). Elementary spectral expansion thus gives

||f||_H2 <= C(||(Delta+6)f||_2 + |integral f|)

when the degree-one components vanish. From (4.3),

K_q-3 = -(Delta+6)f + Q(f),

where, for ||f||_C2<=rho, ||Q(f)||_2<=C rho ||f||_H2. This follows by expanding e^{-2f}=1-2f+O(f^2): the remainder is a sum bounded by C(|f|^2+|f||Delta f|). The area term also absorbs for rho small. Equivalence of h and q measures then gives

||f||_H2 <= C ||K_q-3||_{L2(q)}.                  (5.2)

For the area-renormalized path

q_theta = [V0/integral e^{2theta f}dmu_h] e^{2theta f}h,  0<=theta<=1,

factor curvature stays positive; area remains V0. The same formula and the bound on the scalar area multiplier give ||K_qtheta-3||_2<=C||f||_H2. With two such factors, (4.1) and (5.2) imply D(q1,theta+q2,theta)<=C D(q1+q2). Mean scalar is 12 throughout. If initial D=0, (5.2) forces the balanced factors f1=f2=0, so the gauged contraction fixes that metric after undoing the selected conformal coordinate changes.

Area imbalance is also concretely removable in this local product category. Write q_i=a_i q_i^0, where q_i^0 has area V0, and assume the product is mean-scalar normalized. Then 1/a1+1/a2=2, so a1=1/(1+u), a2=1/(1-u). With Vi^0=V0, (4.1) reads

D= (a2/a1)V0 ||K1^0-3||_2^2 +(a1/a2)V0 ||K2^0-3||_2^2
   +64pi^2 u^2/(1-u^2).

For |u|<=1/2, contract u to (1-s)u, keeping the q_i^0 fixed. The factors remain positively curved, mean scalar stays 12, the imbalance term decreases, and each variance weight remains between 1/3 and 3. Thus this first path has energy at most 9D(input). It fixes any Einstein input since then u=0. Follow it by the balanced conformal-factor paths just constructed. This gives the claimed small-energy and relative repair throughout the explicitly presented local product subclass.

This executes the natural repair rather than stopping at the counterexample (5.1). It is a local construction for explicitly presented conformal product metrics. A general nearby metric need not carry this product presentation. No claim that a finite-dimensional Möbius gauge solves the full sectional-cone problem is made. The calculation is elementary elliptic/slice composition and is not offered as a substantial nominee.

## 6. Two tempting freedoms which do not exist

For a warped product g=q_B+f^2 q_F with positive f on a closed base B, a mixed plane spanned by a unit base vector X and a unit fiber vector has

sec_g(X,U)=-Hess_B f(X,X)/f.

Thus sectional nonnegativity implies Hess f<=0. Its trace has integral zero, so Delta f=0 and f is constant on each connected closed base. Warping cannot supply an arbitrary small function while retaining the joint hypotheses.

There is a stronger obstruction to a global conformal repair of the equal product h=h1+h2. The conformal curvature formula for h-orthonormal X,U, with X in the first factor and U in the second, is

e^{2f} sec_{e^{2f}h}(X wedge U)
 = -Hess f(X,X)-Hess f(U,U)+(Xf)^2+(Uf)^2-|df|^2.       (6.1)

For completeness, (6.1) follows by inserting the connection difference

nabla^f_X Y-nabla_X Y = df(X)Y+df(Y)X-h(X,Y)grad f

into the curvature definition and evaluating the mixed plane, whose background curvature is zero. Take an orthonormal frame e1,e2 in the first factor and e3,e4 in the second, and sum (6.1) over the four mixed pairs. The sum is

-2 Delta f -2|df|^2.

If all mixed curvatures are nonnegative, Delta f+|df|^2<=0. Equivalently Delta(e^f)<=0. On the closed connected product the maximum principle, or integration followed by the strong maximum principle, forces e^f constant. Therefore no nonconstant global conformal change of this product remains sectionally nonnegative. Separate factor conformal changes in Section 4 are different tensors and do not contradict this statement.

## 7. First- and second-order geometry of the sectional boundary

Set h=h1+h2 with both factors round of curvature 3, and let P,Q be its parallel rank-two tangent distributions. Consider a C2 one-sided path g(t)=h+t k+(t^2/2)l+o(t^2) in metrics, with sec(g(t))>=0 for t>=0. Smoothness here includes the spatial derivatives needed to differentiate curvature. At a point choose product normal coordinates, lower-case Latin indices a,b in P and Greek indices mu,nu in Q. For an h-unit mixed pair, the curvature numerator has first variation

A_{a mu}(k)=nabla_a nabla_mu k_{a mu}
 - (1/2)nabla_a nabla_a k_{mu mu}
 - (1/2)nabla_mu nabla_mu k_{aa}.                   (7.1)

The two mixed covariant derivatives commute because the background mixed curvature vanishes. In product normal coordinates all possible background mixed curvature terms in the first variation vanish. The denominator of sectional curvature is 1 at t=0; its derivative multiplies the zero background numerator and contributes nothing to (7.1).

Sum (7.1) over a=1,2 and mu=3,4. Parallelness of P and Q identifies this sum with

A(k)=div_P div_Q(k_PQ) -(1/2)Delta_P tr_Q k -(1/2)Delta_Q tr_P k.

Every term integrates to zero against dmu_h, by integration by parts on the closed product. On the other hand, sec(g(t))>=0 and sec(h)=0 on a mixed plane imply A_{a mu}(k)>=0. Therefore A(k)>=0 with zero integral. Continuity forces A(k)=0 pointwise, and each nonnegative summand vanishes. Choosing frames containing any given unit X in P and U in Q yields

A_{XU}(k)=0 for EVERY mixed plane.                 (7.2)

Thus every admissible first variation is tangent to all zero-plane equations. A strictly positive first-order repair of these planes cannot be achieved by any global metric variation. This is an integrated compatibility identity, not a statement that every such k integrates to a nonnegative-curvature path.

The next constraint is explicit. Put

C_{ij p}(k)=(1/2)(nabla_i k_{jp}+nabla_j k_{ip}-nabla_p k_{ij}).

The coordinate curvature formula at a product-normal point gives

R_g(a,mu,mu,a)
 = t A_{a mu}(k)
   +t^2[(1/2)A_{a mu}(l)+Q_{a mu}(k)] +o(t^2),

Q_{a mu}(k)=sum_p [C_{a mu p}(k)^2-C_{aa p}(k)C_{mu mu p}(k)].    (7.3)

Here R(X,Y,Y,X) uses the convention positive on a round sphere. One can check the sign directly on a warped product: the mixed numerator contains +Gamma_{a mu}^2-Gamma_{aa}Gamma_{mu mu} in addition to the negative second-derivative terms, and reduces to -f Hess f. For a straight metric segment h+t k the second-derivative part is exactly linear, and the quadratic term is the same expression contracted with g(t)^{-1}; thus (7.3) is not a guessed error estimate.

In view of (7.2), necessary second-order inequalities are

(1/2)A_{a mu}(l)+Q_{a mu}(k)>=0 for every mixed plane,

and hence, after tracing and integration,

integral sum_{a,mu} Q_{a mu}(k) dmu_h >=0.          (7.4)

The acceleration l cannot change this integrated second-order obstruction, since integral A(l)=0. Even the individual fixed-plane inequalities omit moving planes. There is a stronger explicit second-order condition. Let X,Y be an orthonormal frame of P, U,V one of Q, and xi=X wedge U. Define the symmetric curvature bilinear form Rcal_t on bivectors using the covariant curvature of g(t) and the fixed h identification, so its value on a simple bivector is the sectional numerator. Write Rcal_1 for its first derivative. Put

p=Rcal_1(xi,V wedge U),    q=Rcal_1(xi,X wedge Y).

Consider the moving plane spanned by X+t(aY+bV) and U+t(cY+dV). Its first bivector derivative is

zeta=a Y wedge U+b V wedge U+c X wedge Y+d X wedge V.

Since (7.2) holds on every mixed plane, differentiating that identity with respect to the mixed-plane parameters shows Rcal_1(xi,Y wedge U)=Rcal_1(xi,X wedge V)=0. The background curvature is 3 on each pure-factor bivector and zero on the mixed subspace. The moving plane's numerator therefore has t^2 coefficient

B+2bp+2cq+3(b^2+c^2),    B=(1/2)A_XU(l)+Q_XU(k).

Terms involving the second bivector derivative pair trivially with xi in the background curvature. The changing denominator is positive and cannot change the leading sign. Nonnegativity for every b,c implies, by the exact square completion

3(b+p/3)^2+3(c+q/3)^2+B-(p^2+q^2)/3 >=0,

that

(1/2)A_XU(l)+Q_XU(k) >= (p^2+q^2)/3.             (7.5)

In invariant notation, let Bmix be the block of Rcal_1 from P wedge Q to (Lambda^2 P) direct-sum (Lambda^2 Q), with h-orthonormal bivectors. Sum (7.5) over an orthonormal mixed basis and integrate; the acceleration again disappears and gives the stronger necessary condition

integral sum_{a,mu} Q_{a mu}(k) dmu_h
 >= (1/3) integral ||Bmix||_HS^2 dmu_h.            (7.6)

This explicitly accounts for the first motion of the null-plane set. The coefficient 1/3 comes from the normalized factor curvature, not from a curvature-operator positivity assumption. The sectional cone is tested only on decomposable bivectors. Neither (7.2), (7.5) nor (7.6) gives an equivariant selection of l, controls the remaining plane directions and higher orders, or proves integrability of an arbitrary tangent tensor. These are necessary compatibility calculations, not an existence theorem.

## 8. A classical nonproduct family genuinely inside the small-energy region

It would be wrong to infer from the preceding restrictions that all nearby nonnegatively curved metrics are products. The compatible Cheeger construction gives explicit counterexamples to that reduction.

Identify the two spheres as unit vectors x,y in R3 and put h=(1/3)(g_unit+g_unit). Let G=SO(3) act diagonally. Identify its Lie algebra with R3, bracket the cross product, and Q the Euclidean inner product. At p=(x,y) define

A_p z=(z cross x,z cross y),
A_p^*(u,v)=(1/3)(x cross u+y cross v),
C_t=(I+t A_p A_p^*)^{-1},   h_t(V,W)=h(C_t V,W).    (8.1)

Formula (8.1) is smooth on all of M including the singular orbits x=+/-y, since it involves an everywhere positive invertible endomorphism, not division by an orbit tensor at a singular orbit. It extends smoothly to t=0 with h_0=h. For t>0 it is the quotient metric of

(M x G,h+t^{-1}Q) -> M,   (p,a) -> a^{-1}p.

Indeed the horizontal lift of C_t^{-1}V is (V,-t A_p^* V): it is orthogonal to every vertical (A_p Z,Z), and its projection is V+t A_p A_p^* V. O'Neill's formula gives sectional nonnegativity. More specifically its curvature numerator on the transformed plane is

N_t(C_t^{-1}V,C_t^{-1}W)
 =N_0(V,W)+(t^3/4)|[A_p^*V,A_p^*W]|_Q^2 + nonnegative O'Neill term.    (8.2)

These are classical Cheeger/Müter operations. The actual horizontal-lift proof and curvature formula, zero-plane corollary, and explicit diagonal SO(3) example were read in the Ziller/He exposition; Cheeger's original PDF access failed and Müter's thesis was not read. No new attribution for (8.1)--(8.2) is claimed.

At a point with x not parallel to y, the h-zero planes are exactly span{(u,0),(0,v)} with nonzero u perpendicular to x and v perpendicular to y. To verify this, decompose the simple bivector into its two pure-factor and mixed components; the product curvature numerator is 3 times the sum of the squares of the pure-factor components. Vanishing means both projections of the plane have rank at most one, so the plane is this mixed span.

For such a plane, the bracket in (8.2) vanishes precisely when x cross u and y cross v are parallel. They must then both lie on the line R(x cross y). Thus u and v each have a unique projective direction. Conversely, the one-form dual to a diagonal Killing field is the sum of forms pulled back from each factor, so its exterior derivative vanishes on a mixed pair. The O'Neill expression in the read curvature formula is therefore zero when the bracket is zero. Exactly one zero-curvature plane survives at each generic point, after the C_t^{-1} transform. At x=+/-y a circle of such planes survives, in agreement with the actual primary example.

A product of two positively curved surfaces has a two-dimensional family RP1 x RP1 of zero planes at every point. The generic single zero plane of h_t therefore proves h_t is not locally isometric to such a product for t>0. In particular it is not isometric to the equal round product. Since h_t -> h smoothly and E_h=0,

D(h_t)<=C t^2 for 0<=t<=t0.

For all sufficiently small positive t, Ric(h_t)>0. If D(h_t)=0, then Ric=(R/4)h_t; contracted Bianchi gives dR/2=dR/4, hence R is constant. Thus h_t would be positive Einstein with sec>=0. The paid classification and Euler characteristic 4 of S2 x S2 (as opposed to 2 for S4 and 3 for CP2) force the equal round product up to scale, contradicting the zero-plane set. Thus 0<D(h_t)<=C t^2. Applying N changes neither this conclusion nor sectional signs. This verifies actual nonproduct examples under every proposed small-energy, normalization, topology and curvature hypothesis. It does not merely count a formal deformation parameter.

On this explicit one-parameter family the reverse path h_t -> h_{(1-s)t}, followed by N, is already a cone-preserving relative contraction. Conjugating the specified action by diffeomorphisms gives compatible pullback examples. The missing operation is not contraction of this known family. An arbitrary nearby metric need not admit any isometric SO(3) action, so this construction supplies no map on the full metric neighborhood. Nor is it legitimate to choose a new action continuously on every metric from its topology alone.

## 9. What is and is not left open by these calculations

The investigated full-scope direction was a relative family mechanism in the space

C_delta(M)={g smooth : sec_g>=0, Rbar(g)=12, D(g)<delta},

relative to its normalized Einstein subspace E(M). A meaningful strong form would take every compact parameter pair (P,A) and every continuous smooth-metric family P -> C_delta(M) with A mapped into E(M), and deform it, fixing A, to E(M), through nonnegatively curved normalized metrics with a uniform small-energy bound tending to zero with delta. An equivariant neighborhood deformation would imply this form. No such statement was frozen as a viable theorem and no proof of it is submitted.

The full remaining work after the strongest compatible reductions is specific:

1. Replace or repair the initial source smoothing path by a continuous relative family path which stays in sec>=0, with uniform small-energy control and no newly imposed initial curvature bounds. The source's integral negative-part estimate is insufficient for this replacement.
2. At the product endpoint, construct a diffeomorphism-equivariant contraction of the actual sectionally nonnegative slice, including nongroup-invariant, nonproduct perturbations, preserving all zero-plane compatibility equations and controlling energy. Equations (7.1)--(7.6), including moving-plane square completion, give necessary constraints, not a solution. Global conformal correction is unavailable by (6.1); product conformal gauges and Cheeger reversal solve their own subclasses only.
3. Glue such a cone-preserving local operation over compact parameter families relative to the full Einstein orbit. Ordinary slice theory already handles the associated-bundle gluing once an equivariant cone-preserving fiber operation exists; it should not be named as an additional unexplained obstruction.

One could weaken the problem to paths through unrestricted metrics, or add a product presentation or a prescribed SO(3) action. The actual constructions above explain why those reduced variants are compatible and largely classical. They are not offered as replacement nominees for a full-scope result. No claim is made that the three obligations are impossible, novel in the literature, or exhaustive across all possible Source348 directions.

The round/CP2/product classification, original-metric GH power estimate, formula (4.1), local Möbius gauge repair, conformal and warped restrictions, mixed-plane variations, and Cheeger example do not amount here to a distinct substantial completed theorem. The correct discovery handoff is PREFREEZE/no nominee, with these durable integrated derivations and the exact missing cone-preserving operation preserved.
