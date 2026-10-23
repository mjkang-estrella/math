# Prefreeze calculations I: finite jets and quantitative descent through the zero resolution

These are feasibility derivations for the unchanged scope in note00. No smaller statement is nominated or frozen.

## 1. Simultaneous finite determinacy really can be paid here

The source displays individual finite determinacy. Its preceding finite-flat Jacobian construction supplies enough extra structure to make that preliminary reduction simultaneous; this is a routine analytic reduction, not the proposed contribution.

Let A=O_(x,t)/J_x(F) on the finite representative of the spatial critical scheme. It is a locally free O_D-module of rank mu, and every fiber A_t is a LOCAL algebra of length mu, supported at x=0. Hence (m_x A_t)^mu=0. For each monomial x^nu of degree mu, its class is a holomorphic section of the vector bundle A and vanishes at every t. In a local free frame all its coefficient functions vanish; the class is therefore zero. Thus

    m_x^mu ⊂ J_x(F)

in the relative analytic ring after shrinking. This argument uses the reduced disk and actual freeness. Pointwise ideal membership in a nonflat quotient would not suffice.

Put b=j_x^(mu+1) F-F. Then b lies in m_x^(mu+2). Write b=a^T g with g=(F_xi) and all a_i in m_x^2. Also db/dx=Cg with every entry of C in m_x, since b_xi is in m_x^(mu+1). For F_s=F+s b,

    grad_x F_s=(I+sC)g,
    w_s=-(I+sC)^(-T)a,
    d_x F_s(w_s)=-b.

On a smaller common neighborhood, I+sC is invertible for all real 0<=s<=1 and all t in a fixed smaller closed disk. The vector field is holomorphic in x,t and has a uniform O(|x|^2) bound. Its flow exists for the whole unit interval on a common spatial neighborhood, fixes x=0, depends holomorphically on (x,t), and has the reverse flow as inverse. It gives (j_x^(mu+1)F)(h_t(x),t)=F(x,t).

Both (x,t)->(h_t(x),t) and its inverse have bounded derivatives on smaller compact neighborhoods; hence they are bi-Lipschitz there. This reduction preserves the existence of an exponent in note00. It does not make the parameter coefficients polynomial, assert a bound on base ramification, or prove the ambient Hölder step. It eliminates arbitrary spatial Taylor tails as an explanation of the remaining difficulty.

## 2. A proper analytic quotient transfers Lipschitz control upstairs to Hölder control downstairs

Here is the precise equal-fiber calculation. Let q:M->X be a proper real analytic map, with M a real analytic manifold and X contained in Euclidean space. Work over a compact subset K of X and a slightly larger compact neighborhood inside the representative; use finitely many analytic charts upstairs. Suppose h:M->R^k is smooth on the larger compact preimage and is constant on every fiber of q. Then h descends continuously to a map H on K, and H is Hölder there with some positive exponent.

In a pair of charts, let

    R={(p,p'): q(p)=q(p')},
    D(p,p')=|q(p)-q(p')|.

The relation is analytic, and the distance to it is subanalytic on compact chart blocks. The distance form of Bierstone–Milman Theorem6.4 gives

    dist((p,p'),R) <= A D(p,p')^a

for some a>0 (decrease a to <=1). Use a larger chart block for R and smaller ones for estimates, so boundary truncation does not discard the nearest equal-fiber pair. Compactness handles chart pairs away from R. A finite covering gives uniform constants and the minimum exponent. The zero locus consists of ALL equal fibers, not only the diagonal.

Since h is uniformly Lipschitz upstairs and h(p0)=h(p0') whenever (p0,p0') belongs to R,

    |h(p)-h(p')|
      <= L(|p-p0|+|p'-p0'|)
      <= A' |q(p)-q(p')|^a.

Take an infimum if the distance is not attained in the chosen chart. This proves the asserted two-point estimate without supposing h itself is subanalytic. The smooth partition of unity and its flow need only have bounded first derivatives on the compact resolution. The exponent belongs to the analytic quotient relation, not to a definability claim about ODE solutions.

This is the same equal-fiber device actually used in the proof of Bierstone–Milman Theorem6.10, applied to a fiber-constant Lipschitz function instead of curve length. It is a classical quantitative transfer, not new substantiality by itself.

## 3. Apply the pair calculation to the ACTUAL source resolution

In the non-log-canonical branch, take Source064 Proposition resolved-family after t=u^e. Let b:M->X' be that proper resolution and let Psi_u be the smooth complete transport on the resolved closed-ball tubes from Section13, preserving E and the sphere. On smaller compact tubes the map

    Psi: M_0 x D_u -> M, (p,u)->Psi_u(p)

and its inverse are smooth with bounded derivatives. This follows from smooth ODE dependence on the compact proper tube; arbitrary small representatives are chosen only once, before the estimate.

Define the analytic quotient

    q_0(p,u)=(b_0(p),u)

and smooth output h(p,u)=(b(Psi_u(p)),u). If q_0(p,u)=q_0(p',u'), then u=u'. Off E_0 the map b_0 is injective, so p=p'. On E_0 both output spatial points are zero because Psi_u preserves E. Therefore h is constant on EVERY q_0-fiber. The pair calculation gives a JOINT Hölder zero-family map

    Z(x,u)=(z_u(x),u),  x in X_0 cap B,

in the ordinary outer product metric. This is stronger than |z_u(x)|<=C|x|^a: it controls arbitrary close pairs and variation in u simultaneously.

For the inverse, use the analytic quotient q(p)=b(p), with the base coordinate retained, on the TOTAL resolved tube M. The smooth output

    p -> (b_0(Psi_(q_base(p))^(-1)(p)), q_base(p))

is constant on each q-fiber for the same reason. A second application gives a Hölder inverse. Taking the smaller of the two positive exponents and enlarging constants produces a common a in (0,1]. Boundary corners are handled by larger charts; the germ conclusion only uses interior compact neighborhoods.

Thus the actual proper zero resolution supplies intrinsic bi-Hölder triviality after the cover. No uniform exponent in mu or resolution graph is proved. No embedding of the resolution into a resolved ambient FUNCTION family is present. The calculation cannot simply be applied to the ambient extensions V_a: these fields do not come from a smooth flow on an analytic proper quotient covering the ambient tube.

## 4. The finite-cover seam has a calculable Hölder cost

This calculation applies to exact tube maps H_u whenever their total map AND inverse are jointly a-Hölder with common constants, H_0=id. For the zero-family construction just obtained, the exact domains are X_0 cap B and X_(u^e) cap B, so it applies there too.

First J_s=H_(zeta s)^(-1) H_s is jointly a^2-Hölder in (x,s), and its inverse has the same exponent. This follows by composing the TOTAL maps, retaining the parameter coordinates; replacing fiberwise estimates by this assertion without joint estimates would be invalid.

Write t=r^e exp(i theta), 0<=theta<=2pi, and

    u=r exp(i theta/e),  sigma=r theta/(2pi),
    phi_t=H_u J_sigma.

On angular regions of width at most pi, both t->u and t->sigma are 1/e-Hölder. Indeed, for t=R exp(i theta), t'=R' exp(i theta'),

    |R^(1/e)-R'^(1/e)| <= |R-R'|^(1/e),
    min(R,R')^(1/e)|theta-theta'|
       <= C |t-t'|^(1/e).

The latter follows from the chord estimate when |theta-theta'|<=pi and theta range bounded. The same calculation applies to sigma. Thus (x,t)->phi_t(x) is a^3/e-Hölder on such regions. The inverse is a three-fold composition in the opposite order and has the same conservative exponent.

At the cut, use the exact identities H_(zeta r)J_r=H_r and their inverses. For parameters whose shortest angular separation crosses the cut, insert cut points at a common intermediate radius (or the intersection of the short chord with the cut); their distance contributions are at most a fixed multiple of |t-t'|. The two sector estimates then glue, using A^gamma+B^gamma<=2^(1-gamma)(A+B)^gamma. At t=0, both u and sigma vanish and the same estimates apply, because all constituent maps at zero are the identity. There is no hidden angular Lipschitz claim at the origin.

Consequently the explicit source seam correction PRESERVES existence of a positive exponent. On the non-lc zero family, it gives a concrete exponent a^3/e. This routine exponent loss means that cyclic monodromy removal is not the remaining qualitative Hölder obstacle. It does not establish the ambient tube's initial a-Hölder estimate.
