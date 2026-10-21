# T360S147 — global bi-Sobolev transport through conjugate contacts

Author proof at the unchanged statement in STATEMENT.md. This is discovery-stage mathematics relative to stipulated Source360, not an independent correctness/contribution verdict. No downstream manuscript, formalization or release stage is opened.

## 1. Exact dependencies and conventions

The manifold, cost and weak-MTW convention are exactly those of STATEMENT.md. Fix an admissible density pair; constants in local regularity may depend on its bounds. Write the negative-cost dual potentials as

    u(x)+c(x,y)+v(y)>=0,

with equality on the optimal correspondence. The following pinned inputs are used as true, including their operative proof operations:

* Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW, `geo:prelim`, `geo:support`, `geo:sections`, `geo:intermediate`: compact minimizing-log graph, uniformly semiconvex and Lipschitz potentials; ordinary subgradients all give global contacts; convex lifted sections with the stated diameter inequality; full intermediate graph homeomorphism; C1,1 regularization and uniformly Lipschitz inverse pole/momentum maps at fixed interior time.
* Uniform-Bi-Holder-Transport-from-Weak-MTW, `thm:main`, `sc:power` and conclusion: every pole has exactly one contact endpoint, the reverse correspondence has the same property, and the two maps are continuous inverses. The stronger all-points contact conclusion is in the operative proof, not inferred only from an almost-everywhere representative.
* The second source's `spec:Jacobi-factorization` identifies the broken-action Hessian with the full Jacobi matrix up to invertible short-piece factors, including at conjugacy. We also give the equivalent Jacobi-field argument below.

The external local regularity input is De Philippis–Figalli, arXiv:1211.2341v1, Theorem `w21eps` (Theorem1.1): a strictly c-convex Alexandrov solution with bounded positive generalized Monge–Ampère density, smooth twisted nondegenerate cost and their orthogonal-pair condition(C1), is locally W^{2,1+kappa} for some kappa>0. Its cost norm(C0) contains C3/mixed fourth derivatives and the logarithm of the mixed determinant. We use it only on relatively compact smooth, nondegenerate cost patches. We do not claim uniformity as those patches approach cut. The full proof was read; its section/engulfing antecedents are credited, with bounded transitive reads recorded separately.

Classical operations used below are the injective Lipschitz area formula, distributional Piola identity, Sobolev chain rule with smooth functions, finite-dimensional adjugate algebra, and smooth isometric embedding. The argument for the composite derivative is included to avoid assuming Sobolev regularity of an inverse in advance. None of these classical operations is claimed as a new theorem.

## 2. There is a unique log at every contact

Let T be the source's contact homeomorphism. At fixed x, every p in the zero-height lifted section S_x(0) has endpoint T(x). This section is nonempty: all minimizing logs of T(x) lie in it. Its endpoint v-oscillation is zero. The exact source inequality gives

    diam S_x(0)^2 <= 8[0+osc_(p in S_x(0)) v(exp_x p)] = 0.

Consequently there is a single minimizing log p(x) to T(x). By `geo:prelim` and `geo:support`, the ordinary subdifferential of u is exactly {p(x)}. A semiconvex function with singleton ordinary subdifferential is differentiable; hence p=grad u everywhere. The compact, closed subgradient graph then shows p is continuous: any convergent subsequence of p(x_j) with x_j->x must limit to the unique subgradient at x. Thus u is C1. The same reasoning gives v in C1 and the unique reverse log.

This eliminates ordinary multiple-geodesic cut contacts. It does not eliminate unique conjugate contacts. Set

    E={x: (d exp_x)_(p(x)) is singular},    O=M\E.

The set E is closed by continuity of p and of the exponential differential. At x in O, the minimizing log is unique and nonconjugate, so it lies strictly before cut (`lem:interior-characterization` in the first source). Therefore c is smooth on a product neighborhood of (x,T(x)).

## 3. Local Sobolev regularity on O uses the full compatible primary theorem

Fix x0 in O and y0=T(x0). Choose relatively compact coordinate balls U,V around x0,y0 with c smooth and det D_xy c nonzero on their closures. After shrinking, both twist maps are diffeomorphisms onto their ranges. Weak MTW becomes precisely DPF(C1) in these coordinates; its orthogonality pairs the tangent and cotangent variations, so it is invariant under the coordinate changes used in the primary proof.

Continuity of T permits a smaller U on which every global contact endpoint is in V. Represent u there using the unchanged dual datum restricted to a compact subneighborhood of V containing those endpoints. The supremum equals u because each point retains its actual global contact. Contacts of this restricted representation are global contacts: the representing numbers are still -v(y). Reverse uniqueness implies strict c-convexity, including singleton contact with y0.

The continuous nonnegative function

    x -> u(x)+c(x,y0)+v(y0)

vanishes exactly at x0 on compact M. Its sufficiently small positive sublevel is relatively compact in U; its contact image is relatively compact in V. This supplies the local section boundary condition in DPF without imposing global coordinate-domain convexity. The same localization is explicitly permitted in DPF's setup and FKM's local section discussion.

For every Borel A in this section, homeomorphic transport and the density bounds give

    (lambda/Lambda) vol_g(A) <= vol_g(T(A))
                              <= (Lambda/lambda) vol_g(A).

Coordinate volume densities are smooth positive and bounded above/below on the selected patches. Thus the c-contact measure has bounded positive density with respect to coordinate Lebesgue measure. Equivalently, on the differentiability set the generalized Monge–Ampère right side includes the smooth nonzero factor |det D_xy c| and rho_0/rho_1(T); those factors are bounded above/below on this patch. This is the bounded Alexandrov-data hypothesis in DPF, not merely an almost-everywhere determinant equation asserted as a substitute for the measure hypothesis.

DPF consequently gives u locally W^{2,1+kappa} on this section. Here kappa and constants may depend on the patch. Since T is a smooth function of (x,du(x)) in these cost coordinates, the Sobolev chain rule gives T locally W^{1,1+kappa}. Hence T is W^{1,1}_loc(O). The identical argument applies to the reversed map off its conjugate-contact set.

Local W^{1,1} on O alone does not prove the claimed global result. A null exceptional set can carry singular derivative measure. We next identify and remove that measure, rather than take an unjustified limit of local estimates.

## 4. A global Lipschitz parametrization of the endpoint graph

Fix t=1/2 and w=Q_tu. Source `geo:intermediate` gives w in C1,1 with a geometry-only bound. Let

    X(z)=exp_z(-t grad w(z)),
    Y(z)=exp_z((1-t) grad w(z)).

These are the initial and final endpoints of the supporting geodesic through z. Equivalently, (X(z),p(X(z))) is the source inverse of the full intermediate graph projection. Since the subgradient graph is now the graph of the continuous p, X is a homeomorphism. Also Y=T o X and is a homeomorphism.

Both X and Y are Lipschitz with a common bound L_g>=1 depending only on (M,g). Indeed |grad w|<=diam M, the source bounds Hess w at t=1/2 solely by geometry, and geodesic flow has bounded derivatives on the resulting compact velocity/time set. This does not bound the Lipschitz norm of T=Y o X^{-1}: X^{-1} is merely a homeomorphism at this stage.

At almost every z, w has an Alexandrov Hessian H and X,Y are differentiable. Put x=X(z), y=Y(z), and define symmetric forms on T_zM,

    A=D^2_zz[c(x,z)/t],       B=D^2_zz[c(z,y)/(1-t)],
    P=A-H,                   Q=H+B.

Both half-geodesics are strictly before cut, even if the full ray is conjugate. The fixed-endpoint costs in these formulas are therefore smooth on common neighborhoods. The source's two-sided supports

    -v(y)-c(z',y)/(1-t) <= w(z') <= u(x)+c(x,z')/t

are equalities at z. Their second-order expansions show P>=0 and Q>=0. Their sum is

    D=P+Q=A+B,

the Hessian in the joining point of the broken action c(x,z')/t+c(z',y)/(1-t).

Differentiate the identities grad w(z)=D_z[c(X(z),z)/t] and grad w(z)=-D_z[c(z,Y(z))/(1-t)]. With

    B_X=D_zx[c(x,z)/t],       B_Y=D_zy[c(z,y)/(1-t)],

one obtains at these almost-everywhere points

    dX=-B_X^{-1}P,            dY=-B_Y^{-1}Q.                 (4.1)

The mixed maps B_X,B_Y are invertible. Their norms and inverse norms are bounded on the compact bundle of half-minimizing rays. In local coordinates, connection terms cancel in the differences A-H and H+B because the first derivatives of the touching functions agree. Thus(4.1) is also the coordinate differentiation formula used in the change-of-variables argument below.

## 5. Conjugacy gives exactly the cancellation needed by the cofactor

The form D is positive semidefinite and is singular precisely when the full minimizing geodesic from x to y is conjugate. This is the source's broken-action/Jacobi factorization. Here is a direct description of the same classical operation.

For a joining variation a in T_zM, solve the Jacobi boundary-value problem from 0 at x to a at z on the first half, and from a at z to 0 at y on the second. Each problem is uniquely solvable because the halves are nonconjugate. The derivative of the broken-action gradient is the mismatch of the two one-sided velocities at z. Thus Da=0 exactly when these two fields match derivatives and form one Jacobi field vanishing at the full endpoints. A nonzero full Jacobi field cannot have value zero at z, because the first half would then have a nonzero endpoint-zero Jacobi field. This identifies ker D with the full endpoint-conjugacy kernel. Equivalently the source writes J(1)=J_t(1-t) D J(t), with both short-piece factors invertible.

We use the following elementary algebra in the COMMON joining tangent space:

    P,Q symmetric PSD and P+Q singular  ==>  Q adj(P)=0.     (5.1)

If rank P<=n-2 then adj(P)=0. Otherwise P has rank n-1, since P+Q singular prevents P from being positive definite. Take a nonzero a in ker(P+Q). Positivity gives Pa=Qa=0. Therefore ker P=span(a), the range of adj(P) is contained in span(a), and Q adj(P)=0. No simultaneous diagonalization of P,Q is assumed.

Adjugates multiply in reverse order even for singular matrices, by polynomial continuation of the invertible identity. From(4.1),

    dY adj(dX)
      = -B_Y^{-1} Q adj(P) adj(-B_X^{-1}) = 0              (5.2)

whenever X(z) belongs to E and the above derivatives exist. Coordinate volume factors and frame changes do not affect this vanishing.

In particular det dX=0 on X^{-1}(E) almost everywhere. The Lipschitz area formula already shows vol_g(E)=0, without needing an endpoint a.e. Jacobian theorem. More importantly,(5.2) kills the WEIGHTED cofactor representing derivative measure; merely knowing this volume-null conclusion would be insufficient.

## 6. Distributional composite formula; no assumed inverse Sobolev regularity

Let X:V->U be a Lipschitz homeomorphism between open Euclidean coordinate domains, and let Z:V->R^m be Lipschitz. Assume first that X preserves orientation, so det DX>=0 almost everywhere. Define f=Z o X^{-1}. For a compactly supported smooth scalar test phi on U, injective area formula gives

    integral_U f_alpha partial_j phi dx
      = integral_V Z_alpha [partial_j phi](X) det DX dz.

Writing A=DX, the polynomial identity cof(A) A^T=det(A) I and the Lipschitz chain rule give

    det A [partial_j phi](X)
      = sum_k cof(A)_(jk) partial_k(phi o X).

The rowwise Piola identity sum_k partial_k cof(DX)_(jk)=0 holds distributionally for Lipschitz X. One can see this by mollifying X on the relatively compact support: the smooth mixed-derivative cancellations prove it for each mollification, and cofactors converge in every finite L^p. Products with the Lipschitz function Z_alpha obey the weak product rule. Integrating by parts yields

    integral_U f_alpha partial_j phi
      = -integral_V (phi o X) [DZ adj(DX)]_(alpha j) dz.

Thus the full distributional derivative, including any singular part, is

    Df = X_#(DZ adj(DX) dz).                              (6.1)

This is a finite matrix measure on relatively compact sets; it proves BV membership rather than assuming it. Orientation-reversing X introduces its constant local degree sign. The vanishing and norm conclusions are unchanged.

On Riemannian manifolds the same formula is intrinsic after replacing adj(dX) by the volume-adjusted cofactor C_X:T_(X(z))M->T_zM, characterized on nonsingular points by

    C_X=J_gX (dX)^{-1},

and extended polynomially in oriented orthonormal frames. For a scalar/vector-valued Z,

    D(Z o X^{-1})=X_#(dZ C_X dvol_g),                     (6.2)

where the covector on the right is based at X(z). To verify the volume factors in coordinates, write dvol_x=a(x)dx and dvol_z=b(z)dz. Testing with div_g V=(1/a)partial_j(aV^j), change variables, and apply the Euclidean Piola identity to a(X)V(X). The remaining coefficient is [a(X)/b] DZ adj(DX), which is precisely dZ C_X. No derivative of a has been discarded. This also proves the local transformation law.

One may work on orientation-compatible coordinate patches; no global orientation is required. Local homeomorphisms have a constant orientation sign, absorbed as above. Partitions of unity localize the distribution identity and the total variation measure. For a fixed smooth isometric embedding iota:M->R^m, set Z=iota o Y. Since X,Y are globally Lipschitz, the resulting measure is globally finite and

    |D(iota o T)|(M)
      <= integral_M |d(iota o Y) C_X|_HS dvol_g
      <= sqrt(n) L_g^n vol_g(M).                          (6.3)

The last estimate uses |d(iota o Y)|_HS<=sqrt(n)L_g and ||C_X||_op<=L_g^{n-1}. These inequalities are invariant, so the estimate does not multiply by a number of charts chosen using the individual transport map.

## 7. Removal and the exact conclusion

Restrict the measure in(6.2) to E. Since X is a homeomorphism, that restriction is the pushforward of its density restricted to X^{-1}(E). At almost every point of X^{-1}(E), equation(5.2) shows this density is zero, also after composition with iota. The nondifferentiability set has zero parameter volume and contributes zero. Therefore

    |D(iota o T)|(E)=0.                                  (7.1)

On O, Section3 proves iota o T locally W^{1,1}. Hence its distributional derivative there is absolutely continuous. Its derivative on all of M is finite by(6.3), has no singular part on O by local Sobolev regularity, and vanishes on E by(7.1). It is therefore absolutely continuous globally. Compactness supplies L1 values, so T belongs to W^{1,1}(M;M). The weak differential is tangent to the embedded manifold almost everywhere by the usual smooth constraint/chain rule, and its intrinsic Hilbert–Schmidt norm is the norm of the embedded derivative.

Apply the same proof to the reversed density pair. The geometry-only Lipschitz constant can be the same L_g at t=1/2; reversing exchanges X and Y. Thus T^{-1} also belongs to W^{1,1}, and summing(6.3) in both directions proves the frozen inequality with the permissible choice

    K_g=2 sqrt(n) L_g^n vol_g(M).

No value of lambda or Lambda enters this last bound. They are essential for invoking the source's all-points contact homeomorphisms and the local DPF theorem, but their local exponents and constants were never summed across a degenerating family of cost charts. This proves exactly STATEMENT.md relative to the declared inputs.

## 8. What this proof does and does not pay

The focal removal is a compatible composition of the actual midpoint geometry, a weighted cofactor/Piola identity, and local smooth-cost Sobolev regularity. It handles the full distributional derivative, not only the almost-everywhere differential. It does not require a uniformly positive midpoint density; I225's determinant diagnostic is consequently respected. It does not infer cut avoidance from Hölder continuity, nor use a bi-Sobolev inverse chain rule before establishing that regularity.

The uniform L1 bound is not asserted to give uniform integrability of derivative densities across all admissible density pairs.

Whether the weighted-cofactor cancellation is a substantial contribution after crediting all these source/classical operations is an independent contribution question. The author does not assign that grade. The fact that the theorem has rough densities, allows focal contacts, or has a geometry-only norm bound is not itself evidence that the remaining operation is nonroutine. A reviewer may reduce this proof to a technical composition. Bounded searches and incomplete transitive reads establish no literature-priority or current-open claim.
