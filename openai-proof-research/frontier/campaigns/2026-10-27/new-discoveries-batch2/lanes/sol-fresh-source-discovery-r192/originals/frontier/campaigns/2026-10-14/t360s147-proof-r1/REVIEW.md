# T360S147 — independent full correctness review r1

## Verdict and immutable scope

**PASS for the entire unchanged frozen statement**, relative to the stipulated Source360 theorems and operative proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, with the established local De Philippis–Figalli theorem and the classical operations identified below. No mathematical repair or additional hypothesis is required. This is solely a correctness verdict. No contribution, acceptance, count, priority, current-open, or exhaustive-search verdict is assigned.

The reviewed statement is exactly the 2121-byte `STATEMENT.md`, SHA256 `5c36d8a2237f1416282ed5b930cc945ab78ec3fac42214685199c5228dc98ddc`. The reviewed author proof has SHA256 `90f07fcca19ff034d9ac46d7dc94fefe85cf57aaf05ee814990b205d2ca0d719`. These files were not changed. The conclusion is global bi-W^{1,1} for the homeomorphic optimal representatives on every fixed closed connected smooth weak-MTW manifold, dimension n>=2, including nonorientable manifolds and conjugate contacts, with one intrinsic Hilbert–Schmidt L1 bound common to all positive finite density-bound classes. No smooth-density, nonfocal, cut-separation, approximation, or higher Sobolev conclusion replaces any frozen clause.

The argument passes because it proves a measure identity for the full distributional derivative before removing its focal part. Local almost-everywhere differentiability or almost-everywhere cut avoidance would not suffice.

## 1. Exact operative inputs

Both canonical Source360 companions were authenticated against the complete 13223-entry preprints tree, whose SHA256 is `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`. The truncated `tree.json` was not used. Canonical paths, pin URLs, sizes, Git blob SHA1s, SHA256s, and independently selected copies are in `INPUT-AUTH.json`.

The foundation's actual `geo:prelim` proof gives ordinary semiconvex subgradients as the convex hull of **all** active minimizing logs. `geo:support` is an all-ordinary-subgradient assertion, and the actual proof of `geo:sections` supplies the stated lifted diameter inequality, including its midpoint gap identity. The entire `geo:intermediate` proof supplies two-sided touching supports, geometry-only C^{1,1} bounds, and the backward-flow formulas. These are stipulated inputs, not upstream claims challenged by this review.

In the Hölder companion, the actual proof of `sc:power`, together with `jet:contradiction` and the conclusion, gives a unique contact endpoint at **every** pole, and the same for the reverse pair. This is stronger than merely selecting a continuous version of an almost-everywhere map. The full mathematical section/scalar/jet proof chain was read, with its proof operations stipulated. `spec:Jacobi-factorization` is an exact identity at a singular full endpoint, with both short-piece factors invertible. It is not an identity obtained only after inverting the full Jacobi matrix.

The external regularity input is De Philippis–Figalli, arXiv:1211.2341v1, Theorem `w21eps` (1.1), for a strictly c-convex local Alexandrov solution with bounded positive contact-measure density, smooth twisted nondegenerate cost, and orthogonal-pair condition (C1). Its full mathematical proof and approximation footnote were read. FKM1107.1014v1's cost-coordinate, dual-norm, section-height, and engulfing arguments were compared directly. CEMS2001's cut-locus and Jacobian proofs were read for the precise limits of almost-everywhere arguments. DPF1209.5640v2's continuous-density partial-regularity statement is not a substitute for the input actually used here.

## 2. Every contact has one log; the potential is C1

For the given pair, the source provides the all-points contact homeomorphism T. Fix x. Every p in the zero-height lifted section has endpoint T(x), and every minimizing log to T(x) lies in that section. It is nonempty and compact. Its endpoint v-oscillation is exactly zero, so the actual source inequality gives diameter squared <=8(0+0)=0. Thus there is a single active minimizing log p(x).

The active-hull equality in `geo:prelim` now gives the ordinary subdifferential exactly `{p(x)}`. The standard semiconvex argument is applicable: after adding a local fixed quadratic, an ordinary convex function with singleton subdifferential at an interior point is differentiable there. Consequently du=p everywhere. Subgradients have a uniform bound, and their graph is closed by the uniform quadratic supporting inequalities. In local tangent-bundle coordinates, every subsequential limit over x_j->x therefore equals p(x). Compactness gives continuity, so u is C1. The same holds for v.

The set E of singular `(d exp_x)_{p(x)}` is closed. On its complement the log is unique and nonconjugate. The source's actual interior-characterization lemma then puts it strictly before cut and gives a smooth true-cost product neighborhood. A unique conjugate contact remains allowed. No implication from mere Hölder continuity to cut avoidance is used.

## 3. The local DPF hypotheses are paid

Take a nonfocal contact `(x0,y0)`. Shrink coordinate balls U,V so their closures lie in a smooth true-cost product patch and the mixed determinant is nonzero. Uniform closeness of the mixed derivative to its invertible central value, on convex coordinate balls, gives both twist diffeomorphisms after shrinking. The required C3 and mixed fourth-derivative bounds and the log mixed-determinant bound are finite there.

Here is the convention check rather than just a curvature-name match. In coordinates let `p_i=-partial_i c(x,y)` and let `v=p^sharp` at fixed x. With the Levi-Civita symbols at x,

    A_DPF,ij(x,p) = -partial_ij c(x,y)
                  = -Hess^g_ij c(x,y) + Gamma^k_ij(x) p_k.

The last term is linear in p and disappears under two p derivatives. If xi is a coordinate tangent vector and eta a coordinate covector, `xi^i eta_i=0` is precisely `g(xi,eta^sharp)=0`. Varying p affinely varies the minimizing initial vector affinely by eta^sharp. Hence

    D_pp A_DPF[xi,xi,eta,eta] = (2/3) S_source(x,p^sharp)[xi,eta^sharp] >=0.

The positive factor and minus sign are correct. This holds at every pair in the chosen product patch. No condition on nonorthogonal pairs or strict MTW has been inserted.

Choose U smaller so every actual endpoint over its closure lies in a compact subneighborhood of V. Restrict the representing datum to V using the original values `-v(y)`. The representation still equals u, and every equality contact for this representation is a global contact. Even if one uses the canonical local dual completion, an interior contact has `du=-c_x(x,y)`; local twist and the already established C1 property force y=T(x). Thus no extra local contact mass is introduced. Reverse contact uniqueness supplies strict c-convexity.

The global nonnegative gap `u(x)+c(x,y0)+v(y0)` has the unique zero x0. On the compact complement of any chosen neighborhood of x0 it has a positive minimum. Its sufficiently small sublevel is therefore relatively compact in U. Its contact image is relatively compact in V by continuity of T. On the boundary, u equals the supporting mountain plus the section height, precisely the boundary condition used in DPF. This supplies the local domain/section requirements without a global smooth cost chart. The actual FKM local-domain remark `R:no-need-B2-B2u` confirms that once strictness is available the later local section arguments do not require global c-convex ambient domains; its smallness and interior-margin requirements are met by these shrinking sections. One could also choose sufficiently small strongly c-convex coordinate balls locally; no uniform size near cut is claimed or needed.

The measure hypothesis follows setwise, before any weak derivative assertion. For each Borel A in the section, homeomorphic transport gives `mu1(T(A))=mu0(A)`, hence

    (lambda/Lambda) vol_g(A) <= vol_g(T(A))
                            <= (Lambda/lambda) vol_g(A).

If a(x),b(y) are the smooth coordinate volume densities, the coordinate contact measure even has the Radon–Nikodym density

    rho0(x) a(x) / [rho1(T(x)) b(T(x))]

almost everywhere, by pushforward testing. This is bounded positively on the patch. The equivalent differential Monge–Ampère expression contains the additional smooth nonzero `|det c_xy|` factor. Both conventions have bounded positive local data. No a.e. determinant equation is being substituted for a setwise measure condition, and no continuity or derivative of either rho is used.

All the actual DPF hypotheses therefore hold. Its theorem gives local W^{2,1+kappa} of u. The endpoint is a smooth function of `(x,du)` on this patch, with the relevant values contained in a compact smooth branch, so the ordinary Sobolev chain rule gives local W^{1,1+kappa} of T, in particular W^{1,1}_loc on O=M\E. The reversed argument has the same validity. Local constants may degenerate as cut is approached; none enters the final global bound.

## 4. Common midpoint and the exact derivative factorization

Put t=1/2, w=Q_tu, and

    X(z)=exp_z(-t grad w(z)),
    Y(z)=exp_z((1-t) grad w(z)).

Since x->(x,p(x)) is a homeomorphism onto the full ordinary subgradient graph, the inverse of the source intermediate projection gives a homeomorphism X. Its other endpoint is Y=T∘X, also a homeomorphism. Source bounds on grad w and Hess w, and smooth geodesic flow on the compact bounded-velocity set, give a common Lipschitz bound L_g>=1 for X and Y depending only on the geometry. This does not assert any Lipschitz bound for X^{-1} or T.

At simultaneous differentiation points use the common space T_zM and write

    A=Hess_zz[c(x,z)/t], B=Hess_zz[c(z,y)/(1-t)], H=Hess w,
    P=A-H, Q=H+B.

Both cost pieces are smooth: each is a proper initial segment of the minimizing full ray, after reversal for the second. The entire bundle of half-minimizing rays is compact and lies inside the open injectivity domain. Thus both mixed Hessians and their inverses have uniform geometry-only bounds, including when the full ray is conjugate.

The actual two-sided source supports touch at z. Their second-order inequalities give P,Q positive semidefinite, without commuting or diagonalization assumptions. With `B_X=D_zx(c/t)` and `B_Y=D_zy(c/(1-t))`, differentiation gives

    H=A+B_X dX, H=-B-B_Y dY,
    dX=-B_X^{-1}P, dY=-B_Y^{-1}Q.

Both signs and multiplication orders agree with the author proof. In arbitrary coordinates the Christoffel terms in the touching Hessians cancel because their first derivatives agree; these equations are simultaneously the coordinate equations needed for Piola. The required full-measure set follows from C^{1,1}/Rademacher. In fact if X is differentiable at a point, the smooth half-cost identity recovers differentiability of grad w there; thus the check is not relying on an unaccounted positive-volume derivative stratum.

## 5. Full conjugacy is equivalent to singular P+Q

The sum `D=P+Q=A+B` is the Hessian at the joining point of the broken action. It is positive semidefinite, either by P,Q or by the minimum property of broken energy along a minimizing ray.

For a joining variation a solve the two Jacobi endpoint problems, with values (0,a) on the first half and (a,0) on the second. The half-piece nonconjugacy makes both solutions unique. The Hessian D applied to a is the difference of their one-sided covariant velocities at the join. Therefore Da=0 precisely when they join to a full Jacobi field vanishing at x and y. A nonzero full endpoint-zero Jacobi field cannot vanish at the midpoint: otherwise half-piece nonconjugacy and Jacobi uniqueness would make the full field zero. This establishes an isomorphism of kernels and BOTH directions, at singular as well as regular endpoints. Equivalently the actual source identity is

    J(1)=J_t(1-t) D J(t),

with both outer matrices invertible. No inversion of J(1) is used.

If D is singular, a nonzero a in its kernel satisfies Pa=Qa=0 by positivity. If rank P<=n-2 its adjugate vanishes. Otherwise rank P=n-1, because P cannot be positive definite, and the range of adj(P) lies in its one-dimensional kernel spanned by a. Hence `Q adj(P)=0`. No commutation follows or is needed. Adjugates multiply in reverse order by their polynomial identity even at singular matrices, so

    dY adj(dX)=(-B_Y^{-1}) Q adj(P) adj(-B_X^{-1})=0

at every focal parameter point where these derivatives exist. Multiplication by smooth embedding derivatives or metric volume factors preserves the zero. Also det dX=0 there. Injective Lipschitz area formula therefore gives vol_g(E)=0, but the stronger weighted identity, rather than this nullness, is what removes derivative mass.

## 6. Full distributional pushforward, including critical points

This is the central independent check. Work first on connected Euclidean coordinate domains, with X:V->U a Lipschitz homeomorphism, Z:V->R^m Lipschitz, and f=Z∘X^{-1}. Write A=DX. Its local topological orientation sign epsilon is constant. At a differentiability point with invertible A, closeness to the invertible linear map on sufficiently small spheres identifies the local degree as sign det A. Thus `det A=epsilon |det A|` almost everywhere; at singular differentiation points both determinants are zero.

For phi smooth compactly supported in U, its pullback psi=phi∘X is Lipschitz with compact support in V, since the inverse is continuous. Injective area formula gives

    integral_U f_alpha partial_j phi dx
      = epsilon integral_V Z_alpha (partial_j phi)(X) det A dz.

The row convention is `cof(A) A^T=det(A) I`, so the Lipschitz chain rule gives

    det A (partial_j phi)(X)=sum_k cof(A)_jk partial_k psi

almost everywhere, including at singular A. No inverse matrix is used.

For Lipschitz X the rowwise Piola identity holds distributionally. Indeed, mollify X on a neighborhood of the compact support. The smooth mixed-derivative cancellation gives the identity for each mollification; bounded derivatives and strong finite-Lp convergence imply strong finite-Lp convergence of all cofactors. It passes to the distributional limit. Moreover the identity can be tested against compactly supported Lipschitz functions: approximate such a test in W^{1,1} by smooth compactly supported functions; the coefficient cofactor is bounded. Apply it to `Z_alpha psi`. The weak product rule for these Lipschitz factors then yields

    integral_U f_alpha partial_j phi dx
      = -epsilon integral_V psi [DZ adj(DX)]_alpha,j dz.

Consequently the **entire** distributional derivative is the locally finite measure

    Df=X_#(epsilon DZ adj(DX) dz).

This proves BV locally; it does not assume it or an inverse Sobolev theorem. In particular it does not discard the critical parameter set. As a diagnostic, for a strictly increasing Lipschitz scalar map a with a'=0 on a positive-measure fat Cantor set C, take `X(s,t)=(a(s),t)` and Z the identity. The formula retains the nonzero density diag(1,0) on C×(0,1), which pushes to singular inverse derivative mass. A formula that removed all zero-Jacobian parameters would fail this example. The author's weighted density retains precisely the mass that must later be canceled.

For the metric version let `dvol_x=a(x)dx`, `dvol_z=b(z)dz`. Testing against a smooth vector field V uses `div_g V=a^{-1} partial_j(a V^j)`. Apply the Euclidean identity to the smooth coefficients `a V^j`. The tensor density after changing to parameter volume is

    C_X=epsilon [a(X)/b] adj(DX),
    Df=X_#(dZ C_X dvol_z).

At nonsingular points this is `C_X=J_gX (dX)^{-1}`, with J_gX the **nonnegative metric Jacobian**. At singular points the displayed degree-signed cofactor is the continuous polynomial extension in local oriented frames. This makes explicit the local sign already described in author Section 6. The derivative of a is included in the divergence test; it has not disappeared through an invalid differentiation of a composed Lipschitz function. No derivative of b is needed, since it enters by reexpressing the parameter integral.

Changing either coordinate orientation changes epsilon and the signed cofactor consistently. The resulting density cofactor and tensor measure are intrinsic. One can choose compatible orientations on each paired neighborhood of a point and its preimage; no orientation of the whole manifold is required. For f=iota∘T use Z=iota∘Y. Compactness gives global finiteness. A target partition of unity glues the local identities: terms differentiating the partition sum to zero, and the variation estimate uses the sum of its nonnegative weights, equal to one. There is no multiplication by the number of charts or any density-dependent localization constant.

In orthonormal frames `||C_X||op<=L_g^{n-1}` and `|d(iota∘Y)|HS<=sqrt(n)L_g`, since iota is isometric. Thus the intrinsic matrix-measure variation obeys

    |D(iota∘T)|(M)<=integral_M |d(iota∘Y) C_X|HS dvol
                   <=sqrt(n) L_g^n vol_g(M).

Coordinate determinant and metric volume factors are already accounted for by C_X; they do not add an atlas or embedding-dimension factor.

## 7. Removal, both directions, and the uniform constant

Because X is a homeomorphism, restriction of this pushforward measure to E is exactly the pushforward of its density restricted to X^{-1}(E). At almost every point of that preimage the weighted cofactor is zero by Section 5. The residual nondifferentiability set has zero parameter volume and carries no part of this represented measure. Therefore `|D(iota∘T)|(E)=0`.

On O, the local DPF conclusion identifies the derivative with an absolutely continuous weak derivative. A countable cover of O suffices to remove its singular part; no local norms are summed. The global derivative is finite by the preceding intrinsic estimate and has no singular part on either O or E. The compact-valued function is L1. Hence iota∘T is globally W^{1,1}.

Its differential is tangent to iota(M): take a smooth tubular projection near the compact embedded manifold, smoothly extend it for the chain rule, and differentiate the identity projection∘f=f. Its derivative on the image is the tangent projection, so Df is tangent almost everywhere. The isometric embedding identifies its norm with the intrinsic Hilbert–Schmidt norm. Smooth transition/extension between any two fixed embeddings on the compact image supplies the usual equivalence in the frozen definition.

Repeat with the reversed density pair. The very same geometry-only bound is available at t=1/2; reversal interchanges the two midpoint endpoints. It yields W^{1,1} for T^{-1} and the same variation estimate. Consequently

    K_g=2 sqrt(n) L_g^n vol_g(M)

is a valid common bound for the sum in the frozen statement. Lambda, lambda, local exponents, cut-distance scales, chart counts, and density derivatives do not enter it. Positivity and boundedness are used to obtain the contact homeomorphisms and local contact-measure bounds; those uses do not change K_g. The a.e. uniqueness assertion is the exact source transport interface. If a displayed density class is empty the universal assertion is vacuous.

## 8. Actual old-scope comparison and limitations of this verdict

The five specifically required old files were read in full. I07 already proves a cofactor/change-of-variables inverse W^{1,1} convergence statement under its stated p>3, positive-Jacobian and inverse-Sobolev assumptions. I331 already treats exceptional images carefully using Lipschitz pieces and proves inverse-energy/cofactor identities in its bi-W^{1,2} setting. These operations are credited. Neither permits silently assuming the endpoint inverse Sobolev chain rule in this review. The present full distributional calculation supplies that missing premise for the present geometry rather than citing those old arguments outside their hypotheses.

I07's cut-avoidance/smoothness target is unchanged and not solved by permitting focal contacts. I225's full uniform square-root stability/IC target is unchanged: the current proof makes no comparison between two different transports and uses no positive midpoint-density floor. I331's full three-dimensional simultaneous bi-W^{1,2} approximation target is unchanged: no approximation or squared inverse-energy claim is made here. This comparison assigns no fresh grade to any old target.

This review checks a mathematical implication, not a formalization. Classical area formula, basic BV/Sobolev calculus, topological local degree, smooth isometric embedding, and the stated external DPF theorem are imported in their standard forms, with the operative Piola/composite and geometric compatibility arguments proved explicitly above. A fresh line-by-line proof audit of every classical/transitive original was not conducted. Full actual read extents, including primary-proof-chain limits, are separately recorded in `READING-COVERAGE.md`. No search absence or finite matrix experiment supplies a premise. Artifact authentication and copied controls establish bytes and read-only behavior only.
