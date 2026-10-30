# T372L127 — author proof of the frozen logarithmic estimate

This is an author argument for the entire unchanged frozen-scope.md, SHA2566e39d59e65aecf9fc8710244c7eccbe7964e38af10287ad173663585539d790a. It has no independent correctness or contribution verdict. No campaign count is assigned. The two calculation files are part of this proof, not separately proposed findings. Every pinned theorem and operative proof input is stipulated; external primary bodies are not covered by that stipulation.

We first prove a quantitative estimate when smooth extensions agree outside Omega, using only uniform C100 bounds there. We then remove that intermediate agreement by the finite-order boundary calculation. Constants below may depend on fixed balls, direction atlases and finite derivative orders; these choices will depend only on Omega,c,M. Positive exponents can decrease a finite number of times. None depends on an individual pair or on its higher derivatives.

## 1. Inherited physical and transport operators

Put m=mu, k=lambda+mu, ell=lambda+2mu, c0=m/ell, r=k/ell=1-c0 and g=grad log m. All denominators below are bounded away from zero on an elliptic bounded class. The source's displacement-divergence augmentation has scalar Laplacian principal part. For an independent pair (u,d), it uses

    R_i=m Delta u_i+k partial_i d
          +sum_j m_j(partial_j u_i+partial_i u_j)+lambda_i d,
    S=ell Delta d+2 grad k dot grad d+2 grad m dot Delta u
          +2 sum_(i,j) m_ij partial_i u_j+(Delta lambda)d,
    Lcal=(m^-1 R, ell^-1[S-2m^-1 grad m dot R]).           (1)

For an actual physical solution d=div u, both R and S vanish. The difference of two normalized augmented operators has order at most one. The supported Carleman and physical solvability operations in the source give, for E=exp(theta dot x/h) and theta dot theta=0,

    ||E^-1 U||H_h^1 <= C h ||E^-1 Lcal U||H_h^-1         (2)

for compactly supported U, and a uniformly L2 bounded right inverse for the conjugated physical equation on a fixed ball. Its scaled interior estimate controls two derivatives with their h powers. These are the actual source operations, not an unrestricted augmented DN map.

The leading physical fiber is E_theta=H_theta plus C, where H_theta={a:theta dot a=0}. For a leading pair (a,b), normalize by

    p=sqrt(m)a,
    s=-k b/(2sqrt(m))-(g dot p)/2.

The source's transport equation is D_theta(p,s)=M_theta(p,s), where

    M_theta=[0,theta; Q_theta dot,T_theta],
    T_theta=D_theta log(k/ell),
    2 Q_theta=[(c0 D_theta log k-(theta dot g)/2)g
                                      -c0 D_theta g].  (3)

In particular the coefficient in Q is m/ell, not k/ell. On each local transverse interval the source supplies a smooth invertible frame and realizes its columns, multiplied by an arbitrary smooth transverse cutoff, as the leading pairs of exact physical CGOs. The compatible recursion and physical correction give O(h) convergence in L2 of both normalized displacement and ACTUAL divergence. We use a fixed recursion order8, not an unbounded-order construction.

## 2. Uniform finite-order versions of these inputs

Here and through Section6 assume the extended pairs agree off closure Omega, are constant outside one fixed ball, have uniform positivity bounds, and have uniformly bounded C100 norms on a larger fixed ball. Choose all successive exterior balls with fixed positive separations, for example radii r,2r,...,10r, with closure Omega strictly inside the smallest. Use a finite smooth atlas of the projective null conic, with representatives bounded above and away from zero.

The constant in (2) is uniform on this class. In its actual proof the lower-order coefficients of (1) are absorbed into a convexified scalar Laplacian estimate. Their multiplier bounds use only a fixed finite number of low coefficient derivatives. First choose the convexification parameter using that bound, then choose h small uniformly. Removing the fixed convexification factor introduces a finite constant depending on the same bound. The physical right inverse follows by duality, and the scaled interior estimate follows from uniformly elliptic local estimates on h-balls. These arguments use fewer than ten derivatives of lambda,mu; they do not require compactness in the smooth topology.

We explain the less immediate uniform frame assertion. For a square planar operator D+A, local invertible Cauchy-transform frames exist for C^(s,alpha) coefficients: on a sufficiently small disk the equation F=I+Cauchy(AF) is a contraction, followed by elliptic regularity. Transition functions are holomorphic. The same holomorphic-bundle trivialization over a disk used in the source gives a global frame on a slightly smaller fixed disk. This construction requires finite differentiability only; smoothness of the input to every order is not used to obtain a frame of a prescribed finite order.

Near one such coefficient A0 and frame F0, a frame is F0 B, with

    B=I+Cauchy[F0^-1(A-A0)F0 B].                         (4)

Use a fixed extension and cutoff before the Cauchy transform. Smallness in C^(s,alpha) makes (4) a contraction in that Banach space; B is close to I and invertible. Differentiation of this convergent equation gives bounds for each fixed number of external parameter derivatives. The same frame reduces an inhomogeneous transport to an ordinary Cauchy equation, giving the finite-order right inverses needed by the amplitude recursion.

The family of restrictions of our C100-bounded coefficients to rotated planes, on fixed disks and bounded transverse intervals, is precompact in C^(70,1/2). Its closure consists of finite-regularity coefficients for which the preceding frame construction still applies. Cover that compact closure by finitely many neighborhoods of the form (4). This gives uniform frame, inverse and inhomogeneous-solver bounds at every lower order used here. The cover includes the direction and transverse parameters. Product neighborhoods and smaller parameter plateaus can be chosen finitely, so their cutoff derivatives and positive support margins have uniform bounds. For a fixed coefficient pair one selects the applicable neighborhoods; no differentiability in the coefficient-pair index is needed.

This is a finite-regularity compactness argument, not compactness of a bounded smooth class in C-infinity. Its only limiting uniqueness input is planar holomorphic continuation, valid for the finite-regularity frames just constructed. It does not invoke global elasticity uniqueness for nonsmooth coefficients.

For the supported operator P=D-M2 left+M1 right, no compactly supported homogeneous distribution exists. Local finite-regularity frames reduce such a solution to a holomorphic matrix; the identity theorem propagates its zero exterior value. Uniform supported H1 coercivity follows by contradiction and Rellich compactness over a compact C1 coefficient family: a normalized failing sequence would converge to a nonzero supported homogeneous solution. Ordinary elliptic estimates then give

    ||W||H^(j+1) <= C_j ||P W||H^j                     (5)

for supported W and each fixed j needed below. The least-squares inverse varies smoothly in the direction and transverse parameters by bounded-operator inversion. Its derivatives through20 at j=24 use coefficient derivatives of total order at most44, with two additional derivatives to form (3).

For clarity, the finite budget used here is: derivatives through70 for frame compactness and parameter perturbation; at most20 further differentiations of a frame with respect to plane parameters or space in the fixed-order8 amplitude recursion, taken at lower norms; transport coefficients use two derivatives of the original pair; supported inverses use j=24 and parameter order20; the strong residual is needed only through order12. These requirements can all be taken inside coefficient C80. The spare20 derivatives in the C100 bound allow the fixed extensions, coordinate products and ordinary Sobolev embeddings. No step differentiates the unknown coefficients more than80 times. The high polynomial degrees or repeated fixed cutoffs in a finite construction change constants, not that coefficient-derivative count.

## 3. Noisy physical transfer and weak transport comparison

Let delta be the full physical DN difference. Take three exact first-medium physical CGO columns with a leading frame on a transverse plateau. Their boundary H^(1/2) norms are at most C exp(C/h); fixed polynomial losses are absorbed in C/h. Solve the second-medium Dirichlet problem in Omega with each same displacement trace and paste to the original solution outside. If v2 denotes the pasted H1 field, its residual on the larger ball is exactly

    a2(v2,phi)=<(Lambda2-Lambda1)trace u1,trace phi>.

Solve away this residual with zero outer boundary condition. Coercivity and the fixed trace theorem give a correction z with ||z||H1<=C delta exp(C/h). Thus u2=v2-z is an exact global second-medium PHYSICAL solution. Outside Omega, u2-u1=-z. On fixed exterior annuli every requested finite derivative is bounded by C delta exp(C/h), by interior regularity. This is the compatible variational transfer already present in I112/I115, with its actual residual retained.

Write U_j=(u_j,div u_j) and W=chi(U2-U1), where chi=1 on the inner ball and all its derivatives are in a fixed exterior annulus. Equation (1) gives

    Lcal2 W=chi(Lcal1-Lcal2)U1+[Lcal2,chi](U2-U1).

The first forcing has weighted H_h^-1 norm at most C/h, using the source's first-derivative CGO bound. The commutator is controlled by the exterior correction. Equation (2) therefore gives

    ||E^-1 W||H_h^1 <= C                              (6)

whenever delta exp(C/h)<=1. The physical correction precedes augmentation: no differentiated interface delta is asserted to lie in H_h^-1.

For a physical normalized pair a=E^-1u, b=E^-1 div u, the exact constraint is

    theta dot a=h(b-div a).                            (7)

Choose a smooth n_theta with theta dot n_theta=1 and project a to a^c=a-n_theta(theta dot a). By (7) this projection changes a bounded L2 pair by O(h) in H^-1, while retaining an L2 bound. Divide R=S=0 by h^-1 and use (3). The resulting constrained normalized transport has residual O(h) in H^-2: the second derivatives carry h, and the projected H^-1 error is differentiated at most once. This follows directly from (1); it uses neither a small high derivative norm nor an unphysical scalar component.

Let V_j be the matrices of these projected, normalized columns and let Y1 be the leading first-medium normalized frame. On its transverse plateau set

    G_h=I+chi(V2-V1)Y1^-1,
    P_theta W=D_theta W-M2 W+W M1,
    f=M2-M1.                                          (8)

Using V1-Y1=O(h) in L2, the product rule and the exterior correction give

    ||G_h-I||L2 <= C,
    ||P_theta(G_h-I)-f||H^-2(y,t)
                      <= C[h+delta exp(C/h)].          (9)

The term f(V1-Y1)Y1^-1 is retained and is O(h). Derivatives of chi occur where V2-V1 is small. Subtracting V1, rather than simply subtracting Y1 from V2, is essential for the fixed support property. All supports in (9) lie strictly inside a fixed larger planar disk. The transverse cutoff in the source frame is one on a smaller plateau and supplies all three columns there. No common boundary kernel or subsequence is used.

## 4. Strong residual on all planes

Apply the full argument in transport-calculation.md to (9), with j=24 and a strictly larger support disk. Set w=T_24 f and G=I+w. Its residual e=P w-f satisfies the normal equation P^dagger(1-Delta_y)^24 e=0 in the support disk. Pairing (9) against the interior smooth adjoint residual gives a small L2 norm of e; parameter interpolation gives

    ||e||C12 <= C epsilon^b,
    epsilon=h+delta exp(C/h), b>0.                     (10)

All required a priori mixed bounds are supplied by Section2. The Hilbert projection is not being applied as a high-regularity inverse to arbitrary H^-2 data. Its particular normal equation, the support margin and the bounded parameter derivatives are what justify (10).

Comparisons produced in overlapping charts need not agree. Conjugate them into the same bundle coordinates and average affinely with a partition of unity in the direction and transverse variables. D_theta differentiates neither such variable. Thus the affine combination still obeys (10), with f multiplied by weights summing to one. The finite plateau construction in Section2 supplies bounded derivatives of these weights. Outside a fixed physical ball every comparison equals I. Extending by I there produces one global section G of End(E) over physical space times the entire projective null conic, with uniformly bounded higher norms and small C12 transport residual. Its construction depends on the coefficients, not on h; h is used only to estimate the residual.

## 5. Approximate holomorphic rigidity

In a holomorphic direction chart use a holomorphic representative theta and the holomorphic frame of E=H plus O. At FIXED physical x, M_theta is holomorphic. Differentiating the transport equation gives

    P_theta(partial_bar G)=partial_bar e.

The derivative has compact physical support. Equation (5), followed by parameter differentiation and interpolation at lower orders, bounds partial_bar G in the finite C norms needed below by C epsilon^b. Derivatives at fixed moving-plane coordinates are converted to fixed-x derivatives by the chain rule, which adds only bounded coefficients times spatial derivatives. The C12 budget in (10) leaves these derivatives available.

For each x, project G onto the finite-dimensional holomorphic sections of End(E) on the compact conic. The Cauchy–Riemann elliptic estimate on that fixed bundle gives a holomorphic Gamma with Gamma-G small in lower C norms, including the required spatial derivatives. The projection is fixed and linear; outside the support ball it sends I exactly to I.

The source identifies H with O(-1)^2, its null line N with O(-2), and H/N with O. Hence Gamma=[F,0;A,f], with f independent of direction. The upper-right transport equation is F theta-theta f=O(epsilon^b). On the finite-dimensional space of these holomorphic sections its kernel is F=f I: a map vanishing on N factors through O into H, which has no holomorphic section. The quotient inverse is bounded, so F-f I is small, also after spatial differentiation.

The upper-left equation then says

    (theta dot grad f)I_H-theta A=O(epsilon^b).

The linear map on grad f and the holomorphic section A is injective. In its kernel a rank-two scalar matrix equals a rank-at-most-one matrix; theta dot grad f=0 for all null theta, hence grad f=0 and A=0. Finite-dimensional norm equivalence bounds both by C epsilon^b. Integrate grad f from the exterior, where f=1, along fixed-length straight segments. Differentiating the same finite-dimensional relations in x gives

    ||G-I||C5 <= C epsilon^b,
    ||M1-M2||C4 <= C epsilon^b                         (11)

on the constrained fibers, decreasing b if the preceding interpolation required it. These are the entire conic-bundle and rank operations of the source, with errors retained; no local conic arc is substituted for the whole conic.

## 6. Coefficient recovery with errors

The lower-right block gives a C4 bound for grad log(r1/r2). Its exterior value is zero. Integration and differentiation give r1-r2 small in C4, with the extra derivatives obtained from the displayed gradient bound. Thus c1-c2 and beta1-beta2 are small in C3, where c_j=m_j/ell_j and beta_j=grad log(k_j/m_j). All their denominators stay uniformly positive.

Let K be the ambient matrix linear in theta with (Q1-Q2)_theta=K theta. The constrained lower-left part of (11) says that (K theta) dot p is small for every unit p in H_theta. The kernel of this fixed finite-dimensional map of K is the scalar matrices, as proved in the source by null-line preservation. Therefore K-kappa I is small in C3, with kappa=trace K/3.

Put eta=log m1-log m2, v=grad eta, c=c1, beta=beta1 and a=(c-1/2)/c. Expanding (3) gives

    2 Q_j=[(c_j-1/2)g_j g_j^T+c_j g_j beta_j^T
                                     -c_j Hess log m_j]theta.

Move the small c2-c1 and beta2-beta1 terms into a matrix error. Using g1 g1^T-g2 g2^T=g1 v^T+v g2^T gives

    partial_i v_j = sum_a B_ij^a v_a+delta_ij q+F_ij,
    B_ij^a=a(g1)_i delta_ja+[a(g2)_j+beta_j]delta_ia,
    q=-2 kappa/c, ||F||C1<=C epsilon^b.                 (12)

Here B is uniformly C1 bounded. The fields v,q vanish outside the fixed ball. For each s choose i different from s. Commuting derivatives in the ii and si entries of (12) yields

    partial_s q=sum_a[(partial_i B_si^a-partial_s B_ii^a)v_a
                  +B_si^a partial_i v_a-B_ii^a partial_s v_a]
                  +partial_i F_si-partial_s F_ii.

Substitute (12) for the derivatives of v. Together with (12), this is a first-order linear system for (v,q) with bounded coefficients and forcing O(epsilon^b). Along straight segments from the exterior, Gronwall gives v,q=O(epsilon^b). Integrating v gives eta=O(epsilon^b), and hence m1-m2 is small. The r ratio then gives k1-k2 and lambda1-lambda2 small. We have proved the common-exterior estimate

    ||lambda1-lambda2||infinity+||mu1-mu2||infinity
                  <= C[h+delta exp(C/h)]^b.            (13)

All paths and support radii are fixed; no domain-dependent winding or shrinking collar is used in this step.

## 7. Removal of boundary agreement and conclusion

Apply boundary-calculation.md to the ORIGINAL coefficients. It supplies a bound t<=C delta^a, a>0, for normal jets through119 and tangential derivatives through100, using at most248 derivatives of the coefficients in the boundary-layer recurrence and220 in tangential interpolation. Its proof explicitly retains the finite physical energy correction, the full frozen Lamé Jordan solution, the two independent polarizations and the geometry factors. It does not infer a uniform estimate from an unspecified smoothing remainder.

The collar replacement there produces (lambda2',mu2'), identical to the first pair near the boundary, satisfying positivity and

    ||lambda2'-lambda2||C100+||mu2'-mu2||C100
                                           <= C delta^(a/10).

Extend the first pair smoothly across the boundary with a bounded C100 extension operator on the fixed smooth domain. A fixed sufficiently narrow exterior collar retains positivity by the C1 bound; a convex interpolation then makes the extension constant outside a fixed ball. Extend the second modified pair by this SAME exterior. The agreement in an actual interior collar makes the extension smooth, although that collar's width depends on delta. Its global C100 norm is uniformly bounded: on the interior this was just proved, and on the exterior it is the first extension. No C1000 bound for the modified pair is claimed or needed.

The physical energy identity and coercivity give

    ||Lambda2'-Lambda2||H^(1/2)->H^(-1/2)
        <= C[||lambda2'-lambda2||infinity+||mu2'-mu2||infinity].

Indeed use the two solutions with prescribed traces in the bilinear coefficient-difference identity and bound their H1 norms by the trace norms. Therefore the modified data error d is at most C(delta+delta^(a/10)). Apply (13) with d. For d sufficiently small choose h equal to a fixed sufficiently large constant divided by log(1/d), so d exp(C/h)<=d^(1/2). The right side is at most C[log(1/d)]^-b. As d<=C delta^a' with a'>0, this is bounded by C[log(1/delta)]^-b for small delta. The collar replacement error is a positive power of delta and is absorbed in the same bound.

At delta=0 the stipulated exact full-data theorem gives equality. For the remaining bounded-away-from-zero delta, increase C using the uniform L-infinity bound2M. This gives exactly the function omega_alpha and all quantifiers in frozen-scope.md, with alpha=b>0 after the finite reductions. Constants depend only on Omega,c,M and the fixed Sobolev norms. No individual higher derivative enters them. This completes the author argument for T372L127.

## 8. What is credited and what needs independent review

The source already pays physical augmentation, compatible CGO recursion, supported Carleman control, transverse-cutoff frames, supported planar inverses, the full null-conic bundle classification and coefficient finite type. I112/I115 pay the physical variational residual. Classical boundary-layer constructions, including Lin–Nakamura's actual Taylor/ODE method, and Tan–Liu's exact impedance algebra pay the boundary mechanisms. Least squares, elliptic regularity, compact-bundle projection, finite-dimensional norm equivalence and Gronwall are classical. Ruland–Salo's actual scalar known-interior-support proof pays its own optimized CGO/Fourier route, but does not provide this constrained physical comparison. Cekic's actual connection-system transport and holomorphic repair are a close primary comparison with a different DN contract.

The proposed integrated quantitative step is (9) through (10): a weak residual for actual physical columns, a supported high-order least-squares residual with its adjoint equation, parameter control on every plane, and a single global approximate comparison compatible with the whole conic. Section2 and the boundary calculation are required to make its constants uniform over the frozen finite-regularity class. An independent reviewer should check these interfaces in their combined scope, particularly the finite-order frame cover, the projected physical constraint in H^-2, the adjoint residual pairing and global patching, and the normalized boundary-layer induction. This paragraph makes no substantiality claim. A compatible generic reduction may classify the complete theorem as technical.

The postfreeze Lin–Nakamura read cannot be backdated. The scope bytes were not changed. The development of the boundary calculation occurred after the initial symbol-remainder approach was found insufficiently justified; it closes the SAME boundary-unrestricted frozen scope, rather than replacing it with a collar assumption.

## 9. Resumption clarifications (after the user-stop interruption)

The first runner stopped at a user request, not because of a mathematical failure. The resumed runner, Factory Droid (Opus 5.5, high), checked Sections 1–8 against the frozen scope, both calculation files and the retained source372 sections. It found no step that needed a new argument. The clarifications below were added after the interruption and are disclosed here. They make implicit choices explicit; they do not change the frozen scope or any exponent or derivative count above.

(a) Bounded exterior components. R^3 minus closure Omega may have bounded components. In Section 7 the C100 extension, the narrow positive collar and the convex interpolation to a constant admissible pair are performed on EVERY exterior component. The interpolation is to a constant beyond the fixed collar, including inside bounded components. The second modified pair uses this same exterior everywhere, exactly as in the source's lem:common-extension. In Section 3 the first-medium CGO is defined on the whole ball B_5r, including such holes. The pasted field equals u1 on every exterior component, and the residual lives on all of the boundary of Omega. The physical cutoff chi equals one on a ball containing closure Omega, so the holes lie where chi=1. Sections 5–6 integrate along straight segments from outside a fixed ball, which never uses connectedness of the complement.

(b) Meaning of H^-2 in (9). The norm in (9) is the dual norm against H^2_0 test functions on the open plateau cylinder D_T x J. The residual consists of h times second derivatives of L2 amplitudes, h-small H^-1 projection errors differentiated once, the retained f(V1-Y1)Y1^-1 term, and cutoff terms of size delta exp(C/h). Each is bounded by duality against such tests. This is exactly the pairing used in transport-calculation.md (5), whose test function psi^2 chi Q_j e lies in H^2_0 of that cylinder.

(c) Supports in Section 4. Let f be supported in B_r. Choose chi supported in B_3r and the planar disks with radii 3r<s<R<T<R0, with frames on D_R0 and R0>5r as in the source. Then g_h=G_h-I and f are supported in D_s on every plane. The least-squares solution w is supported in closure D_R and vanishes on planes with |t|>r, because there f=0 and the minimum is attained at w=0. Consequently G=I whenever |x|>sqrt2 R. The least-squares problem uses only P and f, not the CGO frame or its plateau. The plateaus serve only to localize estimate (6), so patching is needed only between direction charts and their plane coordinates.

(d) Support of the dbar derivative in Section 5. For every direction, G(.,theta)-I vanishes outside the fixed ball B_(sqrt2 R). Hence the dbar derivative at fixed x vanishes there too, and its restriction to each plane is supported in D_(sqrt2 R). Estimate (5) is applied on that fixed larger disk, using frames on an even larger fixed disk. Section 2 supplies these frames uniformly, and the source's compact-support uniqueness also allows a larger support.

(e) Independence of h. G, w and e depend only on the two extended coefficient pairs and the fixed charts. Estimate (6) of transport-calculation.md therefore holds with epsilon replaced by the infimum of h+delta exp(C/h) over all admissible h. These are the h with h<=h0 and delta exp(C/h)<=1, where h0 comes from the uniform Carleman estimate of Section 2. Section 7 then chooses h=C'/log(1/d).

(f) The m=0 boundary step. The induction in boundary-calculation.md at m=0, with t_(-1)=0, already gives t0<=C[delta+N^(-1/2)] for every large N, and hence t0<=C delta. The Tan–Liu impedance algebra quoted there is an equivalent cross-check, not a needed input.

(g) Scratch sanity checks. The frozen profile ODE residual for e3, the divergence (b-1)exp(-s) and the moment 1/2^(m+1) were spot-checked numerically by the resumed runner at one admissible parameter. Nothing was retained. This is not a proof or a gate.

References: [pinned elasticity E](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026); [Tan–Liu2211.06650v1](https://arxiv.org/abs/2211.06650v1), Propositions2.2/2.3 and Theorems1.1/1.2; [Lin–Nakamura1708.00591v1](https://arxiv.org/abs/1708.00591v1), Sections2–4 at the recorded extents; [Cekic2309.09348v3](https://arxiv.org/abs/2309.09348v3), Theorem3.4 and Lemma4.1; [Ruland–Salo1708.06307v1](https://arxiv.org/abs/1708.06307v1), Proposition6.1. Exact canonical paths, Git blobs, SHA256 and semantic reading limits are retained separately.
