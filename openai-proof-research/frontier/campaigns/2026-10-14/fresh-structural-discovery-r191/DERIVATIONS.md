# r191 — prefreeze quantitative filling construction

No theorem is frozen and no author-proof nominee is submitted. These are retained deductions and feasibility calculations, with paid operations distinguished from the operation that did not close. Source315 and every operative proof at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The source, operative primary passages and selected original-history sections preceded this extended derivation. The subsequent author-hosted Clair–Whyte version and successful Lück retry were read after the short RESEARCH-NOTES entry but before this document; no frozen scope existed. Supplementary Bowditch Section 6 foundation pages, Hruska–Ruane introductory definitions, and I89/r49 original scopes were read after this draft; the comparison and reading-limit records identify them as late. They changed no claimed result or frozen scope.

## 1. The full operation investigated

Fix any finite connected aspherical integral Poincare complex of formal dimension four, allowing arbitrary orientation character. Choose the source's finite four-dimensional homotopy model Q, cell lifts, a finite generating set of Gamma=pi_1(Q), cellular incidence matrices, and chain maps and homotopies implementing local-coefficient Poincare duality. Bounds are permitted to depend on these data, including changes of model. No computable word problem or residual finiteness is assumed for the initial construction.

The direction is quantitative finite-support approximation of one-cochains by the sum of zero-coboundaries and adjoints of two-coboundaries. The sought improvement would supply, from the finite structural data, constants C>0, alpha>0, beta>=0 and R0 such that for every integer R>=R0 one can choose the finite columns V_R of Section 2 with

    delta(V_R) <= C R^(-alpha),    cost(V_R) <= C R^beta.       (1.1)

This is an investigational specification, NOT a frozen or asserted theorem. Both estimates must refer to the same columns with support in B_R. Merely taking a minimum or defining C through an unknown asymptotic is not this operation. The powers may depend on Q. The output would be quantitative cover bounds and a low-spectrum bound by the proved estimates below. No Novikov–Shubin, torsion, Atiyah, higher-dimensional or subgroup theorem is asserted.

A residual normal-tower version alone would not establish (1.1) in the full original scope. Conversely, a universal bound independent of Q is not being requested or claimed. The only family is Source315.

## 2. A concrete finite matrix approximation, with all interfaces retained

Put H_j=ell^2(Gamma)^(c_j), with the cellular orthonormal bases, and use cochain operators

    d_0:H_0 -> H_1,       d_1:H_1 -> H_2,
    A=(d_0,d_1^*):H_0 direct-sum H_2 -> H_1,
    Delta=A A*=d_0 d_0* + d_1* d_1.                           (2.1)

They are bounded matrices over the real integral group ring. The equality d_1 d_0=0 is the actual cellular relation. Write a=c_1. The source's finite-matrix comparison identifies ker A* with the first reduced harmonic space. Its vanishing of b_1^(2), together with faithfulness of the finite von Neumann trace, gives ker A*=0 as a Hilbert space. Thus closure(im A)=H_1. This inference does not require closed range or a spectral gap.

Let e_1,...,e_a be the one-cell vectors over the identity. For a tuple V=(v_1,...,v_a) of finitely supported real vectors in H_0 direct-sum H_2 put

    r_j=e_j-A v_j,
    delta(V)=sum_j ||r_j||_2^2,
    cost(V)=sum_j ||v_j||_2^2.                               (2.2)

Equivariantly extend these columns; V and E=I-A V are finite group-ring matrices. Density of im A gives finite-support V with delta as small as prescribed. First approximate each e_j by A applied to an arbitrary Hilbert vector, then approximate each such vector by finite-support rational vectors. Boundedness of A controls the resulting residual error. This gives rational certificates, but no support/norm modulus.

Let W_R be the finite-dimensional input space spanned by input cells based in B_R. Set A_R=A|W_R, with outputs represented in B_(R+s), where s is an integer propagation bound for A, enlarged to at least one. Define

    delta_R = min_(v_j in W_R) sum_j ||e_j-A_R v_j||^2.       (2.3)

If P_R is orthogonal projection onto im A_R, then

    delta_R = sum_j <(I-P_R)e_j,e_j>.

This follows by columnwise orthogonal projection, since I-P_R is idempotent. A_R is an ordinary finite matrix obtained from the actual marked ball and cellular incidence. Its minimum-norm preimages are obtained by solving the normal equations on (ker A_R)^perp. All these subspaces and projections have rational matrices; Gaussian elimination gives exact rational witnesses. The radius increases the available input space, so delta_R is nonincreasing; Section 2's density gives delta_R -> 0. No finite radius need have delta_R=0.

Let kappa_R be the cost of these minimum-norm least-squares columns. It is finite at each R; monotonicity of delta_R gives no monotonicity or useful bound for kappa_R. To optimize residual and cost together one must use the regularized problem in Section 4, rather than select unrelated optimizers for the two quantities.

This is finite-dimensional linear algebra relative to a supplied genuine marked ball. From an arbitrary finite presentation one cannot silently identify all words or certify nonidentities. No uniform word-problem algorithm is asserted. For a supplied finitely presented residually finite group, simultaneous relator-proof and finite-quotient searches decide a fixed finite list of equalities, but this additional promise is not part of the full source scope and is not a discovery result.

## 3. Exact transfer of a finite witness to a regular cover

Let N normal Gamma have finite index n and let ell(N) be the shortest word length of a nonidentity element of N. Assume

    ell(N) > 2(R+s).                                        (3.1)

If r_j is supported in B_(R+s), two distinct support elements cannot agree in Gamma/N: their difference has length at most 2(R+s). Thus quotienting preserves ||r_j||_2 exactly. Write A_N,V_N,E_N for the quotient matrices, and P_N for projection onto ker A_N*. Then

    P_N A_N=0,    P_N E_N=P_N.

For all n translates of every cell vector, projection is contractive. Summing squared norms gives

    b_1(Q_N;Q) = ||P_N||_HS^2
               <= ||E_N||_HS^2 = n delta(V).                (3.2)

The last equality uses both normality, which makes every translate have the same residual norm, and support injectivity. No approximation limit is invoked. The first equality is finite-dimensional Hodge linear algebra; rational and real Betti numbers agree. Taking V to be the exact minimizer yields b_1(Q_N)/n <= delta_R.

This certificate works for every finite regular cover satisfying (3.1), whether or not Gamma has an exhausting residual tower. It does not bound ell(N) in terms of n. A sequence with ell(N)->infinity forces residual finiteness; that fact does not identify a rate in index.

Ordinary duality requires care when returning to other degrees. If Q_N is oriented, b_3=b_1. Otherwise let Q_N^+ be its orientation double cover, of degree d=2 over Q_N (put d=1 in the oriented case). Its subgroup N intersect ker(w) is normal in Gamma, has index dn and systole at least ell(N). Rational transfer and the trivial/sign decomposition for the double cover give

    b_3(Q_N)=b^1(Q_N;Q^w) <= b_1(Q_N^+) <= dn delta_R.

Hence, with d in {1,2},

    b_1(Q_N)/n <= delta_R,   b_3(Q_N)/n <= d delta_R.

Euler characteristic then gives the paid quantitative identity

    b_2(Q_N)/n - chi(Q)
      = (b_1(Q_N)+b_3(Q_N)-1-b_4(Q_N))/n,

where b_4 is 1 if oriented and 0 otherwise. In particular its absolute value is at most (1+d)delta_R+2/n. This is not a new value or vanishing assertion for b_2^(2); chi(Q)=b_2^(2) is already in the source. These transfers are not nominees.

## 4. The exact norm-cost/spectrum calculation

Let F(t)=tr_Gamma(1_[0,t](Delta)), so F(0)=0 and F(K)=a for K>=||Delta||. For P_t=1_[0,t](Delta), write

    P_t e_j=P_t r_j+P_t A v_j.

The operator norm of P_t A is at most sqrt(t): its squared norm is the norm of P_t Delta P_t. In the direct sum of the a Hilbert columns the triangle inequality therefore gives

    sqrt(F(t)) <= sqrt(delta(V))+sqrt(t cost(V)),
    F(t) <= (sqrt(delta(V))+sqrt(t cost(V)))^2.               (4.1)

No claim about dimensions of individual vectors is used. The trace equals the sum of these a squared projected basis norms.

There is an exact optimization behind this estimate. For t>0 minimize

    I(t)=inf_V [delta(V)+t cost(V)]                           (4.2)

over arbitrary Hilbert columns, equivalently take the infimum over finite-support columns by density. For one column the strictly convex functional has the unique minimizer

    v_j(t)=A*(Delta+t)^(-1)e_j.

Indeed (A*A+t)v=A*e, and (A*A+t)^(-1)A*=A*(Delta+t)^(-1). The residual is t(Delta+t)^(-1)e_j. Summing spectral integrals proves

    delta(t)=integral t^2/(lambda+t)^2 dF(lambda),
    cost(t)=integral lambda/(lambda+t)^2 dF(lambda),
    I(t)=integral t/(lambda+t) dF(lambda).                   (4.3)

In particular F(t)<=2I(t), since t/(lambda+t)>=1/2 for 0<=lambda<=t. Also cost(t)<=a/(4t), by maximizing lambda/(lambda+t)^2. Source vanishing yields I(t)->0 by dominated convergence; it gives no speed.

The finite-support version is equally explicit: minimize (4.2) over W_R, giving v_j=(A_R*A_R+t)^(-1)A_R*e_j. For rational t>0 this is an invertible rational matrix system. Its minimum decreases to I(t) as R increases, since finite-support columns are dense. This gives convergent, finite certificates at every fixed t, with no claim of an a priori R(t).

If (1.1) were established, choose an integer R comparable to t^(-1/(alpha+beta)) for sufficiently small t. Then (4.1) would give

    F(t) <= C' t^(alpha/(alpha+beta)).                       (4.4)

This is a fully checked CONDITIONAL implication, not an assertion that its antecedent holds. Section 3 would already give power decay in ell(N). If beta=0 the exponent in (4.4) is one. Increasing beta if necessary avoids any small-R convention. A residual-only estimate without a cost estimate does not justify (4.4).

## 5. Strongest primary payment: polynomial localization and the logarithmic bound

Clair–Whyte's actual Lemma 3.2 and Propositions 3.4–3.5 provide a stronger construction than a generic qualitative appeal to Lück approximation. Let r>=1 bound propagation of Delta and let K>max(1,||Delta||) bound the quotient norms as well, as obtained from coefficient l1 norms. For any real polynomial p of degree m with p(0)=1 and p>=0 on [0,1], when mr<ell(N),

    b_1(Q_N)/n <= tr_Gamma p(Delta/K).                       (5.1)

The proof is coefficientwise: diagonal traces of a degree-m polynomial contain only group elements of length <=mr. No nonidentity kernel element contributes. Positivity then majorizes the finite harmonic projection. Their formula is

    p_(m,z)(x)=[T_m((1+z-2x)/(1-z))+1]
               /[T_m((1+z)/(1-z))+1],   0<z<1.

It satisfies 0<=p<=1 on [0,1], p(0)=1, and p(x)<=4 exp(-2m sqrt(z)) on [z,1]. The inequalities follow from |T_m|<=1 on [-1,1], monotonicity of T_m on [1,infinity), and the exact hyperbolic formula for T_m. Hence

    b_1(Q_N)/n <= F(Kz)+4a exp(-2m sqrt(z)).                 (5.2)

The exponent and normalization were checked against a rendered primary page, not guessed from extraction.

These polynomials also construct OUR finite columns. Since p(0)=1,

    q(lambda)=[1-p(lambda/K)]/lambda

is a polynomial of degree m-1. Put V=A* q(Delta). Then I-A V=p(Delta/K). Its input support is at most s+(m-1)r and its residual cost is

    delta(V)=tr_Gamma p(Delta/K)^2
             <= tr_Gamma p(Delta/K)
             <= F(Kz)+4a exp(-2m sqrt(z)).                  (5.3)

Thus the local least-squares profile cannot be described as an entirely new approximation mechanism. It includes the already paid Chebyshev construction, up to a fixed linear change of support radius. A smaller numerically observed delta_R would not constitute a full-scope theorem.

For residually finite Gamma, the integer determinant argument read in Lück's Lemma 2.8 and Theorem 2.3 gives the logarithmic spectral estimate. Applied to A* (so f*f=Delta), its normalized eigenvalue product is a nonzero integer after zero factors are removed. With a uniform norm bound, negative logarithms of eigenvalues <=lambda are bounded by positive logarithms of the others. The polynomial trace limit and right-continuity at zero transfer the bound to

    F(lambda)-F(0) <= C_Q/|log lambda|   (0<lambda<epsilon_Q).

Here F(0)=0 is supplied by Source315; determinant class or residual finiteness is not silently supplied by it. Choosing z=(log m/m)^2 for large m in (5.2) or (5.3) gives

    F(Kz) <= C'_Q/log m,   exp(-2m sqrt(z))=m^(-2).

Consequently the bound C''_Q/log ell(N) is already paid, and delta_R=O(1/log R) is paid for residual Gamma. Clair–Whyte obtains the same asymptotic with a more closely balanced log-log choice; that optimization does not change the missing operation. Their positive-spectral-exponent and spectral-gap cases are additional hypotheses, not consequences of the Singer theorem. Their nonresidual discussion has bounded systole, so it cannot supply full-scope spectral control by passing to the residual quotient: the universal cover and its spectral measure change.

The finite CW rather than simplicial convention changes no matrix calculation: only finite free cellular terms, integer incidence, bounded propagation and a finite quotient enter the above proof. This is an explicit applicability check, not a new coefficient/class substitution.

## 6. A constructive regularized truncation does not remove the gap

Let q_t=K/(K+t). The Neumann expansion is valid in operator norm:

    (Delta+t)^(-1)
       = (K+t)^(-1) sum_(j>=0) [I-(Delta+t)/(K+t)]^j.

Truncate after m terms and put V_(m,t) equal to A* times this polynomial. Its propagation is at most s+(m-1)r. The difference between its residual and the optimal residual in (4.3) has norm on each basis vector at most q_t^m: spectrally the multiplier is

    lambda/(lambda+t) [1-(lambda+t)/(K+t)]^m,

whose absolute value is <=q_t^m. Thus

    sqrt(delta(V_(m,t))) <= sqrt(delta(t))+sqrt(a) q_t^m.    (6.1)

Moreover each singular-value multiplier of V_(m,t) is sqrt(lambda)/(lambda+t) times a number in [0,1], so cost(V_(m,t))<=cost(t)<=a/(4t). This is an actual simultaneous support-and-norm construction, not just the name of an inverse operator.

For example, to make the truncation error <=epsilon, it suffices to take

    m >= log(sqrt(a)/epsilon)/log(1+t/K).

What it does not do is choose t so that delta(t)<=epsilon^2 without information on F near zero. Using the primary logarithmic bound gives at best a very large t-to-error conversion; using source vanishing alone gives existence without a controlled conversion. The polynomial optimization in Section 5 is already stronger for the support-only cover problem. Neither construction closes (1.1).

## 7. Integrating actual Poincare duality with the source correction

It would be inaccurate to say the finite-support correction in topo:cech has no construction. The given finite duality chain maps make its dependence precise.

Over k=F_2 identify compactly supported cochains with regular-module cochains as in found:ends and topo:cech. Let D map the degree-reversed cochain complex to C_*(Q-tilde;k), let E be its chain inverse, and let K be a cochain homotopy with

    Id-E D=dK+Kd.

For a finite-support degree-two cocycle omega, D omega is a finite two-cycle. Asphericity makes it a boundary: choose a finite three-chain b with partial b=D omega. Define

    eta=E b+K omega.                                        (7.1)

Then d eta=ED omega+(Id-ED)omega=omega. This exactly implements the source correction d eta=d alpha. The cap-product equivalence has finite group-ring matrices and homotopies, so let s_D,s_E,s_K bound their propagation. If h_2(R) denotes a radius in which every two-cycle supported in B_R can be filled, (7.1) gives

    supp(eta) contained in
    B_max{h_2(R+s_D)+s_E, R+s_K}.                            (7.2)

For each R, h_2(R) exists: over F_2 there are finitely many such cycles and each has a finite filling. More economically choose a basis of their finite-dimensional space and fill its members; their maximum support radius works for every cycle. Over the real numbers the same basis construction supplies a linear filling at a finite radius, with a finite operator norm depending on its chosen fillings. The signs and involution for the orientation character are retained in integral/real duality; passing to F_2 trivializes them only for the boundary-label argument.

This pays existence and a relative support formula. It does not bound h_2 or the norm of the real filling operator by a power of R from the given finite data. Nor does (7.1) apply directly to an arbitrary low-spectrum one-cochain: that vector is generally not a cocycle. Mod-two component labels record connectivity, not a real Hilbert norm estimate. Converting the correction into (1.1) must therefore control both the true filling operation and the approximate-cocycle error. A finite cap-product equivalence alone does not perform either step.

## 8. Integrating annular depth and the strongest geometric primary mechanism

The source's quantitative-looking depth comparison is exact:

    D(g_n^(-1)A,b) >= D(g_n^(-1)A,1)+D(1,b)-C_r,
    C_r=N(r/2,d_0)+N(d_0,r)+2,

uniformly for b at distance at least 3r from the limiting repeller, once the negative set is sufficiently small and its depth sufficiently large. N(a,b) counts annuli with both sides large. Finiteness of N is proved; neither a bound in word radius nor a spectral parameter is supplied. The construction chooses a countable family of finite-energy coordinates and arbitrarily small summable weights. These make square-summable edge lengths, but do not furnish lower control of rho by word distance.

The source then defines vertex depth by a MINIMUM over the whole stabilizer coset C(v). This makes every representative eligible for an edge move or for every power of the chosen parabolic stabilizer. Three fixed anchors give majority labels J_m, and one threshold M(A,Z,S) works for all deeper paths. The proof preserves this entire compatibility: we do not replace the minimum by one favorable representative, let M depend on path length, assume finite stabilizers, or infer that the block subgroup H is finitely generated.

What this proves is preservation of component labels. The actual path in a component can have unbounded length. Mesh tends to zero by excluding finitely many translated edge templates, then a Hausdorff limit is connected. There is no claimed linear bound for replacement length, no bound for a filling disc, and no lower/upper comparison between annular depth and the word-support radius of Section 2. Even an explicit M alone would not control the norms in (1.1).

The stronger primary construction was read rather than assumed missing. Hruska–Ruane's Lemma 4.1, in a proper hyperbolic space with a geometric action, replaces a path of length ell outside radius r by one of length <=lambda ell outside radius r+1. With simple connectivity it also controls the homotopy outside r-kappa, using bounded filling discs for loops of bounded length. Their Theorem 5.4 then iterates to length lambda^m L and uses a visual metric to turn radial depth into a geometric contraction factor. This yields uniform short chains and linear connectivity. The finite-orbit block graph here may have infinite stabilizers and valence, and the source never supplies that hyperbolic/visual/proper package. Applying that primary theorem as if it did would change the hypotheses.

Bowditch's primary annulus proof confirms another possible overreach. Finite-orbit annulus systems give crossratio control, and compactness of the distinct-triple quotient supplies quasidensity and hyperbolicity. The source proves convergence (properness on triples), not cocompactness on triples. Its countably many annular scales with finite-large-side property are not a finite-orbit crossratio system. Bowditch's more general construction in Section 8 is also paid; it does not create the missing all-conical/compact-triple hypothesis. No hyperbolic group or relative-hyperbolic structure is inferred for Gamma or H.

Finally, the boundary is a CONTRADICTION OBJECT constructed under b_1^(2)>0. Under the true vanishing conclusion there need not be a nondegenerate boundary of this particular construction at all. A small positive spectral window is not a positive harmonic kernel. Treating it as one would fail at the extraction of a nonzero D/D_0 class and at exact integration of a closed one-cochain. Quantitativizing this extraction, while controlling (7.2) and the all-representative path construction, is an actual missing compatibility operation, not a rejection of any source proof.

## 9. Two diagnostic controls on quantitative shortcuts

First consider the scalar derivative on the infinite line, A f(n)=f(n+1)-f(n), with input supported on vertices -R,...,R. This is a toy Hilbert-complex control, NOT a replacement PD4 example or a claimed source counterexample. Its outputs lie on edges -R-1,...,R, whose number is L=2R+2. The image consists exactly of vectors with coordinate sum zero. The residual of the target delta_0 under least squares is the constant vector 1/L. Hence

    delta_R=1/(2R+2),
    kappa_R=[(R+1)^2+2 sum_(j=1)^R j^2]/(2R+2)^2.            (9.1)

The derivative is injective on this finite input space, so the minimizer is unique. Its successive values are -j/L for j=1,...,R+1, followed by the positive values R/L,...,1/L. The cost grows asymptotically as R/6 although the residual tends to zero. Exact rational residuals and normal equations were checked for R=0,...,15. The proof is the zero-sum projection, not these finite checks. This control prevents treating density as bounded-norm solvability.

Second, abstract trace/spectral data alone cannot turn vanishing and logarithmic determinant control into a power bound. Define a probability measure on (0,exp(4)] with distribution

    F(t)=1/[log(1/t)]^2  for 0<t<=exp(-2),

no mass between exp(-2) and exp(4), and an atom of mass 3/4 at exp(4). The continuous mass is 1/4. Substitution u=log(1/t) gives

    integral_(0,exp(-2)] log(t) dF(t)=-integral_2^infinity 2/u^2 du=-1.

The atom contributes 3, so the total logarithmic integral is 2. This is the spectral measure of multiplication by t in the finite commutative von Neumann algebra L-infinity(mu). It has zero kernel, bounded norm, and positive logarithmic integral, but F(t)/t^epsilon tends to infinity for every epsilon>0. It satisfies a logarithmic upper bound and violates every positive power bound.

This does NOT realize the measure by an integral group-ring Laplacian, a group, or an aspherical PD4 complex. It rules out only a deduction using those abstract scalar conditions alone. The additional geometric input required for (1.1) is not disproved. No global impossibility or exhaustion conclusion is drawn.

## 10. Endpoint and exact unpaid operation

The strongest integrated reduction retains: an exact finite least-squares profile with rational witnesses; an exact cover certificate including the nonorientable duality accounting; the norm-cost spectral inequality and exact regularized minimization; explicit finite-propagation inverse truncations; the stronger paid Chebyshev/logarithmic construction; an actual duality-based formula for finite-support cohomological correction; and a precise comparison with the all-representative three-anchor argument and the stronger hyperbolic primary path replacement.

What remains unpaid is a construction of the SAME finite-support columns satisfying (1.1) at every sufficiently large radius for every Q in the full source class, or an equally strong closed bridge producing the desired improved quantitative output. It must handle near-harmonic real cochains, the cost of their corrections, and word-support localization. No combination carried out here supplies that bridge. Finite support at each scale, a convergent search, and the classical logarithmic rate are already paid and cannot be substituted for it.

Accordingly the endpoint is PREFREEZE/no nominee. No weakened old target, conditional theorem, source headline, finite experiment or parameter substitution is offered as a finding. No mathematical self-grade, acceptance or count is assigned.
