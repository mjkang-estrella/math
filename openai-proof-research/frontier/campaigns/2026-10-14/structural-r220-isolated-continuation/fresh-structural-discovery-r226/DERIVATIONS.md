# Source350 r226 — durable prefreeze derivations

Status: PREFREEZE, no theorem frozen or nominated yet. No grades/count. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its actual operative proofs are assumed true. Completed source-body reading before these notes: all mathematical sections and bibliographies of surface S, dimension3/4 D, and power P. Source macros/includes classified; no missing mathematical nested include. README/PDF duplicates authenticated but not used for proof coverage. Original r13 target and candidate mathematical Sections 1–10 read on direct overlap; its grades/status not read or used.

## Paid interfaces and concrete composition under consideration

S: planar logarithmic profiles allow p_j sign changes, uniformly bounded sup norms, K/(S+|B|)->0, K²||grad p||/[S(S+|B|)]->0. One-step subdivision only needs local coefficient/first derivative bounds; mean-growth persistence uses initial growth, connected compact surface and a positive low-frequency floor. Roy-Fortin small-potential local length is the final interface. Consequently fixed scalar potentials or compact coefficient classes are likely routine under the same proof; no fresh claim is made from these observations.

D3: scalar correction with denominator n²U²+|grad U|² yields b,s and div_g(b grad U)+lambda s U=0. Dividing U by a positive v with -Delta_b v+lambda b³v⁵-lambda s v=0 gives scalar metric conductivity q=bv², density d=q³. The coercive linearization is -Delta_g+4lambda. Localizing v to 1 causes only a collar determinant defect; where the clean background gradient is nonzero, its rank-two tangent projection repairs det A=d without changing flux. Trace-free tangent perturbations then make the selected eigenvalue simple while preserving the eigenfunction and volume. Each earlier sign certificate survives in its own finite-norm neighborhood.

D4: independent weighted correction -> h1,w,V0, conjugation v=w^(1/2)U -> (Delta_h1+lambda-V0)v=0. Solve Delta_h1 Z=V0 Z+lambda(Z³-Z), linearization Delta_h-2lambda. Localize Z; rank-three tangent repair yields det(A h1)=rho². No resonance issue appears. Thus applying the P power-law packets on a four-dimensional ordinary background and this repair appears compatible: it must be executed before claiming any new dimensional obstruction.

P: repeatable envelopes have ||h_k||Cj <= Cj k^[delta(j+1)], normalized transverse Hessian margin >=c k^-delta, integrated Q >= c k^gamma, with one gamma independent of all residual orders. Three transverse wells return more gradient mass than the whole parent; the intersection count is d-3. Finite phase/transport equations, jet noncancellation exponent 500 and coefficient correction loss 2129+1088R are paid. A fixed gamma persists under stage-specific finite tolerances and shrinking collars. Final S4 x S1 is a weighted-operator circle realization.

## Original-history overlap discovered before any new frozen target

Eligible original r13 candidate Sections 5–8 already replace the d-3 obstruction on a three-dimensional base by alternating near-full-mass fullification with radial corrugation. Weak preparation includes D³h control. Fullification is a frozen affine oscillation of size b(s/S)ell_A², ell_A=nu²S, with periodic second derivative positive on 1-kappa of a period. The old favorable direction lies in ker dv intersect ker dz3; the adverse quadratic contribution on normalized grad is O(nu²). Fullification retains 1-2kappa-O(nu) mass. Radial corrugation returns 1+zeta_B times its full-input parent mass and one good direction. Choosing kappa=zeta_B/[8(1+zeta_B)] and scale ratio r=nu^6 returns 1+zeta_B/2 times old parent mass. The old D³ term at the new scale is multiplied by nu^12, the fullification D³ term by nu^10. This was an independently contemplated direction but is already present in the actual original history; it is not an r226 contribution.

The r13 frozen theorem is on S3 x S1, with a fixed power-law violation. Its statement and proof remain immutable. We do not reopen or regrade it. Its three-dimensional envelope mechanism, combined with D3 ordinary-metric exactification at every finite stage rather than after the limit, must be fully carried through as the strongest compatible reduction. This combination may be routine; no nominee follows merely from reaching S3.


## Executed strongest reduction: the three-dimensional power construction

This is a prefreeze comparison calculation, not a new frozen target, a re-submission of r13, or a contribution nomination. It executes the compatible mechanisms rather than treating the dimensional label as a new operation. It uses the actual r13 Sections 5–8 construction, not any status or verdict. All canonical source mechanisms at the pin are paid.

Work on the smooth connected closed S³. Write Δ=div grad, so −Δu=λu and k=√λ. Eigenfunctions and all sign certificates are real. Use fixed coordinate Sobolev norms and a finite smooth atlas; constants below can depend on the current smooth background and the current collar. A neighborhood of the round metric in C∞ specifies finitely many seminorm constraints. There is no assertion of one frequency threshold uniform over every seminorm or over all backgrounds.

### 1. The actual repeatability input and parameter order

The original-history fullification step must precede each two-variable radial corrugation. Fix its full-input radial mass gain ζ_B>0. Then choose κ=ζ_B/[8(1+ζ_B)], choose the fullification amplitude b from the weak Hessian constants, and only then choose ν>0 small relative to b, κ and the cutoff constants. The fullification retains a fraction at least 1−2κ−Cν of gradient mass. The radial step returns at least (1+ζ_B) of the retained parent mass. Thus

    (1+ζ_B)(1−2κ−Cν) ≥ 1+ζ_B/2.

The scale ratio is r=ν⁶; gradient factors lie between fixed α>0 and β<∞. The weak third-derivative constant obeys an estimate of the form

    C_next ≤ C_flat + C ν¹² C_old + C_b ν¹⁰.

It is therefore bounded after ν is fixed sufficiently small. This is the actual missing intersection operation in a naive two-dimensional transverse radial step; it is already carried out in r13. Its loss constants do not depend on the requested WKB residual accuracy. Iterating m=floor(θ log k) generations with θ fixed sufficiently small gives a common γ>0, the normalized Hessian margin ≥c k^(−δ), the derivative bounds ||h_k||C^j≤C_j k^[δ(j+1)], and integrated oscillation weight at least c k^γ. Constants C_j may grow with j; no ultradifferentiable bound is inferred.

The arbitrary residual accuracy M and jet order J are selected after γ and all repeatability parameters are fixed. Polynomial phase/transport jets can then be taken to arbitrarily high finite order. On a three-dimensional base use three independent complex packets supplying four real first-jet directions, as in the actual r13 reduction of P's packet construction. The small-ball and mesh count in r13 is k^(352−D); taking the mesh exponent D=500 makes the bad first-jet probability tend to zero. Sign-certificate success has fixed positive probability, so these two requirements can be met simultaneously for large k. This is not a projection of a quasimode to a spectral interval.

For each fixed background g close to round, round on a clean region, and each finite M,J, the resulting real smooth U satisfies, with a positive comparison weight W,

    |∂^j U| ≤ C_j k^(2j+41) W,
    |∂^j R| ≤ C_j k^(−M) W,       R=(Δ_g+k²)U,  0≤j≤J,
    |U|+|dU|_g ≥ c k^(−500) W.

These bounds are pointwise at the same point; no derivative of W is taken. U is the exact round beam w_N=Re(x₁+ix₂)^N in a clean collar and beyond, with k²=N(N+2). The background representation A=(dv_g/dμ)g^(−1), ρ=dv_g/dμ in P's notation gives precisely its ordinary metric principal symbol; its independent-coefficient notation does not restrict the incoming ordinary metric. The preparation uses the principal metric and its fixed finite local bounds.

There are finitely many disjoint certificate cylinders in coordinate balls, with opposite strict signs on their two transverse two-dimensional disks and total projected disk area at least c_g k^(1+γ). The constants can depend on g and the stage. Arbitrary small positive amplitude of a certificate is allowed; it merely reduces the later persistence neighborhood. No new nodal components or domains are counted from this statement.

### 2. Scalar weighted correction with an explicit finite derivative budget

Use D=U²+|∇U|² rather than the n²U²+|∇U|² of D3. Put

    b=1−RU/D,
    s=1−k^(−2)[RU/D−div_g((R/D)∇U)].

Then a direct product-rule calculation gives

    div_g(b∇U)+k²sU
      = R−div_g((RU/D)∇U)−RU²/D+U div_g((R/D)∇U)
      = R−(R/D)(|∇U|²+U²)=0.

The denominator is ≥c k^(−1000)W². At derivative order j,

    |∂^j D| ≤ C_j k^(2j+86)W²,
    |∂^j(D^(−1))| ≤ C_j k^(1000+1088j)W^(−2).

For the second estimate, a term with l differentiated D factors has exponent
1000(l+1)+2j+86l = 1000+2j+1086l ≤ 1000+1088j.
The coordinate derivatives of the fixed background only alter C_j. Hence

    ||b−1||C^q + ||s−1||C^q ≤ C_q k^(−M+2129+1088q).

In particular any prescribed finite coefficient tolerance η can be achieved by first fixing q and a desired power k^(−T), then choosing M>2129+1088q+T+1, and finally choosing k large. Positivity b,s>0 follows when η is small. On every open set where R=0, b=s=1 exactly. All supports are consequently controlled by the residual support.

### 3. Ordinary metric realization in dimension three

Let Δ_b=div_g(b∇). Seek v>0 near 1 solving

    −Δ_b v+k² b³v⁵−k²s v=0.                         (E)

This is the paid D3 semilinear step, now with the explicit polynomial coefficient budget above. For clarity, a conservative sufficient estimate can also be seen directly. Put v=1+w, L=−Δ_g+4k². On fixed spectral Sobolev norms, L^(−1):H^(ell−2)→H^ell is bounded independently of k≥1. With ell≥4 and the finite coefficient C^ell bounds η, the fixed-point right side has norm at w=0 at most C k²η. On a ball of radius C' k²η, its Lipschitz constant is at most C(η+k²η+k⁴η). Thus η≤c k^(−4) suffices, and

    ||v−1||H^ell ≤ C k²η.

Choose ell>p+2+3/2 to control C^(p+2). In particular v>1/2 for small η. These are stagewise constants; no unproved spectral gap at the target eigenvalue is used in (E). The positive shift 4k² is coercive.

For u=U/v and q=bv², the identity

    div_g(q∇u)=v div_g(b∇U)−U Δ_bv

gives div_g(q∇u)+k²d u=0 with

    d=sv²+k^(−2)v Δ_bv=b³v⁶=q³.

If A is a positive g-selfadjoint conductivity and d=det_g A, the metric

    g_A(X,Y)=g(d A^(−1)X,Y)

has volume d dv_g and Laplacian d^(−1)div_g(A∇). Thus the scalar choice A=qI already gives an ordinary metric wherever (E) is used without a cutoff.

The global semilinear solve need not be supported where the residual is supported. This is why the collar repair, rather than the unlocalized scalar construction alone, is essential. Choose χ=1 on the support of b−1,s−1 and χ=0 before a clean round collar ends. Set ṽ=1+χ(v−1), u=U/ṽ, q=bṽ², and

    d=sṽ²+k^(−2)ṽ Δ_bṽ.

The same flux identity holds everywhere. Away from the transition collar d=q³. On the transition collar U=w_N and the old metric is round. With r=√(x₁²+x₂²),

    |∇w_N|²=N²(r^(2N−2)−w_N²)
              ≥N²r^(2N−2)(1−r²).

The collar has r bounded away from 0 and 1. For η small, the normalized vector
∇u/(N r^N) has a uniform positive lower bound, and its derivatives of order p have at most fixed polynomial growth in k. This follows by writing

    ∇u/(N r^N) = ṽ^(−1) ∇w_N/(N r^N)
                  − [w_N/(N r^N)] ṽ^(−2)∇ṽ;

both normalized beam expressions and their derivatives are bounded polynomially. No division by an exponentially small unnormalized gradient is left unaccounted for.

Let Π be the g-orthogonal rank-two projection onto (∇u)⊥ in that collar and put

    A=q[I+(sqrt(d/q³)−1)Π].

Then A∇u=q∇u and det_g A=q³(d/q³)=d. Its eigenvalues are q along ∇u and q sqrt(d/q³) in the two transverse directions, all positive. Define it to be qI off the collar, where the defect vanishes in open overlap neighborhoods. The resulting smooth g_A satisfies −Δ_(g_A)u=k²u exactly and is the original round metric outside the enlarged correction region. All signs of U are preserved because ṽ>0.

A conservative estimate is

    ||g_A−g||C^p ≤ C_(g,collar,p) k^(2p+4) η,

after taking ell≥p+6. Any larger finite polynomial bound would suffice as well. Choose η=k^(−T) with T>2p+4 plus the requested decay, and then M as in §2. The order of choices does not shrink γ. There is no uniform-in-p claim here.

### 4. Round collars, simplicity and finite persistence

Use t=1−r² and decreasing clean-region thresholds a_j→1/4, all below 1/2. At a step, leave room for ordered collars

    a_j < splitting collar < cutoff collar < a_(j−1).

The incoming metric is round below a_(j−1). Wave gluing and scalar residual correction start beyond the cutoff collar; χ transitions where U is exactly the beam. The final determinant repair is supported in this clean region. Afterwards the D3 pinned splitting perturbation is supported in the separately reserved splitting collar and leaves the metric round below a_j. All collars have positive width at their own finite stage; constants may diverge as j→∞ and are absorbed by later choices of M and k.

The selected eigenvalue can be made simple by the actual D3 trace-free tangent conductivity construction. It preserves u and the volume exactly while perturbing the rest of its finite eigenspace. The required local independence is available on the round collar: if another eigenfunction z has dz tangent-annihilated everywhere, locally z=F(w_N), and

    F''(w_N)|∇w_N|²+k²(F(w_N)−w_N F'(w_N))=0.

For N≥2, |∇w_N|² varies on fixed-w_N leaves because of r^(2N−2). Therefore F''=0 and F is a multiple of w_N; unique continuation gives the same globally. The nondegenerate finite-dimensional splitting argument is the paid D3 argument, not an invocation of an unread genericity theorem. Choose its parameter small enough for every prescribed C^p tolerance. This step does not alter the certificate signs.

A simple isolated real eigenpair has a continuous real normalized branch in a sufficiently small finite-norm metric neighborhood, with sign fixed at a chosen nonzero point. Elliptic regularity gives the C⁰ continuity needed on the finitely many compact certificate disks. Strict opposite signs persist. Each cylinder projects onto its transverse disk from the zero set by the intermediate value theorem on every fiber segment. A Lipschitz projection therefore bounds the H² measure of that zero set below by a fixed multiple of disk area. The cylinders are disjoint, so the areas add without multiplicity or overlap. This applies to the full zero set; neither regularity of every zero nor a count of embedded nodal components is asserted.

### 5. A single smooth limiting metric, and the unchanged exponent

At step j take a finite derivative order p_j≥j (also covering the finitely many prescribed seminorms of the initial neighborhood). The three-dimensional one-step construction above is available with arbitrarily small C^(p_j) perturbation. Let ε_i>0 be a C^(s_i) neighborhood in which the i-th simple branch and its certificate persist. Require each later perturbation, in all previously required orders, to be smaller than

    2^(−j) and ε_i 2^(−(j−i+2)),  for every i<j.

Include an additional strict reserve in ε_i. Then the tails stay inside every earlier branch neighborhood. Each fixed derivative norm has a summable tail, so the metrics converge in C∞ to one positive-definite metric g∞. Positive definiteness follows from the initial C⁰ neighborhood and a total C⁰ budget. The limit remains in the prescribed round neighborhood. It is round on the common region t<1/4. No gluing across an uncontrolled accumulation point is left: C∞ convergence on the compact manifold supplies smoothness there.

Choose N_j, hence k_j, after the current finite constants are known, with k_j²>4k_(j−1)² and

    c'_j k_j^(γ/2) > j.

The c'_j include the certificate persistence and volume comparison constants. Let ε=γ/4. At the limit, the i-th branch is an exact eigenfunction of g∞, its eigenvalue λ_i lies in (k_i²/2,2k_i²), and

    H²_(g∞)({u_i=0}) / λ_i^(1/2+ε)
       ≥ c'_i k_i^(γ−2ε) = c'_i k_i^(γ/2) > i.

Take each real eigenfunction L²(g∞)-normalized by a positive scalar. This changes no zeros. The frequency sequence is only a subsequence; no density, all-frequency lower bound, arbitrary power, or Gevrey estimate follows. Earlier stage eigenfunctions need not remain literally the same functions under later perturbations. Their exact simple branches at the final common metric are what persist.

This closes the compatibility calculation at the level of the cited paid and original-history lemmas. The steps beyond r13's envelope are scalar residual division, the paid D3 coercive solve and collar repair, paid pinned simplicity, and an ordinary summable neighborhood diagonal. The dimensional improvement does not itself identify a nonroutine operation. Accordingly this calculation is retained as a strongest-reduction comparison, not nominated or assigned a mathematical grade.


## Stronger family constructions executed before identifying a remaining gap

A genuine family is not automatically a new operation. The following constructions dispose of several tempting versions of that claim. They are comparison derivations, not frozen r226 targets.

### 6. Finite families and a compact Cantor family on S³

The one-step bounds above are required only to arbitrary finite precision. For finitely many backgrounds, take the largest of their finitely many thresholds and choose one common integer N at the step. Construct their waves separately, with the same exponent γ. The residual accuracies and finite tolerance budgets may differ. Thus a finite family is not an unpaid parametric problem.

There is also a concrete infinite compact family. Start in any prescribed sufficiently small C∞ neighborhood of the round metric. At each binary-tree vertex keep a small neighborhood of a smooth metric round below the current threshold a_j. Store the finitely many strict sign certificates and the simple isolated branch neighborhoods of its ancestors. Within this neighborhood, make two arbitrarily small smooth perturbations supported in the core, leaving the round collar unchanged. They can have distinct volumes: for e^(2tf)g with nonnegative nonzero smooth f supported in the core,

    (d/dt) Vol(e^(2tf)g)|_(t=0)=3∫ f dv_g >0.

Choose disjoint open intervals around those two volumes, with closures inside the parent's volume interval when there is one. The metric perturbations can be as small in every currently prescribed finite norm as needed. The strict inequalities and finite eigenbranch data remain valid.

At level j there are only 2^j backgrounds. Apply the one-step construction to each, with a common sufficiently large N_j. Shrink each construction's tolerance so that the resulting metric remains in its chosen volume interval and all ancestor branch neighborhoods. Take the common N_j large enough that every new certificate gives the ratio >j at exponent ε=γ/4 after the reserved persistence loss; also require the new spectral window to lie above all preceding windows. Around the resulting metrics choose small neighborhoods whose closures retain these properties. Each child's future C^p perturbation budget is summable in every p already required, at most 2^(−j) in a fixed complete metric for C∞ convergence. Increase the controlled derivative order at least to j. There are only finitely many constraints at each vertex, so the arbitrary finite precision of the one-step operation meets them.

Every infinite binary path then converges to a smooth positive-definite metric. Every finite prefix's certificate survives in the limit. The common γ was fixed before the accuracy choices, and the finitely many constants at a level were absorbed in the common N_j. The map from the compact binary sequence space to smooth metrics is continuous: paths sharing a length-j prefix have tails tending to zero in each fixed seminorm. It is injective and its images are pairwise nonisometric, because paths separating at a vertex remain in disjoint closed volume intervals. Compactness of the parameter space gives a compact metric family. Each member has a sequence of exact real eigenfunctions in the common disjoint frequency windows and ratios tending to infinity, uniformly by level.

This argument gives no smooth interval of metrics and no common selected eigenfunction over the Cantor set. It requires neither a parameterwise Gaussian choice nor simplicity simultaneously along an interval. It is a branching use of the paid one-step and open persistence operations, not a contribution candidate. In particular, merely asking for uncountably many nonisometric metrics or a compact family does not isolate an unpaid operation.

### 7. A smooth, non-product, nonisometric family with all eigenfunctions preserved

There is an even stronger elementary alternative when an extra circle is allowed. Take any one of the fixed ordinary metrics g on S³ produced in §§1–5, together with its real normalized eigenfunctions u_j. Let φ be the coordinate on R/(2πZ), and choose a smooth real one-form α on S³ with dα≠0. Such a form exists with support in one coordinate ball: extend χ x₁ dx₂ by zero, where χ is identically 1 on a smaller ball. For a parameter s in a fixed compact interval [0,s₀], set

    G_s = g + (dφ+sα)²  on S³×S¹.

This is positive-definite for every s, smooth in x and s, and the manifold is connected and closed. In block coordinates its matrix, inverse and volume are

    G_s = [[g_ij+s²α_iα_j, sα_i], [sα_j,1]],
    G_s^(−1) = [[g^ij,−sα^i], [−sα^j,1+s²|α|²]],
    dv_(G_s)=dv_g dφ.

Consequently, for every smooth f independent of φ,

    Δ_(G_s) f
      = (det g)^(−1/2)∂_i[(det g)^(1/2)g^ij∂_j f]
        + (det g)^(−1/2)∂_φ[−s(det g)^(1/2)α^j∂_j f]
      = Δ_g f.

Thus (2π)^(−1/2)u_j, pulled back to S³×S¹, is an L²(G_s)-normalized exact real eigenfunction with the same eigenvalue λ_j for EVERY s. This statement concerns an invariant subspace of the Laplacian; it does not say that the full spectrum or its multiplicities is independent of s.

The nodal lower bound needs no unjustified assertion about regular nodal components. Lift each disjoint base sign cylinder through a fixed fiber interval I of positive length. Projection onto the base transverse disk times I covers that product from the zero set, by the same fiberwise sign argument. On the compact s interval and compact manifold, these coordinate projections have one finite Lipschitz constant, since G_s are uniformly equivalent to g+dφ². Hence the sum of H³ lower bounds is at least a fixed positive constant times the sum of the base disk areas. It follows that

    inf_(0≤s≤s₀) H³_(G_s)({u_j=0}) / λ_j^(1/2+ε) →∞.

No claim about nodal domains, the regularity of every zero, or equality of the entire Hausdorff measures is needed for this conclusion. At regular hypersurface points the induced block determinant also shows the familiar fiber-volume identity, but the certificate proof suffices for the full zero set.

The family is genuinely nonisometric, and this must be checked rather than inferred from a free-looking connection parameter. Here is a direct curvature calculation. Let e_i be a local orthonormal frame for g, E_i its horizontal lift, and V=∂_φ. At a base normal-frame point,

    [E_i,E_j]=[e_i,e_j]^H−s F_ij V,   [E_i,V]=0,  F=dα.

Koszul's formula gives

    ∇_(E_i)E_j=(∇^g_(e_i)e_j)^H−(s/2)F_ij V,
    ∇_(E_i)V=∇_V E_i=(s/2)∑_j F_ij E_j,
    ∇_V V=0.

Substituting these expressions into curvature yields

    K_(G_s)(E_i,E_j)=K_g(e_i,e_j)−(3s²/4)F_ij²,
    K_(G_s)(E_i,V)=(s²/4)∑_j F_ij².

Tracing both horizontal and vertical planes gives, with the explicitly specified full ordered-index sum,

    Scal_(G_s)=Scal_g−(s²/4)∑_(i,j) F_ij².

This agrees with the scalar trace (1.15) in the actually read Muto 1977 §1; its original O'Neill antecedent was not accessible in the bounded attempts recorded separately. In particular,

    ∫ Scal_(G_s) dv_(G_s)
       =2π∫ Scal_g dv_g −(πs²/2)∫∑_(i,j) F_ij² dv_g.

The last coefficient is strictly positive. For distinct nonnegative s these integrated scalar curvatures differ, whereas all volumes equal 2πVol(g). Isometries preserve that integral, so the metrics are pairwise nonisometric. This is not a disguised gauge family α=df, which would be removed by changing φ. As s₀→0 the family lies in any prescribed neighborhood of the product metric in every specified finite collection of smooth seminorms.

This construction has common exact modes, a nontrivial smooth parameter, equal total volumes, a non-product horizontal distribution for s>0, and a uniform positive power lower bound. Its new ingredient beyond the source and §§1–5 is the classical circle-connection calculation explicitly performed here. It therefore does not supply an identifiable nonroutine operation. It is retained to prevent an overbroad claim that genuine uniform metric families themselves are an untouched gap. It is not a re-submission of the original r13 S³×S¹ target.

### 8. Why the same argument does not yet give an intrinsic smooth S³ family

The preceding two family constructions do not solve the narrower, positive-dimensional same-dimension problem. One tempting attempt is to deform only the common clean round patch and to preserve all round beams w_N. This misses an important quantifier. At its creation stage the selected u_j is exactly a beam there, but later metric perturbations preserve only its nearby simple branch, not its exact function or Cauchy data. At the final g∞ the earlier eigenfunctions are not asserted to equal their creation-stage beams on that patch. Therefore a deformation preserving every round w_N need not preserve the final counterexample eigenfunctions. This is a compatibility failure of that proposed inference, not an impossibility result.

A more elementary vertical-deformation variant also overstates its freedom. In round coordinates (r,θ,ψ),

    g_round=dr²/(1−r²)+r²dθ²+(1−r²)dψ².

Changing only the final factor to q²(1−r²)dψ² leaves a drift ∇log q·∇f in the Laplacian on functions of (r,θ). Preserving all those functions requires q to be independent of (r,θ). A periodic q(ψ) with the same total circle length is only a circle reparametrization. Changing the total length is incompatible with smooth collapse at r=1 unless the circle's smoothness normalization is also addressed. Thus this particular purported free family does not produce a localized nonisometric ordinary-metric family.

The strongest direct remaining route would be a parameter-dependent one-step construction for a compact interval of genuinely varying three-dimensional backgrounds. The elliptic part itself causes no resonance: if b_a,s_a and the background depend smoothly on a and satisfy uniform finite bounds, the operators −Δ_(g_a)+4k² have uniform coercive inverses. The parameter-dependent implicit-function theorem then supplies v_a; positivity, determinant repair, derivative estimates in x and a, and collar support all persist with uniform finite constants. Those parts are already compatible paid operations.

The unresolved input is the simultaneous real wave selection and pinned spectral persistence with the required uniform power gain. For a single three-dimensional manifold the random real first jet has four coordinates, while the spatial net has three dimensions; this is the surplus used in r13's noncancellation probability. Adding a continuous parameter produces a four-dimensional (x,a) net. Merely increasing the net exponent D no longer makes the same small-ball union estimate decay: the k^(−4D) probability and k^(4D) count cancel, before their fixed polynomial losses. This calculation is a limitation of that proof, not a theorem that another selection cannot work.

Critical zero events cannot simply be accepted and divided through. If U=0 and d_xU=0, the exact equation forces

    g^(−1):D²_xU=0.

At such a point a nonzero definite Hessian is incompatible with every positive-definite metric. Indefinite critical zeros can be compatible, but require an actual smooth local realization and matching argument; the scalar first-jet denominator in §2 vanishes there. The two alternatives to establish are a smooth global parameter selection avoiding the forbidden critical-zero events with uniform quantitative bounds, or a new relative exactification across controlled compatible critical zeros. Neither is supplied by a fixed-parameter Gaussian draw, a spectral projection, or the already closed coercive step.

Finally, simplicity at one parameter value is an open finite-parameter fact, not automatic along an entire interval at all infinitely many stages. A uniform pinned splitting/branch construction would have to be proved at that scope, or replaced by an explicit full-eigenspace persistence argument. Finite covers alone do not glue chosen eigenfunctions or their phases at overlaps. These are precise remaining obligations for an unfrozen direction; no theorem at this scope has been frozen or claimed.

## Regularity and dimensional compatibility limits

The executed diagonal chooses arbitrarily strong finite norms at successive stages. It does not control the dependence on derivative order, hence supplies no fixed Gevrey or moderate-growth Denjoy–Carleman norm. This matters mathematically, not merely administratively. The actually read Hezari v1 proof yields H^(d−1)(Z_u)≤C λ^(s/2) for a fixed G^s metric. A metric with H^(d−1)(Z_(u_j))/λ_j^(1/2+ε)→∞ therefore cannot belong to G^s for s≤1+2ε. The equality endpoint is excluded too. More generally its moderate-growth weight bound is C√λ (M_floor(√λ))^[1/floor(√λ)]; along a power-violating sequence that weight factor divided by λ^ε must be unbounded. This is only a subsequence restriction. It does not supply lower derivative bounds at every order or an optimally regular counterexample. These conclusions are routine upper/lower comparisons and are not nominations.

The scalar exactification also reveals a genuine dimensional compatibility condition without a new theorem. In dimension d>2, scalar conductivity qI has density q^[d/(d−2)]. The corresponding positive-factor equation is

    −Δ_bv+λ b^[d/(d−2)]v^[(d+2)/(d−2)]−λs v=0,

whose linearization at b=s=v=1 is −Δ+4λ/(d−2). A transverse rank-(d−1) repair uses multiplier

    τ=(density^(d−2)/q^d)^[1/(d−1)].

In dimension two, an ordinary metric conductivity has determinant exactly 1, independently of its volume density. Thus qI can be such a conductivity only when q=1. There is no free continuation of the positive-power exactification formula through d=2. The supplied sharp surface bound, which is assumed true, cannot be bypassed by the higher-dimensional scalar rewrite. This calculation is a compatibility check, not a new surface result.

## Present disposition of the research, without mathematical grades

PREFREEZE / no nominee. No new full-scope statement was frozen. The retained strongest reduction reaches the three-dimensional power consequence using available constructions, and the finite, Cantor and circle-connection families above likewise leave no identified nonroutine operation. The intrinsic smooth three-dimensional parameter-family direction remains unproved at the simultaneous wave-selection and spectral-persistence interfaces described in §8. No negative, exhaustion, worldwide novelty, correctness, contribution, acceptance or count claim is made. Parent review is separate.
