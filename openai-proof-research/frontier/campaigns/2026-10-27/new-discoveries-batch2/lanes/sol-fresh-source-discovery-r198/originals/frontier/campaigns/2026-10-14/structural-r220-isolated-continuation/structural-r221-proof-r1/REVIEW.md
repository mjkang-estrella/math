# Independent Structural221 correctness review, round 1

**Proposed correctness verdict for parent adoption: PASS, at the entire unchanged frozen statement and submitted-proof scope, relative to the stipulated premises.** This is not acceptance, a contribution verdict, or a campaign count. No essential repair, extra hypothesis, restriction, replacement theorem, or unresolved essential verification is needed. Several compressed steps require explanation; the explanations below are consequences of the submitted text and its expressly invoked source interfaces, not changes to the submission.

Reviewer provenance: authorized Codex / GPT-6 Astra / xhigh / default. All review work is confined to `structural-r220-isolated-continuation/structural-r221-proof-r1/`. No parent assessment, contribution review, peer result, task registry, or foreign body was consulted. The wrapper is an isolation prefix, not reuse of a closed theorem.

## Object, authentication, and dependency boundary

The reviewed statement is the 3402-byte `FROZEN.md`, SHA256 `0031fe7106971855b2c1b98e3e1bc40574ed249ad8b17e9ac028d1f30bfae1ce`. The reviewed `PROOF.md` has SHA256 `deae6858c76a031fe0a49c6908647ca8a3f0bacf4821dae087919bbd25c9c8db`. All public original prose, including DERIVATIONS, COMPARISON, FINAL and the outside REPORT, and the exact private READING-LIMITS were read. The admitted author's 57 manifest-selected files plus its three outside files were authenticated, including their modes and exact directory selection, before mathematical reliance. The author's inspected verifier passed with all three supplied detached anchors. An independent baseline includes all 60 files and all 8 directories. All 17 canonical blobs were independently checked against the complete, correctly hashed, 13223-entry pinned tree, including Git blob SHA1 and byte count. Hashing is not counted as semantic reading.

The premises are Source345 and all its operative upstream proofs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, stipulated true. I do not reassess their truth. I check that the new applications use their actual hypotheses, constants, degree ranges, maps, coefficients and filtrations. In particular I do not replace the native cut by a different coproduct, and do not infer anything from a geodesic-counting theorem alone.

Exact canonical source prefix: `preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026/`, at that pin. In the citations below, source filenames are relative to its `build/` directory; line numbers use the authenticated TeX bytes. The decisive interfaces actually read are:

- `sections/setup.tex`, lines 1–69: strong H1, period one, E equal to the integral of squared speed, F equal to sqrt(E), open length and F sublevels, F2 coefficients.
- `sections/shortening.tex`, lines 1–393: `lem:arclength`, `lem:shortening-recipes`, `lem:shortening-block`, `lem:shortening-family`, `lem:shortening-bounded`, `prop:fixed-degree-death`, including their actual constructions.
- `sections/cutjoin.tex`, lines 1–615, and `figures/native-cut.tex`, lines 1–40: `prop:sphere-powers`; `eq:cj-thresholds`; `lem:cj-small-chains`; `lem:cj-operations`; `thm:filtered-interchange`; `lem:cj-public-comparison`; `prop:absolute-unit`.
- `sections/ordinary.tex`, lines 1–159: `thm:ordinary-death` and its full proof, including the empty-cut case, two finite fillings, delayed radius choice, arclength prism, and constants-relative chain projection.
- `sections/local.tex`, lines 1–182 and 298–393: `lem:local-analytic`, `lem:local-strips`, `lem:local-polygons`, `lem:local-lens`, with the interfaces used by the round attachment.
- `sections/equivariant.tex`, lines 197–355: `eqv:round-attachment`, the Hessian and negative-rank calculation, and critical-manifold calculations. The introduction was also read completely; the driver include order was inspected.

Primary references actually read, with exact byte extents in the private reading record, are HR v2, sections 3–7; BMW v2, sections 4–5; HW v4, section 1, sections 2.1–2.4 with their adjacent section introduction, and Remark 4.14; CHO v3, section 8 introduction and sections 8.1–8.2; NR's 2012 section 8; COS v1, sections 5–6; and Shelukhin v2, sections 3.1–3.2. HR equation (19) and the round filtration diagram were also visually checked in the authenticated PDF. Precise limits, failures, masks, accidental exposures and truncation recovery are in `private/READING-ACCESS-LIMITS.md`.

## 1. C0 compactness, strong-H1 continuity, and uniform shortening

The tensor box in PROOF 1 is justified. A C0-continuous family of smooth positive definite tensors on compact P gives a continuous positive quadratic form on the compact h-unit tangent bundle over P. Its minimum and maximum yield positive u and finite v with u²h ≤ g_t ≤ v²h. This gives both length and square-root-energy comparisons. Compactness of the parameter space, including a disconnected or nonpure finite polyhedron, is enough; no derivative bounds follow or are needed.

For joint energy continuity, take t_i→t and gamma_i→gamma strongly in H1 in an ambient embedding. Uniform convergence of gamma_i follows from the one-dimensional Sobolev embedding. The fixed smooth tensor g_t evaluated along gamma_i converges uniformly to its value along gamma; its velocity quadratic integrals therefore converge under strong L2 convergence. The additional error from replacing g_t by g_(t_i) is bounded by a constant times the C0 tensor difference times the bounded squared H1 velocity norm. Taking square roots preserves continuity, also at zero. Thus all Y_a are open in the stated topology. This does not assert smooth parameter dependence or a family of gradient flows.

The important uniformity question is whether the h-recipes can be used on pieces normalized by g, rather than only on h-unit pieces. They can. After the paid g-arclength normalization, each rescaled piece has g-Lipschitz constant at most 1, hence h-Lipschitz constant at most 1/u. The h-spokes, with fixed-thirds endpoint connectors in the source construction, have h-length at most D_h and h-Lipschitz constant at most 3D_h. Retiming the active spoke and piece to halves therefore puts both compared paths in the exact path-pair class of `lem:shortening-recipes` for

    L_0 = 2 max{1/u, 3D_h}.

That lemma bounds the h-length of every intermediate path by K(h,L_0), not merely the final path. Consequently every active recipe has g-length at most vK(h,L_0). Retimings have g-length at most vD_h+1. The unchanged suffix consists of original g-pieces. Hence D=vD_h and C=max{vK,D+1} bound every block homotopy by original g-length+C and its final block by D, independently of the number of pieces. Positive time intervals for all nonconstant pieces are exactly what the source uses for strong-H1 continuity; a uniform energy bound during these length homotopies is neither asserted nor used.

The displayed B_j satisfies B_j/2=D+jC+3>D+jC+2. For a≥a_j, floor(a/B_j) is at least j+2, thus at least j+1, and a>2((j+1)C+1). The two source terminal estimates therefore apply: a long loop saves at least B_j/2 from the fully shortened block, while a loop with L<a/2 remains below a-1 by the rough estimate. At most j+1 different blocks change at any parameter point. Their costs add within one stage to H_j=(j+1)C, but the successive stage peaks are a-r+H_j and do not add over r.

Arbitrary finite singular cycles cause no hidden bound on chain size or degree: `prop:fixed-degree-death`, lines 358–371, supplies precisely the finite-polyhedron representation by face pairing and subdivisions, with parameter dimension at most j and image-preserving comparison prisms. Each cycle uses finitely many shortening iterations. Constants may depend on j here; they will be used over only a fixed finite degree range later.

At the terminal level, the globally null cycle lies in A_(b_j)(g), hence A_(b_j/u)(h). Its global nullness is unchanged because the underlying strong-H1 loop space is the same. The reference fixed-degree theorem fills it at h-length <b_j/u+d_j(h), giving g-length <v(b_j/u+d_j(h)). Thus formula (3), which is strictly larger than this entire final level and H_j, is an additive increment for every positive starting level. If that starting cut is already at or below b_j, the same reference argument applies directly. There is no low-cut failure. Only the fixed h construction uses h-injectivity radius; no common g-injectivity radius or curvature bound enters.

**Finding:** the uniform fixed-degree argument is valid at the claimed regularity, including all intermediate homotopies, low cuts and every finite chain degree.

## 2. HR algebra, all classes, bounded resonance, and lambda

The relevant actual primary is Hingston–Rademacher, *Resonance for loop homology of spheres*, [arXiv:1105.0783v2](https://arxiv.org/pdf/1105.0783v2): Lemma 3.1, Lemma 4.2, Lemmas 5.3–5.5, equations (10)–(20), and the section 6 product/BV calculations. This is stronger than merely knowing an asymptotic resonance slope.

Over F2 for every n>2, the product algebra has basis U^r and AU^r, with product unit E=U^0 of ordinary degree n, ordinary degrees |U^r|=n+r(n-1), |AU^r|=r(n-1), and A²=0. HR equations (21)–(22), the Gysin/Pontryagin proof of (22), and Theta=U² cover both parities. For odd n the integral free algebra reduces to this mod-two algebra; the even case is computed directly over F2. Since d=n-1≥2, the residues 0 and 1 modulo d are distinct. Every degree has rank at most one, so there are no omitted homogeneous linear combinations over F2. The n=3 exception in the BV proof is expressly handled in HR section 6 using the round level, rather than the dimension-vanishing argument used for n>3.

For high classes Lemma 5.4 gives a fixed finite Q, |Y|≤3n-2, and z=Y Theta^m. One may see the finite remainders directly as AU, AU², U, U²; the constants and any small exponents are a finite exception set. The exception cutoff is algebraic, not metric dependent. HR (19) says exactly

    (m-2)mu ≤ cr_g(Y Theta^m) ≤ (m+2)mu+cr_g(Y).

The bar on mu in the PDF denotes the common slope, not a distinct variable. This displayed inequality was visually verified. To track normalization, put c_m=cr(Theta^m) and b_m=cr(omega^m). Product subadditivity and cohomology superadditivity give the two Fekete slopes. The BV/duality interleaving in (18), c_(m-1)≤b_(m+1), together with the reverse slope inequality from (16), makes these slopes equal. For admissible m the same interleaving gives c_m≤b_(m+2)≤(m+2)mu and b_m≥c_(m-2)≥(m-2)mu; (16) then gives (19). Small m are covered by the stated finite enlargement.

Because |Theta^m|=n+2md, the reciprocal global mean frequency is mu/(2d). Thus the frozen limit with denominator 2m(n-1), rather than |Theta^m|, has exactly the same normalization. Positivity and finiteness follow from the paid sphere resonance/power interface and HR's positive global mean frequency. Comparing the same fixed topological power classes yields u mu_h≤mu_g≤v mu_h. For each Y, cr_g(Y)≤v cr_h(Y). Subtracting |z|lambda_g from (19) gives an absolute error bounded, for example, by

    2v mu_h + v C_Q + (3n-2)v lambda_h.

This is uniform in g and m. Each exceptional nonzero class is bounded by v(cr_h(z)+|z|lambda_h); there are finitely many such classes, and their reference critical levels are finite because singular representatives have compact image. Consequently the specified R_box works for every nonzero homogeneous class, not just powers or selected degrees.

Cohomological critical levels agree with their dual homological ones in rank one. Independently, over a field the restriction of a dual class to X_s vanishes exactly when the image of H_q(X_s) in the one-dimensional global H_q is zero, by the natural universal-coefficient pairing. This proves equality of the relevant critical thresholds without any unsupported higher-rank duality. Constants in degrees 0 and n have critical level zero and are in the finite enlargement. For degrees above n+1 the pair with constants is canonically identified with absolute (co)homology, precisely the range used for T.

With lambda_g≥u lambda_h, dividing R_box by u lambda_h gives a common dimensionless C_H satisfying the source convention |q-alpha_g cr|≤C_H. Positivity of lambda makes this division legitimate.

For g' C0-close to g, the inequalities (1-epsilon)F_g≤F_g'≤(1+epsilon)F_g hold for arbitrarily small positive epsilon. They compare every critical level through actual sublevel inclusions. Passing to the fixed-power limit proves continuity of lambda. Compact P then gives 0<lambda_-≤lambda_+<infinity. This is a C0 proof; it does not silently import the stronger metric topology appearing in HR's original continuity statement.

**Finding:** all algebraic parity, degree, coefficient and normalization checks pass. Admissibility does constrain R: the degree-n constant fundamental class forces R≥n lambda_+. The theorem never claims these parameters are freely or independently small.

## 3. Uniform cut/join, J, radius choices, D_0 and normalization

Use the actual thresholds in `eq:cj-thresholds`, not an abstract coproduct estimate. For j≥J set m=floor((j-2)/(2d)), q=2md, p'=q-d. Choosing p'>C_H+2/(u lambda_h) gives L=(p'-C_H)lambda_g-2>0 for every g in the box. Requiring p'>n+1 gives the absolute/relative identification needed for the cohomology class T. A single finite J suffices since p' tends to infinity with j.

The source degree conditions also hold:

    2 ≤ r=j-q ≤ 2n-1,
    j ≥ q+2 > q+1=n+p',
    N=|S|=n+q > q+1=n+p'.

Thus both hypotheses of `thm:filtered-interchange` are met. J>2n ensures that r and n belong to the maximum d_* over degrees below J. The length gap is exactly

    l-L=(2n-1+2C_H)lambda_g+4 ≤ G_box.

The source construction supplies S below l and a normalized cocycle T vanishing on A_L. The latter is obtained from a relative-to-X_L representative by the arclength pullback; it is not merely a cohomology class with a claimed support property.

For x below a, `lem:cj-operations` gives a globally null cut D_Tx of degree r below a-L+1. If a-L+1≤0, the cut is zero and W=0. This case is compressed in PROOF 1.3 but is explicit in the invoked source ordinary proof, lines 59–65, and is already entailed by the statement that no term survives a nonpositive open cut. For positive cut level the uniform fixed-degree increment gives W below a-L+1+d_*.

The source's absolute-unit proposition determines [D_TS]=[M] in H_n(Lambda). A relative scalar test alone would not determine this constant-loop component. Its actual proof uses nonvanishing, filtered interchange, and rank one, and then fills D_TS-c in fixed degree n. The bound for this filling V is <G_box+1+d_*.

After these finite fillings are chosen, choose the join radius for their bounds and the interchange chains. Smoothness of each individual g makes sufficiently small rotations have arbitrarily small length distortion; no uniform derivative bound across g is needed because this radius is allowed to depend on g, the chains and their finite length bounds. Source `lem:cj-small-chains` includes whole-parent support, interval factors, refinement prisms and cup-one comparisons, so further finite subdivisions do not introduce a hidden cost depending on the number of simplices or degree.

The two joined fillings have length <a+G_box+d_*+2. The interchange homology has length <a+G_box+4. The unit prism lies below a. Their boundaries combine to x, and the support of their sum is a union, not a concatenation. Consequently D_0=G_box+d_*+6 strictly exceeds every required increment. For j<J, d_j^box≤d_*<D_0. This is a common bound in all degrees and for all positive open cuts.

To return to energy, apply the g-arclength endpoint to the length filling. Its output has F_g equal to the old length. The source energy inequality keeps the original-boundary normalization prism in X_a. Adding that prism fills the original x in X_(a+D_0). The constants-relative projection is checked separately in section 8 below. No regular-cut approximation, nondegeneracy assumption, or continuous fiberwise choice is used.

**Finding:** the constants and interfaces close exactly as submitted. The empty-cut convention is an entailed clarification, not an essential repair.

## 4. Fine good covers and the singular-chain resolution

For any finite simplicial complex realizing P, take sufficiently many subdivisions and the vertex open stars. An intersection of stars is nonempty exactly when the corresponding vertices span a face. Every point in that intersection belongs to a simplex containing this face; linear contraction to its barycenter stays in that simplex and maintains positive coordinates at all specified vertices. These compatible contractions prove contractibility. This argument needs neither purity nor connectedness. In dimension zero the stars are the isolated points. A point belongs to at most p+1 stars. Mesh tends to zero on the finite realization; the diameters of stars tend to zero as well, providing the required fineness.

Here is the exact chain resolution, including the relative version. For a fixed cover and Z, let C^U_*(Z) be singular chains whose individual simplices are contained in one inverse-image cover member. The augmented horizontal complex for a given such singular simplex is the augmented simplicial chain complex of the nonempty set of indices of cover members containing its entire image. It is acyclic. Taking the direct sum over singular simplices proves exactness of the rows of the augmented Cech double complex. Subdivision and its prism show that C^U_*(Z)→C_*(Z) is a quasi-isomorphism. Only finite chains are involved, so a common sufficient subdivision exists for each calculation.

For (W,Z), with W=P×Lambda, apply the construction to both spaces and take the quotient. The subordinate subcomplex of Z is exactly C^U_*(W)∩C_*(Z). The quotient of the two augmented resolutions is therefore the local-pair resolution; the short exact sequences of chain complexes and the absolute quasi-isomorphisms imply its quasi-isomorphism with C_*(W,Z). Subdivision and prisms preserve subspaces. This does not assume that a closed cover satisfies excision, or that local Y_s is a product.

Filtering by cover degree has columns 0 through p and vertical degrees ≥0. Thus in every total degree the filtration is finite and exhaustive. Both augmentations and the filtration are natural for the level inclusions when the same cover is used. No local finite-rank assumption is required.

**Finding:** one sufficiently fine good cover of order at most p+1 exists at the full stated polyhedron scope, and both resolutions have the stated natural convergence.

## 5. E1-diagonal vanishing and filtration lowering

Let f be a map of these filtered total complexes and fix total degree N. If E^1_(r,N-r)(f)=0, then the same component is zero on E^2: its induced map on the kernel of the outgoing differential modulo the incoming boundaries is induced by the zero map on E^1 at that component. Inductively it is zero at every later page. This argument does not require the neighboring components or differentials to vanish. Finite convergence therefore gives zero on

    gr_r H_N = F_r H_N / F_(r-1) H_N.

Since f respects filtrations, this is exactly f(F_r H_N)⊂F_(r-1)H_N, for every r. Nontrivial extensions may make f nonzero on total homology, but cannot prevent this one-step lowering. For a sequence of p+1 such maps with the common cover filtration,

    F_p → F_(p-1) → ... → F_(-1)=0.

The composite is zero. Negative q positions are absent and do not cause extra requirements. Changing covers between steps would require additional comparison control; the proof explicitly avoids that by choosing a single cover for the finite sequence.

**Finding:** the diagonal argument is valid; neither collapse nor splitting of extensions has been assumed.

## 6. Local metric sandwiches, actual maps, LOW and HIGH

For each fixed finite range of cuts, choose a finite A larger than all cuts and all reference levels s+epsilon+D_0. Uniform continuity of the tensor family gives a cover on which the ratios of F_t and F_(t_U) differ from one by at most delta, for every t in the intersection U and any fixed t_U in it. Taking delta A/(1-delta)<epsilon and delta A<epsilon proves the two outer inclusions in (10); the middle inclusion is tautological. Stars sufficiently small in P have this property, and so do their intersections. All levels here are positive.

The four spaces in (10) are related by actual inclusions, with identity on the loop and parameter coordinates. For pairs they are related by maps with the same ambient U×Lambda. Contractibility of U identifies the two middle product spaces and pairs with fiber spaces and pairs, naturally for their inclusions. It is not used to assert that Y_s over U itself retracts to the reference fiber.

For LOW, cr_g(z)>s+epsilon for every nonzero global degree-q class makes the image of H_q(X_(s+epsilon)) in H_q(Lambda) zero. Every local fiber class is therefore globally null and is killed by the assumed D_0. The actual local map factors through that zero map, so is zero.

For HIGH, representability of all degree-q global classes below the reference source cut implies target surjectivity H_q(X_target)→H_q(Lambda). The target long exact sequence consequently has an injective connecting homomorphism

    H_q(Lambda,X_target) → H_(q-1)(X_target).

The boundary of any source pair class is in the kernel of H_(q-1)(X_source)→H_(q-1)(Lambda). The D_0 assumption kills it in X_target. Naturality followed by target injectivity makes the middle pair map zero. For q=0, Lambda is connected because S^n is simply connected, and every positive X contains constants; hence H_0(Lambda,X)=0. This also covers the endpoint without invoking a negative homology group.

Different intersections can use different t_U. They merely establish that each actual inclusion-induced E1 component is zero. Those actual maps already commute with the Cech differential. Coherent choices of reference points, contractions, cocycles or fillings are unnecessary.

**Finding:** LOW and HIGH are valid for the exact spaces and maps used; no coherence or implicit local trivialization is missing.

## 7. Dichotomy, endpoints, arbitrary admissible constants, and exact C

Now D_0>0 and R≥0 are any constants satisfying frozen part (1). The argument does not reuse the particular constants constructed in part (1). Put epsilon=D_0/(4p+8) and tau=D_0+2epsilon.

If (11) holds, its positive left side implies k-p>0. Thus every diagonal position with r'≤p has q=k-r'≥k-p>0. For each of the p+1 successive starting cuts s=a+r tau, r≤p,

    cr(z) ≥ q lambda(t_U)-R ≥ (k-p)lambda_- -R > s+epsilon.

LOW applies to every relevant E1 summand. The common-cover filtration argument kills all H_k, in particular the global kernel, by the increment (p+1)tau.

If (11) fails, set A=max{a,(k+1)lambda_++R+epsilon}. For every nonnegative q≤k+1, every global degree-q class has critical level ≤q lambda(t_U)+R≤(k+1)lambda_++R<A. The strict inequality ensures a representative below A, and hence below the reference source cuts for every HIGH step. The p+1 maps kill H_(k+1)(W,Y_A) in H_(k+1)(W,Y_(A+(p+1)tau)). A global-null class of H_k(Y_a) is the connecting image of a class in H_(k+1)(W,Y_a). Map that class to level A and use the natural connecting square to obtain its death. This includes k=0. When k<p, or k=0, the low inequality cannot hold and this high argument remains applicable; positions with q<0 are simply zero.

For explicit arithmetic, write B=(k+1)lambda_++R+epsilon. If A=B, failure of (11) gives

    A+(p+1)tau-a
    ≤ k omega + lambda_+ + p lambda_- + 2R
      + (2p+1)tau + 2epsilon.

If A=a, the left side is (p+1)tau and is bounded by the same right side because 2p+1≥p+1 and all remaining terms are nonnegative. This resolves the maximum in the author's compressed displayed inequality without changing it. Substituting tau gives

    (2p+1)tau+2epsilon
    = (2p+1)D_0+(4p+4)epsilon
    < (2p+3)D_0.

Indeed (4p+4)/(4p+8)<1, so there is even more slack than the final estimate needs. The low-case increment (p+1)tau is also strictly below (2p+3)D_0, hence below the frozen total bound. Therefore the single increment

    k omega + (2p+3)D_0 + lambda_+ + p lambda_- + 2R

works for every a>0. A cover may depend on a and k through the finite largest level A+(p+1)tau. Its cardinality and mesh do not enter the increment: the number of filtration steps is always p+1. Thus the bound is uniform in a, even for unbounded a. It is valid at critical open cuts because all representative and sandwich comparisons have strict epsilon margins.

**Finding:** the exact frozen coefficient and additive constant follow for every k≥0 and every admissible D_0,R. The maximum case distinction is an entailed arithmetic clarification.

## 8. Constants-relative projection, including low degrees

On W=P×Lambda let i include P×M and e evaluate at time zero without changing t. Then e i=id and Q=id-i_#e_# is a chain map annihilating C_*(P×M). It preserves C_*(Y_a) for every a>0 because the new constant loops have F_t=0. For a relative cycle z, its boundary lies in C_*(P×M), so Qz is an absolute cycle; Qz and z represent the same relative class. If z is globally null relatively, there are finite chains U in W and c in P×M with boundary U=z+c. Applying Q gives boundary QU=Qz. Thus the absolute representative is globally null, and the established absolute filling bound applies with no increment loss. Its filling projects to the required relative filling.

This is valid in degree zero as well as in degrees where the long exact sequence does not itself identify absolute and relative groups. It also proves the fiber relative assertion used in part (1), with P a point. There is no omitted constant summand or low-degree connecting obstruction.

## 9. Round levels, powers and injectivity in all n≥3

The source `eqv:round-attachment` has actual critical manifolds C_m=STS^n at energy (2pi m)². Its Fourier calculation gives negative rank (2m-1)d and nullity dim STS^n=2n-1. The square-root-energy crossing is consequently at c_m=2pi m, with no factor of sqrt(2). The mod-two Gysin sequence of S^(n-1)→STS^n→S^n has zero Euler map because chi(S^n) is even, including even n. It gives rank-one groups in degrees 0,d,n,2n-1. The mod-two Thom shift therefore gives exactly

    (2m-1)d, 2md, 2md+1, (2m+1)d+1.

The small sublevel contributes degrees 0,n. These list all AU^r (r≥0) and U^r (r≥0) exactly once: the two crossing AU classes have r=2m-1,2m, and the two U classes have r=2m-1,2m. Residue separation for d≥2 rules out coincidences, also when n=3.

To justify injectivity rather than just rank counts at one stage, filter by successive regular round levels. In each total degree the crossing spectral sequence has at most one generator, and the known global algebra has exactly that one-dimensional group whenever this generator occurs. Any differential hitting or leaving it would remove that only possible associated-graded generator and contradict the global rank. Finite convergence in each degree is valid because the bottom crossing degree tends to infinity, and global singular cycles and bounding chains have compact, hence bounded-energy, support. Thus the generator cannot later die, and regular-stage inclusions into global homology are injective. Any finite chain in an arbitrary open cut is contained in a smaller regular cut (there are only discrete round critical levels). This extends injection to every positive open cut, including a critical cut.

This also verifies the author's rank argument directly, in addition to HR section 6's explicit perfect-round-filtration statement and diagram. Theta=U², so Theta^m=U^(2m) has degree k_m=n+2md and first crossing c_m=2pi m. The diagram was visually checked rather than inferred solely from a garbled extraction. No orientation issue or odd-n-only computation has been transferred to even n.

## 10. Scaling cover, Mayer–Vietoris and strict endpoints

For f(t)=b-(b-1)t², b>1, one has 1≤f≤b and F_t=fF_h. The sets U,V in (15) are open in Y_a: the signs of t define open relative half-intervals, and [-1,1]×X_(a/b)^h is an open product contained in Y_a. At t=0 the fiber is exactly X_(a/b)^h, so U∪V=Y_a. Their intersection is exactly the product [-1,1]×X_(a/b)^h, since no point has both t<0 and t>0 unless it belongs to that shared product.

Keep gamma fixed and move t linearly toward -1 in U. For initial t≤0, f decreases along the path. For initial t>0, U membership already imposes F_h(gamma)<a/b, which keeps the entire path admissible, including its passage through 0. The path remains in U, and fixes its endpoint fiber. This is a strong deformation retraction onto X_a^h. The analogous path to +1 works in V. The intersection retracts by the same kind of parameter motion to its central fiber. These homotopies are independent of a, hence commute with increasing levels. Under the resulting homology identifications, the two intersection maps are the ordinary inclusion X_(a/b)^h→X_a^h, not a differently chosen correspondence.

Ordinary singular Mayer–Vietoris for this open cover gives exactness at H_k(X_a^h)⊕H_k(X_a^h), with diagonal first map over F2. For c_m<a, the unique lift z_m(a) exists and is unique by the preceding round argument. If also a≤bc_m, the diagonal pair (z_m(a),z_m(a)) cannot come from the intersection: a/b≤c_m and a preimage would represent z_m below that cut. At equality, a finite singular cycle in X_(c_m)^h has compact image and maximum F_h strictly smaller than c_m, contradicting cr(z_m)=c_m. Thus exactness yields a nonzero w_m(a).

The two endpoint images in H_k([-1,1]×Lambda) are the same z_m, since their inclusions are homotopic in the full product. Their sum is zero over F2. Hence w_m(a) is globally null. Naturality of the cover and retractions makes its image at a' the corresponding diagonal class. It is nonzero whenever c_m<a≤a'≤bc_m and zero for a'>bc_m, because then z_m is carried by X_(a'/b)^h. In particular it remains nonzero at the open cut bc_m itself. The construction applies to every integer m≥1 and every real b>1.

## 11. Infima, relative lower bounds, limsup, and sharpness

The persistence just proved does not mean that death is attained at the critical cut. For any D<(b-1)c_m in the nonnegative range relevant to beta, choose a=c_m+eta with eta>0 so small that a+D≤bc_m. Then w_m(a) survives the inclusion with increment D. Thus every such D is excluded from the set defining beta_(k_m), proving beta_(k_m)≥(b-1)c_m by the definition of infimum. No assertion about attainment of that infimum, or equality in each degree, is required.

Since k_m>n+1 and [-1,1]×M has homology only in degrees 0,n, the absolute-to-relative maps in degree k_m are isomorphisms at every positive level and globally, naturally for inclusions. The same surviving classes give beta_(k_m)^rel≥(b-1)c_m. The chain projection was needed for the general upper bound; this high-degree isomorphism is sufficient for the example's lower bound.

For the unit round metric lambda_h=lim 2pi m/(2md)=pi/d. Scaling gives lambda(t)=f(t)pi/d and omega=(b-1)pi/d. Consequently

    ((b-1)c_m)/k_m = 2pi m(b-1)/(n+2md) → omega.

Part (2) bounds beta_k/k and beta_k^rel/k above by omega+C/k in every positive degree, not just the subsequence k_m. Both all-degree limsups are therefore exactly omega. Taking any one fixed b>1 shows that a coefficient smaller than one cannot be compensated by a finite degree-independent family constant. This proves the frozen sharpness claim and no stronger unasserted pointwise equality.

## 12. Nonhomothetic constant-frequency families and other assertions

Let phi be a real, nonconstant degree-two spherical harmonic. It is bounded, so h_t=(1+t phi)h is positive for t in a sufficiently small compact interval [0,delta]. This is an allowed nonempty finite one-dimensional polyhedron and each fiber is smooth. The scalar-curvature linearization at the unit round metric for the variation phi h is

    -<Ric,phi h> + div div(phi h) - Delta tr(phi h)
    = -n(n-1)phi -(n-1)Delta phi
    = (n-1)(n+2)phi.

Choose two fixed points where phi differs. Their scalar-curvature difference has a nonzero derivative at zero, so it is nonzero for every sufficiently small positive t. Therefore these h_t are not homothetic to a round metric (even allowing diffeomorphism), as constant scalar curvature is preserved by those operations. This proves the needed existence of a family not consisting entirely of homothetic metrics; the proof does not claim pairwise inequivalence of all its nonzero parameters.

Critical levels scale by s under g→s²g, hence lambda(s²g)=s lambda(g). The positive continuous scalar s(t)=lambda(h_0)/lambda(h_t) therefore produces a C0-continuous family g_t=s(t)²h_t with constant lambda. Every fiber is smooth in the sphere variable, and a spatially constant rescaling cannot remove its scalar-curvature variation. No differentiability of lambda in t, fixed volume, curvature control, or other normalization is silently required. This is a nonvacuous example at exactly the allowed regularity.

The proof's methodological claims are also accurate: the total-space construction chooses neither geodesics nor continuously varying fiber fillings; it uses actual local inclusion maps. Its beta is a kernel-death invariant, not a prime-image, orbit or critical-value count. Infinite degeneracy is not removed by an unmentioned perturbation. The statement does not extend beyond the given Riemannian sphere/F2 scope. The prefreeze dimensionless resonance estimate in DERIVATIONS is compatible with (19): its lower error is at most 7n-6, and its upper error at most 4d+(2dv/(u mu_h))C_Q. The later R_box bound is a looser length-error version, not a postfreeze change of theorem.

## Strongest relevant alternatives and compatibility objections

These are correctness comparisons, not a contribution assessment.

1. A uniform multiplicative metric comparison alone would turn a fixed-reference additive filling bound into an error growing with the starting cut. It does not prove part (1). The submitted proof instead applies fixed h local recipes to g-arclength pieces and then uses the full paid cut/join to remove degree dependence; the preceding sections check those actual operations.
2. BMW, *Persistent homology of function spaces*, [arXiv:2505.16907v2](https://arxiv.org/pdf/2505.16907v2), Theorem 5.1 and its full relative pseudomanifold/path-cell proof, supplies an additive bound linear in degree for based and free loop spaces. Its section 4 uses NR's based-loop contraction mechanism. The source's strong-H1 construction is the actual interface used here; a uniform-continuity or arbitrary-fillings argument is not substituted for it. NR's [2012 preprint](https://www.math.toronto.edu/rina/morseoct12.pdf), section 8, was read as a comparator; its Theorem 7.3 was not independently read and is not a premise in the new deduction.
3. HW, *Product and coproduct in string topology*, [arXiv:1709.06839v4](https://arxiv.org/pdf/1709.06839v4), definitions 1.2, 1.4 and 1.7 and Theorem 2.13, has the actual H1/short-arc/cochain interfaces compared in the source. I also read its sections 2.1–2.3 prerequisites, extending the author's stated coverage. Remark 4.14 explicitly demonstrates failure of a naive Frobenius formula for its canonical lift. That failure is not an objection to the separately stipulated native `thm:filtered-interchange` with its degree restrictions and absolute-unit proof.
4. CHO, *Loop coproduct in Morse and Floer homology*, [arXiv:2008.13168v3](https://arxiv.org/pdf/2008.13168v3), section 8.1's Euler correction and section 8.2's formulas retain constant-loop terms; Remark 8.4 makes this distinction explicit. The latter computations use odd spheres and integer coefficients. They are not asserted to be the source's native cut in every parity. Its external [22] theorem is not independently re-proved here, nor needed as an added premise of the family argument.
5. COS, [arXiv:2608.04691v1](https://arxiv.org/pdf/2608.04691v1), sections 5–6, and Shelukhin, [arXiv:1904.06798v2](https://arxiv.org/pdf/1904.06798v2), sections 3.1–3.2, were read for the stronger compatible bounded-error/string-operation comparisons. Their coefficient restrictions and Floer interfaces are not transferred wholesale to a total family of loop sublevels. Shelukhin Proposition 10 is explicitly a sketch. No unseen Floer prerequisite is being used to bridge the total-space step. The proof gives its own finite-cover resolution and local-pair argument.
6. Uniform fiber death alone cannot give uniform total-space death in all degrees; the submitted scaling example actually demonstrates the obstruction. Conversely, spectral-sequence collapse would be an unnecessarily strong and unjustified gluing claim. The one-step filtration argument is the correct weaker assertion, and is sufficient with precisely p+1 maps.

## Disposition of objections and remaining obligations

The potential essential objections were: lack of curvature control in uniform recipes; a metric-dependent resonance exception set; loss of the absolute unit; uncontrolled join distortion; a bad cover in the nonpure case; differentials or extensions defeating E1 vanishing; incoherent reference fibers; failure of HIGH at q=0; the maximum in (13); loss of constants at small degrees; even-dimensional round attachments; and strict-cut/infimum confusion. Each is resolved above from the unchanged text and the stipulated interfaces.

The explanations of the empty-cut case, E1 subquotients, the max case in (13), and round injection at critical open cuts expand compressed arguments already entailed by the submission. They add no premise and change no conclusion or constant. No author file was repaired or certified in a modified form.

There is no remaining essential correctness obligation relative to the stipulated source premises. The unavailable Bott/GM/formal endpoints and unread recursive comparator prerequisites are access limits, not secretly assumed independent verifications; they are not needed beyond the expressly paid source operations. The review does not claim a proof of the upstream infinitude theorem, independent formal verification, historical clearance, publication readiness, or any contribution grade. Parent adoption remains separate.
