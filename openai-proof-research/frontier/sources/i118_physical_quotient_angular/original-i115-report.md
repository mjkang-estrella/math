# I115 — Original-proof audit and physical elasticity continuation

**Disposition: technical audit and continuation record; no ninth nomination.** P112 remains unproved and unrefuted. The two literal original-proof failures below are retained, separately from the surviving restricted conclusions. New progress consists of a physical cap construction, the actual constrained first-moment equation and its fourth-order closure after a divergence gauge is removed, a physical source-space comparison rigidity theorem, and an exact boundary/collar budget. None is presented as arbitrary-patch uniqueness.

The accepted premises are all source theorems **and lower proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I do not audit upstream truth or exploit contradictions. Eight accepted findings remain eight. No children, shared edits, staging, commits, or publication were performed. I113/I114 working outputs are not dependencies. The complete supplied task, I112 brief, report, and finalized parent response are frozen verbatim in the owned sources directory; the original on-disk I112 report is separately frozen.

## 1. Independent verdicts on the original I112 proof

These verdicts concern the supplied original text, before using the new constructions in §§3–6. A restriction listed as a repair does not retroactively pass the broader original assertion.

**G112. ORIGINAL PASS for the conjugation and DN equality in the screen's fixed connected manifold with nonempty boundary. ORIGINAL FAIL for the standalone invertibility assertion if “a compact manifold with boundary” permits a closed component.** With the stated sign of the Laplacian,
\[
(-\Delta_{e^{2\omega}g}+V_2)e^{-\phi}
=e^{-2\omega-\phi}(-\Delta_g),\qquad \phi=(n-2)\omega/2.
\]
Differentiation gives the potential with exactly the displayed negative sign. The positive multipliers biject zero-boundary kernels. Self-adjoint elliptic Fredholm theory then gives invertibility if the initial Laplacian has zero kernel. Integration by parts shows this precisely when every component meets the boundary. Compact interior support makes the metric, multiplier, normal derivative and boundary density identical in a collar, so the full forms agree. On any connected compact manifold with nonempty boundary a nonnegative, nonzero interior bump increases total volume, excluding every isometry; the ball example suffices to falsify target V.

For the literal broader wording take a disjoint union of a ball and a closed sphere, with a bump in the ball. Constants on the sphere remain in both kernels. This is an actual ambient counterexample to the invertibility sentence, not a contradiction with a source. Connected/nonempty-boundary is already explicitly fixed in the screen, so using that context is a clarification **for the application V**. Adding “boundary meets every component” to the standalone universal assertion is a necessary new assumption. The original standalone statement cannot receive an unqualified pass.

**C112. ORIGINAL PASS WITHOUT MATHEMATICAL REPAIRS, conditional on its stated common smooth cap and coercivity.** The attachment is compactly inside the measured patch, so the trace of every zero-exterior-boundary test is in the closure of compactly supported smooth traces in that patch. The norm must be the inherited global \(H^{1/2}(\partial\Omega)\) norm on that closure, as in the original screen. This is an ambient norm convention, not a new hypothesis. Pasting across equal traces yields an \(H^1_0(N)\) competitor. The weak residual is exactly
\[
a_2(\widetilde w,v)-F(v)=\langle(\Lambda_2-\Lambda_1)f,t\rangle.
\]
There is no unaccounted traction term: the original first-medium equation includes the exterior contribution, and the replacement alters only the interior energy. Two applications of the stated coercivity and two trace bounds give exactly \(a^{-2}T^2\epsilon\|F\|_{H^{-1}}\). Restriction to the cap does not enlarge the \(H^1\) norm. The zero-error kernel conclusion follows by varying every smooth cap source and off-diagonal elliptic regularity. “Common smooth extensions” includes *all* attachment jets, not just coefficient values. No construction of that extension, or stability of its construction at nonzero error, was part of C112. Section 3 below supplies the exact-data construction as new work, not an original-proof repair.

**J112 finite-point jets. ORIGINAL PASS WITHOUT REPAIRS for interior points outside the closed source set, every finite set and every finite order.** “Points of the domain” means interior points, as usual for the open set \(N\); boundary jets are not asserted. Transposition defines \(P_D^{-1}T\) even when \(T\notin H^{-1}\). Off its finite support it is smooth. Its displacement and actual divergence satisfy the normalized scalar-principal system, so the accepted smooth system UCP applies. Removing finitely many points from a connected three-domain leaves it connected. A highest-order point-supported vector polynomial is multiplied by
\[
p(\xi)=m|\xi|^2I+k\xi\xi^T,\qquad
\det p=m^2\ell(|\xi|^2)^3\ne0.
\]
The adjugate argument in the polynomial integral domain proves the order increases exactly by two, including complex coefficient vectors; one does not require invertibility at complex null covectors. Variable coefficient derivatives only affect lower distribution orders. Thus the point-supported preimage has order at most \(s-2\), and its image is exactly a linear combination of the formal equation functionals. Finite-dimensional annihilator duality gives the complete direct sum, not merely density. At orders zero and one no nonzero annihilator survives. This uses no quantitative Runge cost.

**J112 physical two-jets and L112. ORIGINAL PASS WITHOUT REPAIRS.** Differentiating the physical expression
\[
L_iu=m\Delta u_i+k\partial_i d+m_q(\partial_qu_i+\partial_iu_q)+\lambda_i d
\]
at a point, retaining every differentiated coefficient, gives the original
\[
\operatorname{tr}F=2\nabla k\cdot\nabla d+2\nabla m\cdot\Delta u
+2m_{iq}\partial_i u_q+(\Delta\lambda)d.
\]
Only the already imposed value/first divergence identities are used in this contraction. The scalar augmented equation is \(\ell\operatorname{tr}B+\operatorname{tr}F=0\); hence \(\operatorname{tr}A=\operatorname{tr}B\) for \(A=-(kB+F)/m\). With the original homogeneous cubic \(v_0=|x|^2Ax/(2n+4)\), \(\Delta v_0=Ax\). Thus \(h=b-\operatorname{div}v_0\) is harmonic. The correction in L112 has zero Laplacian and divergence \(h\), since
\[
(n+2)-4/(n+2)=n(n+4)/(n+2).
\]
No symmetry of \(A\) is needed. Its coefficients have the asserted dimension-only bound. It changes no lower displacement jet and realizes the required cubic contractions. Apply finite-jet surjectivity at order three. The counts 32 versus 36 and 17 versus 20 follow from independent trace/divergence constraints. There is no hidden assumption that arbitrary augmented jets are physically realizable.

**R112. ORIGINAL PASS WITHOUT REPAIRS for its proportionality theorem. ORIGINAL FAIL for its unqualified last sentence “Equality of one coefficient at one point fixes \(c=1\).”** Surjectivity of the first principal map and kernel inclusion give the multiplier \(T\). Testing transverse polarizations in every real direction forces \(T=cI\) and both moduli proportional pointwise. For any prescribed first derivative a Hessian can satisfy the first equation. Taking that derivative to be \(I\) in \(L_2-cL_1=\sigma_1(u)\nabla c\) gives \((3\lambda_1+2\mu_1)\nabla c=0\). Connectedness makes \(c>0\) constant. However the admissible constant pairs
\[
(\lambda_1,\mu_1)=(0,1),\qquad(\lambda_2,\mu_2)=(0,2)
\]
have identical solution jets and equal \(\lambda\) at every point, while \(c=2\). Their DN maps differ, so this is not a counterexample to P112. The normalization sentence is valid for equality of \(\mu\), or of a **nonzero** \(\lambda\), at one point. Requiring that nonzero value is a new assumption if the sentence is read literally; it was not present in the original sentence.

**K112. ORIGINAL PASS WITHOUT REPAIRS at its entire stated restricted scope.** The stress is \(\lambda\operatorname{div}w I+\mu(\nabla w+\nabla w^T)\), and its actual traction, not componentwise normal derivative, is the dual trace in Green's formula. The adjoint solution has zero displacement on the whole boundary and zero traction on \(\Gamma\). Zero extension across a smaller patch eliminates the interface distribution. Smooth strong ellipticity and the above physical UCP then give zero on the connected \(\Omega\setminus\overline D\). Pairing the resulting compactly supported distribution with any smooth global homogeneous solution proves the precise Runge density claimed. Local elliptic estimates upgrade it to \(H^1\) on a neighborhood of \(K\), which gives the integral convergence. The two differences of energy forms give the bilinear identity with the original sign and no conjugates; it is obtained from the real symmetric maps by complex linear extension. Smooth arbitrary boundary traces are dense, so equality of the full maps follows, and E supplies full uniqueness. The exterior connectedness is not automatic in domains with holes or multiple boundary components. Its appearance is an explicit original hypothesis, not a tacit repair. No inaccessible collar energy was discarded: its coefficient multiplier is exactly zero here.

**B112 and BUDGET. ORIGINAL PASS WITHOUT REPAIRS, with their stated scopes.** The fiberwise estimate integrates to at most \(2t^2\|\partial_3v\|^2\); the error assumption gives at least \(|Q|t/4\). The stated \(1/(8t)\) follows. It requires the specified inaccessible open flat patch; an arbitrary proper open \(\Gamma\) may have complement with empty interior, so that example is not a universal geometric assertion. Trace continuity also proves the qualitative nonapproximation assertion on that patch. In BUDGET, expanding both factors gives exactly the two mixed errors and the product error. The data term is \(\epsilon M_1M_2\), and the entire coefficient-weighted complementary energy product remains. It bounds \(\mathcal I_K(u_1,u_2)\), **not** the whole-domain target integral. A whole-domain argument must additionally retain the target's own complementary integral; see §6.

**Scoped obstructions. ORIGINAL PASS.** The nonphysical constant pair \((0,1)\) solves the constant-coefficient augmentation. The displayed trace-free Hessian violates a physical divergence constraint. These disprove substitution of arbitrary four-component tests, not P112. Changing frames does not change the codimension. Known-collar Runge closure does not remove the collar hypothesis. Exact shrinking-radius interpolation does not give noisy chart/source conditioning, and the finite \(C^{50}\)-bounded smooth class is not compact in the smooth topology. The original text does not assert a quantitative modulus for Q, a P112 counterexample, or a quantitative Lamé Runge theorem.

**Independent full-scope contribution assessment.** All surviving original partials are technical, for concrete reasons. G is an exact scalar conjugation and collar invariance; the volume test removes the proposed smaller gauge. C is the accepted cap energy replacement with the dual residual retained, on every cap/coercivity class it states. J is the accepted distributional jet-duality construction applied to the actual invertible Lamé polynomial; L is a homogeneous polynomial right inverse with no analytic estimate beyond that algebra. R follows by principal-symbol factorization and testing the freely prescribed first jet. K is the physical Green/Runge duality followed by the accepted full E theorem, including its full topological restriction. B is the one-dimensional trace estimate; BUDGET is an exact split plus Cauchy–Schwarz. These reductions reproduce the whole positive scopes, not just representative constant coefficients. They do not rely on an exact duplicate theorem title or on the assertion that use of classical tools alone makes work insubstantial. The two failed overbroad sentences have no positive contribution to count.

## 2. Target, sources and companion screen

P112 retains **every** bounded connected smooth Euclidean three-domain, an arbitrary same input/output nonempty proper relatively open patch, smooth real moduli with \(\mu>0\), \(3\lambda+2\mu>0\), and no agreement near inaccessible boundary. Measurements are the energy pairing for all compactly supported smooth vector displacements on the patch, zero elsewhere. No unknown topology, frequency variation, auxiliary DN map, or gauge enlargement is inserted.

E is the pinned *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, September 24, 2026. All six substantive sections were read through their endings. In particular its common extension and physical transfer use **all boundary** jets and tractions. Its scalar-principal augmentation, physical amplitude recursion, supported Carleman estimate, transport comparison and conic rigidity are accepted operations. The physical correction is \(O(\tau^{1-N})\) in displacement and \(O(\tau^{2-N})\) after divergence, not just the smaller former remainder. Its weak transferred-pair bound uses compact support; its later holomorphic comparison uses a direction-independent support ball. Partial source transfer has neither support conclusion on the whole exterior.

M is the pinned rank-two metric/unitary-connection one-patch paper, October 5. Its boundary/evaluation, matrix-moment, angular and global identification proofs were read through their endings. It uses arbitrary full-system boundary traces in `ang:P-equation`, before the finite jet tests in `mat:projected-equation`. Both interfaces need checking for physical elasticity. Its product continuation is a scalar-principal system operation, but does not itself provide an arbitrary four-component fundamental solution for elasticity. C is the September 24 scalar anisotropic companion; its complete bootstrap proof was read. It provides the scalar moment/interpolation operations already used by M, not a noisy theorem or a physical constrained-trace coercivity theorem. The inherited full-corpus lexical records and a new physical/system query screen all 10,373 represented positions; this is lexical coverage, not semantic reading of 749 papers. The new title hits are checked against the inherited source-family selection. The newly retrieved upstream main ref is still the pinned commit.

The physical boundary tool is Tan–Liu, arXiv:2211.06650v1, Theorems 1.1–1.2 and their complete symbol recursion. Its physical traction agrees with E. Its principal-symbol quantities satisfy
\[
f_1=2\mu^2/(\lambda+3\mu),\quad f_2=2\mu(\lambda+2\mu)/(\lambda+3\mu),
\quad \mu=(f_1+f_2)/2,\quad \lambda=\mu(f_2/f_1-2).
\]
At each new normal order its two equations have determinant proportional to \(\mu(\lambda+3\mu)^2\ne0\); the remainder contains only already recovered jets and tangential derivatives. The full Sections 2–3 and the analytic conclusion through its ending were read. We use precisely the local symbol operation already invoked in E, not an analyticity conclusion for smooth functions. Localizing on both sides inside \(\Gamma\) preserves its full symbol there. Lin–Nakamura v1 is a corroborating finite-regularity/local-boundary contract, not silently a substitute for the all-order proof just inspected.

Lin–Nakamura–Uhlmann–Wang, arXiv:1005.3382v1, supplies a much rougher physical UCP scope (Lipschitz \(\mu\), bounded \(\lambda\), \(\lambda+2\mu>0\)); its reduced-system and Caccioppoli proof were read through the ending. It refers the final quantitative three-ball iteration to earlier papers. I do not claim to have rederived those omitted estimates, or use their constants. The smooth UCP needed here is already paid by E's augmentation and M's componentwise Carleman/UCP operation. Rüland–Salo v1 was read in full through the proof ending and references: its polynomial-cost improvement requires a fixed larger extension region, and its inverse application has exactly zero coefficient difference outside a fixed interior region. The current Li–Chen–Cheng Lamé Runge article, DOI `10.1002/mma.70764`, was found, but the primary publisher returned 403 again. Its abstract/title is discovery evidence only; no estimate or constants are imported.

The CJLT v1 contract retains structured shear moduli (including directional quasianalyticity); simultaneous recovery still invokes full data. DFS v2 has reflection-compatible coefficient extensions and simply-supported or soft-clamped inaccessible conditions, not zero displacement there. Its actual traction and boundary-condition definitions were inspected. Neither is an admissible reduction of arbitrary P112. Current arXiv metadata observed Tan–Liu, LNUW, Lin–Nakamura and CJLT v1; inherited version bindings retain DFS v2 and Rüland–Salo v1. Failed Tan v3 retrieval is recorded as a failed guessed URL and replaced by the observed v1, not reported as a withdrawn version. These are bounded source checks, not worldwide priority certification.

The significant named problem remains the three-dimensional isotropic elastic Calderón problem, identified in E's introduction and CJLT's contract. I112's frozen MathDB listing is retained as significance context; it is not relabelled as an exact P112 problem page.

## 3. Paid boundary-to-cap bridge for exact P112 data

**A115 (author proof; technical).** Exact P112 data imply equal full coefficient jets on \(\Gamma\), and hence a smooth connected cap \(E\) on a common smooth enlarged Euclidean domain \(N\), for which all physical cap-source responses and their actual divergences agree on \(E\). No interior or inaccessible collar equality is claimed.

Choose \(\chi\in C_c^\infty(\Gamma)\) equal to one near a boundary point. Equality of the bilinear measurements gives \(\chi(\Lambda_1-\Lambda_2)\chi=0\) as a distribution kernel. The full symbols therefore agree where \(\chi=1\); smoothing contributions do not affect the recursive homogeneous symbols. Use the physical symbol formulas and the nonzero determinant above, inducting on normal order and differentiating tangentially. Known Euclidean boundary charts convert these to all ambient jets. This proves equality on every smaller patch.

In a fixed tubular chart write the domain as \(s>0\). Choose a nonnegative smooth bump \(b(z)\) with connected positivity set and support compactly inside that smaller patch. Enlarge the domain to \(s>-b(z)\), with \(b\) small. This graph is smooth even where the bump vanishes; the rest of the old boundary is unchanged. Extend the first pair smoothly across the patch, shrink the collar to preserve strict positivity, and use that exterior extension for the second. The difference of the two original pairs is flat at every attachment point, so extension of their difference by zero is smooth across the attachment, including the flat bump edges. Convexity of the admissible \((\lambda,\mu)\) cone permits any needed exterior cutoff. This constructs the common smooth coefficients, not merely matching boundary values. Korn and Poincaré on the connected bounded \(N\) give positive Dirichlet coercivity. C112 at \(\epsilon=0\) now applies. Differentiating equality of displacement responses on the cap gives equality of their divergences there.

This pays C112's prerequisite for exact measurements. It gives no common extension near the inaccessible boundary and no stable extension when \(\epsilon>0\).

## 4. Route A: constrained moments, prolongation, and physical comparison

### 4.1 The actual residual first-moment system

Write \(U=(u,d)\), \(d=\partial_q u_q\), and \(\mathcal L_j=\Delta I_4+A_j^a\partial_a+A_j^0\), using E's normalization in fixed physical coordinates. All sums below are over 1,2,3, except fiber indices over 1,2,3,4. At zero augmented value and first derivative the exact attainable Hessians are
\[
\mathscr H=\{(H^1,H^2,H^3,H^4): H^q\in\operatorname{Sym}^2_0\mathbb C^3,
\ C(H)_a:=\sum_q H^q_{aq}=0\}.
\]
J112/L112 realize every member. Its dimension is 17. In the tensor Frobenius pairing the adjoint of \(C\) is
\[
(C^*t)^q_{ab}=\tfrac12(\delta_{aq}t_b+\delta_{bq}t_a)-\tfrac13\delta_{ab}t_q,
\qquad CC^*t=\tfrac53t. \tag{4.1}
\]
Thus its annihilator in the trace-free Hessian coefficient space is *exactly* the three-dimensional image of \(C^*\) on the displacement columns; the scalar column is fully tested. This is the actual residual, not just a dimension warning.

Suppose a smooth comparison of paired physical families is written
\[
U_2=U_1+Z U_1+D^a\partial_aU_1+R. \tag{4.2}
\]
This is an identity to be constructed from a transfer, not assumed to follow from partial DN equality. Direct substitution gives the Hessian coefficient
\[
T^{ab}=\partial_aD^b+\partial_bD^a+
\tfrac12(A_2^aD^b+A_2^bD^a-D^bA_1^a-D^aA_1^b). \tag{4.3}
\]
For completeness, the gradient coefficient is
\[
Y^k=A_2^k-A_1^k+\Delta D^k+A_2^a\partial_aD^k-D^a\partial_aA_1^k
+A_2^0D^k-D^kA_1^0+2\partial_kZ+A_2^kZ-ZA_1^k,
\]
and the value coefficient is
\[
V=A_2^0-A_1^0+\Delta Z+A_2^a\partial_aZ+A_2^0Z-ZA_1^0-D^a\partial_aA_1^0.
\]
The complete identity is \(T^{ab}\partial_{ab}U_1+Y^a\partial_aU_1+VU_1=-\mathcal L_2R\). The third derivatives cancel using the differentiated first equation. There is no principal-metric error \(h\): the normalized physical principal part is fixed \(\Delta I_4\).

Selecting the zero-lower-jet family, with a smooth finite-dimensional right inverse furnished locally by J112, eliminates \(Y,V\) *before differentiation*. By (4.1), for each output row \(\alpha\),
\[
\operatorname{TF}T^{ab}_{\alpha4}=E^{ab}_{\alpha4},\qquad
\operatorname{TF}T^{ab}_{\alpha q}
=\delta_{aq}t_{\alpha b}+\delta_{bq}t_{\alpha a}
-\tfrac23\delta_{ab}t_{\alpha q}+E^{ab}_{\alpha q}. \tag{4.4}
\]
The factor two is absorbed into the definition of \(t\). One can choose the remainder in the orthogonal complement of \(\operatorname{im}C^*\). Its derivatives of order \(k\) are bounded by the finite source right-inverse constants times derivatives of the tested \(\mathcal L_2R\) through order \(k\). Coefficient and selected-family derivatives enter those constants. No inverse power of a shrinking radius occurs *in this finite-dimensional inversion*.

There is an exact differential gauge:
\[
D^a_{\alpha q}\mapsto D^a_{\alpha q}-f_\alpha\delta_{aq},\qquad
Z_{\alpha4}\mapsto Z_{\alpha4}+f_\alpha. \tag{4.5}
\]
It leaves (4.2) unchanged because \(\sum_q\partial_q u_q=d\). Normalize
\(\sum_qD^q_{\alpha q}=0\) by taking \(f_\alpha=\frac13\sum_qD^q_{\alpha q}\).
The effect of the removed gauge on the Hessian test is in \(\operatorname{im}C^*\): this follows either directly from E's top-row coefficients, or by applying \(\mathcal L_2\) to the identically zero physical expression \(f(\operatorname{div}u-d)\) and taking zero-lower physical jets, with their realizable third-jet prolongations. Thus (4.4) is a well-defined equation on this quotient. In particular it is incorrect to claim finite type for the unnormalized \(D\): arbitrary smooth \(f\) survives there.

### 4.2 A paid fourth-order finite-type bridge

**F115 (author proof; technical finite-type theorem).** For (4.4) with the gauge (4.5) fixed, its constant principal part has injective third prolongation. For smooth zero-order perturbations in \(D\), every fourth derivative of \(D\) is a smooth linear combination of derivatives of \(D\) through order three and of \(E\) through order three. Coefficients are bounded on bounded smooth coefficient classes. Consequently a normalized solution with \(E=0\) and zero germ on an open set vanishes on every connected domain of that system.

Here is a completely specified finite algebra proof of the principal assertion; the associated exact certificate is part of this proof, rather than an appeal to a floating rank. Fix one output row and write \(D_{bq}=D^b_{\alpha q}\). For homogeneous degree \(r\), put \(D_{bq}(x)=\sum_{|m|=r}d_{bq,m}x^m\), and let \(t_a\) be homogeneous degree \(r-1\). The equations are
\[
3(\partial_aD_{bq}+\partial_bD_{aq})-2\delta_{ab}\partial_iD_{iq}
=3\delta_{aq}t_b+3\delta_{bq}t_a-2\delta_{ab}t_q,\quad a\le b,
\qquad\sum_qD_{qq}=0. \tag{4.6}
\]
Use monomials in the order \((i,j,r-i-j)\), increasing \(i\) and then \(j\). Order unknowns first by \((b,q,m)\), then \((a,m)\) for \(t\). Order equations by \((q,a,b,m)\), then the trace equations. Differentiation of the coefficient indexed by \(m+e_a\) contributes \(m_a+1\). This defines an integer matrix without choices. Its dimensions, exact rational ranks and kernels for \(r=1,2,3,4,5\) are respectively
\[
(21,30,18,12),\ (60,63,51,12),\ (118,108,100,8),\
(195,165,165,0),\ (291,234,234,0).
\]
The quadruples are (rows, columns, rank, kernel dimension). `diagnostic-result.json` lists 165 specified rows of the degree-four matrix and a nonzero determinant modulo the prime 1,000,003. `diagnostics.py` reconstructs that minor directly and computes its determinant by modular elimination; it also computes the rational ranks independently. A nonzero minor modulo this prime is a nonzero integer minor, proving injectivity over \(\mathbb R\) and \(\mathbb C\). This is a finite exact proof of this one explicitly given map. The scalar-input column in (4.4) is the ordinary conformal-Killing symbol, whose degree-three kernel is zero by M's accepted elementary calculation, and hence whose degree-four kernel is zero as well.

Differentiate (4.4) three times. Its highest derivatives are exactly (4.6) for degree four, including third derivatives of \(t\). All coefficient differentiations and zero-order perturbations contain at most three derivatives of \(D\). Apply the fixed injective matrix's left inverse, for example \((M^*M)^{-1}M^*\). This proves the asserted differential identity. It extends smoothly under sufficiently small perturbations of the principal coefficient map, by the same positive least singular value; no global arbitrary-coordinate invariance is being assumed. Along a path collect the derivatives of \(D\) through order three. Their derivative is a bounded linear system plus a forcing controlled by \(E\) through order three. Gronwall gives the claimed vanishing and its inhomogeneous version.

The degree-three kernel has dimension eight: importing M's *two*-prolongation closure is wrong here even after gauge fixing. The ungauged kernel dimensions are \(15,18,18,15,21\), differing by the arbitrary scalar-polynomial gauge dimensions \(3,6,10,15,21\). This matches (4.5). The exact computation tests the prolongations of the constrained equation, not arbitrary augmented Hessians. In a shrinking argument, if its analytic input gave \(\|E\|_{C^8}\le Cr^{3/2}\) on the source's monotone vertical paths, this new closure would bound \(D\) through order nine by \(Cr^{3/2}\). The initial ODE state now contains third derivatives. Such an analytic input is not established below.

### 4.3 An actual physical response embedding and its rigidity

Fix a small source ball \(E_0\Subset E\), and a connected source-free region containing a nonempty part of \(E\). Work over real sources, then complexify. Define
\[
\mathcal J_j(x)F=(P_{j,D}^{-1}F(x),\operatorname{div}P_{j,D}^{-1}F(x))\in\mathbb R^4,
\qquad \mathscr V_j(x)=\operatorname{rowspan}\mathcal J_j(x)
\subset\mathcal D'(E_0;\mathbb R^3).
\]
J112 makes \(\mathcal J_j(x)\) onto. Simultaneous jets make the four-planes at distinct points independent. The map to these four-planes is a local smooth immersion: if a direction \(\xi\) differentiated every row into its span, the differentiated scalar row would express \(\xi\cdot\nabla d\) in terms of \((u,d)\), impossible because \(\nabla d\) can be freely prescribed with \((u,d)\) fixed. Finite choices of sources witness this rank and give ordinary finite-dimensional Grassmann charts locally. Thus the comparison described next is an actual local smooth comparison, if the two response images coincide; it is not an abstract rank model.

**H115 (author proof; technical conditional rigidity).** Suppose on a connected open set there is a smooth local diffeomorphism \(\Phi\) and an invertible real matrix field \(B\) such that
\[
\mathcal J_2(x)F=B(x)\mathcal J_1(\Phi(x))F\quad\text{for every cap source }F, \tag{4.7}
\]
with \(\Phi=\mathrm{Id},B=I\) on a nonempty cap open set. Then \(\Phi=\mathrm{Id},B=I\) everywhere in that connected set and the two Lamé pairs agree there.

If equality of the two response images is given, construct \(\Phi\) by the inverse of the first local Grassmann chart composed with the second. Joint point separation makes it unique on overlaps. Four sources with invertible first value matrix give explicitly \(B=[\mathcal J_2F_\nu][\mathcal J_1(\Phi)F_\nu]^{-1}\), proving smoothness and uniqueness. This construction assumes image equality on an open set; mere contact of two smooth image manifolds is insufficient.

To prove rigidity, write the displacement block of (4.7) as \(u_2=A u_1(\Phi)+b d_1(\Phi)\), the scalar row as \(d_2=c\cdot u_1(\Phi)+s d_1(\Phi)\), and put \(J_{ai}=\partial_i\Phi_a\). Differentiate the displacement and impose its *actual* divergence. Freedom of \(\nabla d_1\) in the physical two-jets forces \(Jb=0\), hence \(b=0\). Freedom of the whole displacement gradient then forces
\[
JA=sI,\qquad A=sJ^{-1},\qquad c_q=\partial_iA_{iq}. \tag{4.8}
\]
Invertibility of \(B\) implies \(s\ne0\). These equations explicitly preserve displacement/divergence and exclude spurious scalar-to-vector mixing.

At any point, first set the displacement value and gradient to zero. Formal Lamé Hessians are exactly source-realizable, so substitution of the now known form \(u_2=A u_1(\Phi)\) gives kernel inclusion of two surjective principal maps. Hence for an invertible matrix \(T\),
\[
p_2(J^T\eta)A=T p_1(\eta).
\]
Taking determinants yields \((\eta^TJJ^T\eta)^3=c_0(\eta^T\eta)^3\). For real nonzero \(\eta\), positivity fixes the positive cube root; polarization gives \(JJ^T=\rho^2 I\). Thus \(\Phi\) is a Euclidean conformal local diffeomorphism.

For clarity, no arbitrary conformal gauge is being allowed. Let \(a=\log\rho\). Differentiating the conformal metric relation gives
\[
\partial_{ij}\Phi=a_i\partial_j\Phi+a_j\partial_i\Phi-
\delta_{ij}a_k\partial_k\Phi.
\]
Flatness of the pulled-back Euclidean metric in dimension three gives
\(\partial_{ij}a=a_i a_j-\frac12|\nabla a|^2\delta_{ij}\), by its Ricci tensor (take the trace first to obtain \(\Delta a=-|\nabla a|^2/2\)). These identities close an ODE along paths for \((\Phi,J,a,\nabla a)\). The cap values \((x,I,0,0)\) imply \(\Phi=x\) everywhere. Now (4.8) says \(u_2=s u_1\), \(d_2=s d_1+\nabla s\cdot u_1\).

Use J112 to prescribe at each point the constant-displacement two-jet \((u_1,\nabla u_1,\nabla^2u_1)=(e_q,0,0)\), which is a formal solution for every smooth Lamé pair. Substitution in the differentiated identity yields \(L_2(se_q)=0\) throughout the set, for each \(q\). Since constants solve \(L_2\), \((s-1)e_q\) solves it and vanishes in the cap. Physical UCP gives \(s=1\). This step also handles the exceptional ratio \(\lambda=\mu\); a first-order coefficient comparison alone would leave a degeneracy there. Finally physical source jets and (4.7) now have identical displacement components and coordinates; R112's main theorem gives constant proportionality. Cap equality of positive \(\mu\) fixes that constant to one. This proves H115 without its originally failed lambda-zero normalization shortcut.

H115 proves uniqueness and rigidity **once the open comparison exists**. It does not prove that the cap response image extends across an interior frontier. Compactness of a unitary fiber group, used in M, cannot be assumed for this general real comparison; in this route the rigidity already proved fixes any existing match to the identity, so a matched frontier has fixed physical coordinates and fiber map. What remains is extending the match, not selecting an arbitrary gauge at that frontier.

### 4.4 The physical sphere transfer and the unpaid analytic estimate

There is a more precise obstruction than the four missing two-jet coordinates. On a smooth small ball \(B\) let \(\Lambda_{j,B}\) be the physical displacement-to-traction map. Put \(\Sigma=\partial B\), \(H=\operatorname{div}\nu\), \(g_\nu=\nu\cdot g\), and \(g_T=g-g_\nu\nu\). The actual augmented boundary traces are exactly the graph
\[
(g,\mathcal T_{j,B}g),\qquad
\mathcal T_{j,B}g=\ell_j^{-1}
\{\nu\cdot\Lambda_{j,B}g+2\mu_j(\operatorname{div}_\Sigma g_T+H g_\nu)\}. \tag{4.9}
\]
Indeed \(\operatorname{div}u=\partial_\nu u_\nu+\operatorname{div}_\Sigma g_T+H g_\nu\), while \(\nu\cdot\sigma(u)\nu=\lambda\operatorname{div}u+2\mu\partial_\nu u_\nu\). Eliminate the normal derivative to get (4.9). Conversely the unique physical Dirichlet solution realizes every smooth \(g\) with precisely this divergence trace. The operator has order one. The graph is a proper subspace of the four-component trace space; no density in arbitrary four-component traces follows from physical Runge approximation.

At a frontier of an existing physical match the normalized principal parts on both sides are the same Euclidean Laplacian. Start with the physical Green matrix \(G_j\) and augment its two tensor factors by actual divergence:
\(\mathbb G_j=(I,\operatorname{div}_x)G_j(I,\operatorname{div}_y)^t\).
The transpose here denotes the operation on the second tensor factor, not a new independent inverse. On the cross where one point is matched, this is a mixed product solution for the two normalized rank-four operators. M's separate-system product extension construction applies at fixed separation: it uses scalar real principal metrics, commuting separate factors, UCP and compact-set bounds, not full-system sources. Its norm constants may depend on the positive separation. The physical constraints persist through each overlapping product extension. For example let \(Q_\beta=\operatorname{div}_x(\mathbb G_{1:3,\beta})-\mathbb G_{4,\beta}\). The normalized augmented equation and E's identity give \(m_1^{-1}P_{m_1,x}Q=0\). The second-variable system commutes with this first-variable differential expression, so \(\mathcal L_{2,y}Q=0\) too. Their sum is a smooth elliptic scalar-principal system on the product. The defect is zero on the nonempty seed open set; UCP for the sum makes it zero on each connected extension component attached to that seed. The overlap construction carries this identity onward, without an extra assumption on connected slices. Apply the same argument in the other factor. Thus the top \(3\times3\) block \(K\) satisfies the physical systems in both variables.

For a fixed positive sphere radius, use the actual physical Green flux
\[
S(y;u)=\int_\Sigma\{K(x,y)^t\sigma_1(u)\nu
-[\sigma_{1,x}(K)\nu]^t u\}\,dS_x. \tag{4.10}
\]
Its orientation is chosen to reproduce positive-\(P=-L\) Green evaluation on the known side. To differentiate in \(y\), first move to a fixed surrounding surface in the continued-kernel collar using physical Green's identity. The second physical equation then shows \(L_2S=0\), and adjoining \(\operatorname{div}_yS\) preserves divergence exactly. UCP from the known side reproduces every paired source solution. Transpose the physical ball DN operator in (4.10) onto the smooth kernel to obtain a smooth displacement density. Its \(y\) derivative represents the scalar output. For each fixed positive radius this is a genuine finite density and genuine physical transfer, not unrestricted augmented Cauchy data. This construction is conditional only on the accepted separated-kernel continuation covering the specified sphere; it makes no uniform bound as the radius goes to zero.

Represent an augmented transfer by a row \(\Psi=(\Psi_u,\Psi_d)\) on normalized sphere measure. On physical traces it depends only on
\(\Psi_u+\mathcal T_{1,B}^t\Psi_d\). Its exact annihilator is
\[
(-\mathcal T_{1,B}^ta,a). \tag{4.11}
\]
This is an infinite-dimensional, radius-dependent boundary differential/pseudodifferential subspace. When the output equation is differentiated as in M's `ang:P-equation`, testing against physical inputs says that the row residual is in (4.11); it does **not** say that it is zero. This identifies the missing analytic interface even though the principal Laplacian is fixed. Choosing a physical value frame does not remove (4.11).

The exact unpaid estimate is a uniform bounded representative of this physical transfer on M's shrinking sphere family (with the physical scaling of the divergence component), or an equivalent coercivity estimate on the quotient by (4.11), with all base commutator terms controlled. In one useful unscaled formulation it would give
\[
U_{2,F}(y)=\int\Psi_\delta(y,\omega)U_{1,F}(x_\delta(y,\omega))\,d\omega,
\qquad \sup_{0<\delta\le1}\|\chi\Psi_\delta\|_{L^2}<\infty, \tag{A*}
\]
where \(x_\delta(y,\omega)=\exp_y^\gamma(r_\delta(y)\omega)\) is the actual sphere parametrization used in the construction (Euclidean spheres give \(y+r_\delta(y)\omega\)). The estimate is required after a fixed, justified value/frame normalization, together with bounded cutoff-region derivatives and compatibility of the normalization with (4.5). Merely using the displacement density and differentiating it can cost \(r^{-1}\) in the scalar row. A nonphysical arbitrary extension of the transfer to all augmented inputs is no remedy: its output need not solve the second system. M's unrestricted coercivity cannot absorb an arbitrary residual (4.11).

If (A*) and its normalization are paid, Taylor expansion against the actual physical first jets permits a canonical decomposition (4.2): first jets have dimension 15, and \((Z,D)\) modulo the four gauges (4.5) have 15 unknown coefficients per output row. Fixed source jets therefore give a smooth local right inverse. The quadratic error is then controlled as in M, with the gauge correction included in \(Z\). F115 addresses the resulting normalized first-moment system, and H115 would remove the final zeroth-order comparison. The present work does not establish (A*) or all those uniform normalization bounds. This is the reason this route is a technical continuation bridge rather than P112.

## 5. Route B: the inaccessible collar and boundary signs

A115 supplies smooth common coefficients across an accessible cap. It does not make an arbitrary physical CGO displacement equal on the rest of the boundary, where its trace is generally nonzero. To enforce the measured trace support, fix \(\chi_\Gamma\in C_c^\infty(\Gamma)\) and solve the **physical** correction
\[
L_j z_j=0,\qquad z_j|_{\partial\Omega}=-(1-\chi_\Gamma)u_j|_{\partial\Omega},
\qquad w_j=u_j+z_j.
\]
This exists by coercive Dirichlet theory and has trace \(\chi_\Gamma u_j\). The exact bilinear error is
\[
\mathcal I(w_1,w_2)=\mathcal I(u_1,u_2)+\mathcal I(z_1,u_2)
+\mathcal I(u_1,z_2)+\mathcal I(z_1,z_2). \tag{5.1}
\]
None of the three correction terms vanishes from the data. The energy estimate is
\(\|z_j\|_{H^1}\le C_j\|(1-\chi_\Gamma)u_j\|_{H^{1/2}(\partial\Omega)}\); it is not a small weighted-CGO estimate.

The signs can be checked before attempting to use a boundary Carleman theorem. For a real linear weight \(\varphi=\alpha\cdot x\), zero-boundary smooth scalar \(v\), and
\(A=-\Delta-\tau^2|\alpha|^2\), \(B=2\tau\alpha\cdot\nabla\), direct integration by parts gives
\[
\|e^{\tau\varphi}(-\Delta)e^{-\tau\varphi}v\|^2
=\|Av\|^2+\|Bv\|^2-2\tau\int_{\partial\Omega}(\alpha\cdot\nu)|\partial_\nu v|^2. \tag{5.2}
\]
The sign reverses for \(-\varphi\); the potential cross term is a boundary integral of \(|v|^2\), hence zero. Componentwise summation gives the scalar-principal system boundary term, with lower-order interior terms to absorb. But the physical boundary condition \(u=0\) does **not** imply \((u,d)=0\) there. In fact
\[
d=\partial_\nu u_\nu=(\nu\cdot\sigma(u)\nu)/\ell,
\quad \sigma(u)\nu=\mu\partial_\nu u+(\lambda+\mu)(\partial_\nu u\cdot\nu)\nu.
\]
Thus applying a four-component zero-Dirichlet estimate to a physical correction drops an actual scalar boundary term. In addition, an arbitrary small patch on a ball does not contain the two non-glancing hemispheres for the opposite linear weights. A one-sign boundary construction for one phase cannot be used for its opposite phase without checking the input/output support again. This excludes the displayed unmodified construction; it does not rule out every possible nonlinear weight or other boundary strategy.

There is also an exact physical cutoff calculation. For a smooth cutoff \(\chi_t\) which vanishes in the distance-\(t\) boundary collar and is one outside distance \(2t\),
\[
\sigma_j(\chi_t u)=\chi_t\sigma_j(u)+Q_j,
\quad Q_j=\lambda_j(u\cdot\nabla\chi_t)I
+\mu_j(u\otimes\nabla\chi_t+\nabla\chi_t\otimes u),
\]
\[
L_j(\chi_tu)=\chi_tL_ju+\sigma_j(u)\nabla\chi_t+\operatorname{div}Q_j. \tag{5.3}
\]
For ordinary \(H^{-1}\), the commutator is bounded by
\(C t^{-1}\|u\|_{H^1(C_{2t})}\), using the divergence term in weak form. In an \(L^2\) estimate its bound is
\(C(t^{-1}\|\nabla u\|+t^{-2}\|u\|)\) in that collar. The actual augmented cutoff pair is
\[
(\chi_tu,\operatorname{div}(\chi_tu))
=\chi_t(u,d)+(0,\nabla\chi_t\cdot u). \tag{5.4}
\]
The final defect has size \(t^{-1}\|u\|\) and its differentiated equation costs further derivatives. These terms are absent only for genuine compact support, as in E, not because the collar volume tends to zero.

For E's supported augmented estimate, using the nonphysical cutoff \(\chi_t U\) is legal since the estimate itself covers every compactly supported augmented test. With \(W=e^{-\tau\theta\cdot x}U\), its exact conjugated commutator is
\[
e^{-\tau\theta\cdot x}[\mathcal L,\chi_t]U
=2\nabla\chi_t\cdot(\nabla W+\tau\theta W)
+(\Delta\chi_t)W+A^a(\partial_a\chi_t)W.
\]
Consequently, with \(h=1/\tau\), the elementary \(H_h^{-1}\le L^2\) bound gives
\[
h\|e^{-\tau\theta\cdot x}[\mathcal L,\chi_t]U\|_{H_h^{-1}}
\le C\{(h/t)\|\nabla W\|_{L^2(C_{2t})}
+(t^{-1}+h t^{-2}+h t^{-1})\|W\|_{L^2(C_{2t})}\}. \tag{5.5}
\]
The constants depend on fixed coefficient bounds and a fixed tubular chart, not on \(t,h\). No uniform smallness follows for *any* relation \(t=t(h)\) without collar control on \(W\); if physical cutoff compatibility is also wanted, (5.4) must be added. Formula (5.5) retains the entire cutoff error rather than naming a Carleman estimate without paying its boundary terms.

## 6. A joint limiting budget and exact location of the boundary gap

Let \(K_t=\{x:\operatorname{dist}(x,\partial\Omega)>t\}\), \(C_t=\Omega\setminus K_t\), taking small regular tubular levels. For physical CGO targets \(u_{j,\tau}\), supported-trace physical approximants \(w_{j,t,\eta,\tau}\), and errors \(\eta_j=\|w_j-u_j\|_{H^1(K_t)}\), write \(A_j=\|u_j\|_{H^1(K_t)}\). The whole-domain estimate, including the target tail omitted by a careless use of BUDGET, is
\[
|\mathcal I_\Omega(u_1,u_2)|\le\epsilon M_1M_2
+Cb(\eta_1 A_2+\eta_2 A_1+\eta_1\eta_2)
+|\mathcal I_{C_t}(w_1,w_2)|+|\mathcal I_{C_t}(u_1,u_2)|. \tag{6.1}
\]
It follows by adding and subtracting the two interior integrals and using \(\mathcal I_\Omega(w_1,w_2)\) from the data. This is valid jointly for every choice of the parameters, with no uniform Runge cost asserted.

The unknown signed collar term has an exact physical flux expression. Green's identity in \(C_t\) gives
\[
\mathcal I_{C_t}(w_1,w_2)=
\int_{\partial C_t}\{\sigma_1(w_1)n_{C_t}\cdot w_2
-w_1\cdot\sigma_2(w_2)n_{C_t}\}. \tag{6.2}
\]
On the exterior boundary the integrated expression is the measured pairing and is zero at exact data; on its inaccessible part both displacement traces are zero individually. The remaining inner-interface flux, with normal pointing toward \(K_t\), remains. Approximation to prescribed interior targets does not force this flux to be zero. Globally it is exactly the negative of the corresponding interior integral for the approximants. Thus no signed-cancellation shortcut follows from imposing zero displacement on the inaccessible boundary.

One may split \(C_t\) into an accessible smaller-patch collar and the rest. By A115, in the former \(b(x)\le C_N\operatorname{dist}(x,\partial\Omega)^N\) for every **fixed** \(N\). Hence its absolute contribution is at most \(C_N t^N\|w_1\|_{H^1}\|w_2\|_{H^1}\). There is no analogous bound in the rest, and no license to choose \(N\) growing with \(\tau\) without controlling \(C_N\). On the inaccessible flat-patch example B112 already forces individual energies of accurate collar approximants to grow at least like \(t^{-1}\). This lower bound disproves a uniform-energy approximation premise; it does not prove that every signed collar product stays large.

A sufficient missing boundary input is a sequence \(t(\tau)\downarrow0\), errors \(\eta_j(\tau)\downarrow0\), and actual supported-trace physical solutions for each of the physical transport/CGO tests required by E, such that jointly
\[
\eta_1A_2+\eta_2A_1+\eta_1\eta_2\to0,\qquad
\mathcal I_{C_{t(\tau)}}(w_1,w_2)\to0,\qquad
\mathcal I_{C_{t(\tau)}}(u_1,u_2)\to0,
\tag{B*}
\]
with the additional weighted cutoff terms (5.5) and physical defect (5.4) controlled if that supported-Carleman route is used. The physical CGO expansion's \(O(\tau^{2-N})\) divergence error must also be multiplied by every collar/trace loss before taking its limit. At exact data \(\epsilon M_1M_2=0\) for each finite approximant, however large its trace; at nonzero error it too must tend to zero. Even (B*) only pays the indicated transfer of test identities; use of E's transport comparison still requires its actual supported comparison or a proved replacement. I do not label this list equivalent to P112 or claim all its inputs are necessary.

This route does actual work: it constructs the cap, the supported-trace correction, the stress cutoff and divergence defect, derives the boundary signs, and identifies the whole signed collar flux. It does not close (B*). Known-collar K112 sets the approximant collar term exactly to zero by a coefficient hypothesis; it does not solve this problem.

## 7. Assessment and continuation decision

The strongest paid new bridge is F115 together with the exact annihilator (4.1) and the gauge (4.5). It replaces the vague finite-jet deficit by a fourth-order finite-type system with an exact certificate, while revealing the distinct infinite-dimensional trace obstruction (4.11). H115 constructs the only possible open physical source-space comparison and excludes spurious coordinates/fibers using actual jets, conformal flatness, and physical UCP. A115 legitimately supplies a common cap from exact local physical measurements. These are author-level **technical** deductions pending fresh review, not independently audited new theorems of arbitrary-patch uniqueness.

Their full-scope contribution reductions are concrete: A115 localizes E's boundary symbol and cap-pasting operations; F115 is finite tensor elimination followed by M's left-inverse/ODE operation, with a different exact principal matrix; H115 combines J112 with an explicit principal-symbol determinant and a closed conformal ODE and uses constant physical solutions to eliminate the scalar multiplier; (4.9), (5.1)–(6.2) are physical traction, product-rule and Green identities. No full-scope P112 reduction has been supplied, and no actual admissible pair refutes it. Conditional comparison rigidity and finite algebra do not count as a ninth substantial finding.

Continue Route A only toward a physical quotient angular estimate controlling (4.11), retaining its radius-dependent trace graph and the divergence normalization. There is a reason to try it: after its analytic input the previously unpaid local jet closure and comparison rigidity now have explicit mechanisms. Park the naive expanding-Runge/cutoff implementation of Route B: its support and collar residuals are exposed, and no joint estimate suppresses them. A new boundary construction could reopen that route. P112 and the earlier quantitative Q remain unproved/unrefuted here; no forced nomination.

## 8. Evidence scope

The owned evidence reuses I112's complete 13,223-entry tree, 749 manuscript directories and 10,373-original mapping by immutable reference. It does not copy the corpus or invoke any earlier verifier recursively. It checks the I112 seal directly, every bound artifact, the original Git blobs and all represented texts, including 776 inherited PDF texts, in one flat pass. Only `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` may drift; their owned snapshots remain immutable. AGENTS and source metadata are immutable references.

Exact inherited lexical expressions, matched lines, spans and multiplicities are replayed; the new lexical expression and its exact results are separately retained. Corpus lexical searches and TeX reading passages use Python `str.splitlines()`, with no appended newline when hashing joined passages. PDF passages use explicit LF splitting and preserve form feeds. Reading manifests distinguish complete operations, selected completed proof sections, and contract-only screens; unsuccessful or truncated tool output is not relabelled full semantic reading. The supplied originals are preserved without typography normalization.

`verify.py` is offline/read-only and run with `python3 -B`. It does not download, write, create bytecode, repair, or reseal. New PDF re-extraction is limited to Tan–Liu v1 and LNUW v1, each to stdout; inherited PDF texts are hash-bound without re-extraction. The exact finite diagnostics check (4.1), dimension 17, the integer prolongation matrices and the selected nonzero minor. The I112 original finite diagnostics are replayed directly once, not by invoking its recursive evidence workflow. Preseal validation is retained before one final seal. The final sealed invocation only reads and reports.

Failures retained include early oversized/truncated read outputs (follow-up complete reads are separately recorded), the invalid blank-thread-id lookup, missing optional SymPy (the recorded initial probe failed at import before any result; the final diagnostics use only standard-library exact arithmetic), the guessed Tan v3 URL 404, and the Wiley 403. Source identity, an exact finite-rank certificate, and successful replay do not certify the universal analytic proof, substantiality, human review, or worldwide priority.

### Source links

- [E, pinned full elasticity paper](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026)
- [M, pinned metric/connection patch paper](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026)
- [C, pinned scalar patch companion](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026)
- [Tan–Liu v1, boundary symbol and all-order recovery](https://arxiv.org/abs/2211.06650v1)
- [Lin–Nakamura v1, local physical boundary reconstruction](https://arxiv.org/abs/1708.00591v1)
- [Lin–Nakamura–Uhlmann–Wang v1, physical UCP](https://arxiv.org/abs/1005.3382v1)
- [Rüland–Salo v1, quantitative Runge and its collar hypotheses](https://arxiv.org/abs/1708.06307v1)
- [CJLT v1, structured partial elasticity](https://arxiv.org/abs/2609.20134v1)
- [DFS v2, reflected partial elasticity with different boundary conditions](https://arxiv.org/abs/1902.04838v2)
- [Li–Chen–Cheng, publisher entry; full proof unavailable in this run](https://onlinelibrary.wiley.com/doi/10.1002/mma.70764)
