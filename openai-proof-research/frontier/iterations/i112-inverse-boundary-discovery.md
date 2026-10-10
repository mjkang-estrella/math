# I112 — Fresh inverse boundary discovery

**Disposition: completed discovery/gap record; no ninth nomination.** The selected target is arbitrary same-patch uniqueness for both smooth static isotropic Lamé coefficients in three dimensions, without agreement near the inaccessible boundary. It remains unproved and unrefuted here. Two developed routes are recorded below. The strongest paid bridge is an exact characterization and explicit cubic lifting of the *physical* two-jets of the scalar-principal displacement–divergence system. It does not supply the unrestricted system jets required by the pinned connection proof.

All new positive statements below are **author proofs, technical**, awaiting the parent's independent review. None has independent original-proof PASS, contribution acceptance, human review, or formal certification. The source theorems and their lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. No upstream truth audit, contradiction synthesis, or ex-falso argument is used. Eight accepted findings remain eight. I110/I111 working outputs are neither read as dependencies nor bound. No children, shared-file edits, staging, commits, or publication were performed.

## 1. Exact screen and significance

Fix a known compact smooth manifold/bundle, or a known Euclidean domain, as specified separately below. These are not unknown-topology or multifrequency problems. The four targets were screened after reading the actual source contracts, the complete elasticity construction, the connection's physical-jet and matrix-moment interfaces, and the scalar shrinking bootstrap.

**Q: quantitative metric/connection recovery.** Fix a background metric (g_0) on a known compact connected (n)-manifold, (n\ge3), and a nonempty proper open patch \(\Gamma\). On the trivial rank-two Hermitian bundle, impose \(B^{-1}g_0\le g\le Bg_0\), \(\|g\|_{C^{50}}+\|A\|_{C^{50}}\le B\), in fixed charts/trivialization, with smooth coefficients. An exact proposed target is constants \(C,\alpha,\varepsilon_0>0\), depending only on this class and the fixed geometry/patch, such that

\[
 \inf_{\Phi|_\Gamma=\mathrm{Id},\,U|_\Gamma=I}
 \bigl(\|g_2-\Phi^*g_1\|_{C^0(g_0)}+
 \|A_2-U^{-1}\Phi^*A_1U-U^{-1}dU\|_{C^0(g_0)}\bigr)
 \le C[\log\log(e^e/\varepsilon)]^{-\alpha},
\]

for (0<\varepsilon<\varepsilon_0\), where \(\varepsilon\) is the operator norm of the difference of the density-valued, same-patch energy maps on the (H^{1/2}) closure of (C_c^\infty(\Gamma;\mathbb C^2)\). Infima range over smooth diffeomorphisms and unitary gauges, with no fixing condition on inaccessible boundary points. The displayed exponent and even this particular finite regularity class are **a target, not a conclusion**. The source has exact zero-error continuation: its shrinking radius is not measurement error, and its dilation is chosen for an already matched pair. Source jet right inverses, contact charts, separated-kernel continuation and conformal-factor removal have not been bounded in terms of this (B\). Interpolation of the source's exact moment estimate is not a noisy continuation theorem. No explicit modulus, including a Hölder one, is asserted or refuted for Q. Even qualitative compactness would additionally require injectivity on the chosen compact closure: a finite-C^50 bounded smooth class is not compact in the smooth topology. No such qualitative stability is asserted; a compactness-only consequence would in any case be technical.

**V: add an arbitrary Hermitian potential at one frequency.** On the same fixed trivial bundle, ask whether the zero-energy local map of (d_A^{*g}d_A+V\), with invertible Dirichlet realization, determines ((g,A,V)\) modulo only patch-fixing diffeomorphisms and unitary gauges. **Falsified as stated** by the conformal compensation in §3. This is outside the zero-potential source contract and creates no conflict with an accepted premise. Recovery modulo an enlarged conformal/potential gauge, or with additional frequency information, is a different target, not proved here.

**P112: selected remaining target.** For every bounded connected (C^\infty\) domain \(\Omega\subset\mathbb R^3\), every nonempty relatively open proper \(\Gamma\subset\partial\Omega\), and every two real smooth pairs
\[
 \mu_j>0,\qquad 3\lambda_j+2\mu_j>0\quad\text{on }\overline\Omega,
\]
does equality of their static energy forms for **all** vector-valued (f,h\in C_c^\infty(\Gamma)\), with displacement zero off \(\Gamma\), imply \(\lambda_1=\lambda_2,\mu_1=\mu_2\)? Fixed Euclidean coordinates and physical displacement/traction are used; there is no asserted diffeomorphism or internal-bundle gauge. This is stronger in access than the pinned full-boundary elasticity theorem. No collar, small shear gradient, analytic/quasianalytic, symmetry, or reflection hypothesis is inserted into P112.

**S: known-collar scalar quantitative recovery.** For smooth real nonnegative bounded Schrödinger potentials on a fixed smooth Euclidean domain in dimension at least three, whose difference is supported in fixed \(K\Subset\Omega\) with connected exterior, seek an (H^{-1}\) logarithmic stability estimate from the same-patch map, with constants depending on the domain, (K,\Gamma\), and the potential bound. This is already contained in [Rüland–Salo][RS], Proposition 6.1 (indeed under weaker regularity), and its proof and ending were read. Their stronger approximation for targets extending past the recovery set already supplies the improvement from exponential to polynomial approximation cost. This lane is not a substantial new result. The nonnegative restriction avoids any claim of spectral-gap-free uniformity for arbitrary signed potentials.

The named problem behind P112 is the **three-dimensional isotropic elastic Calderón inverse problem**, as explicitly discussed in [the pinned elasticity paper][E] and [Chen–Jiang–Liu–Tao, arXiv:2609.20134v1][CJLT]. The latter distinguishes recovery of the shear modulus from partial data from recovery of both moduli with full data. [Doll–Froehly–Schulz v2][DFS] uses reflection assumptions and a different inaccessible-boundary condition (simply supported; with a soft-clamped variant), and retains restricted conclusions. These observed scopes support relevance, not a priority ranking. The related [MathDB inverse-problems listing][DB] contains “Anisotropic Calderón conjecture at zero frequency” and an anisotropic-elasticity gauge problem; neither is represented here as exactly P112. The individual MathDB page failed in the browser retrieval; the fetched listing is the observed evidence.

## 2. Sources, companions, and the actual lower operations

Use the following immutable source names throughout:

- **E**: `Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026`. Its `introduction.tex`, Theorem `thm:main`, gives full static DN uniqueness on every bounded connected smooth Euclidean three-domain. All six substantive sections were read through their endings. `boundary-reduction.tex` constructs common extensions using **all** boundary jets, then glues arbitrary physical solutions using **all** tractions. `analytic-estimates.tex` adjoins actual divergence and pays the supported Carleman estimate. `physical-amplitudes.tex` realizes constrained rank-three transports by compatible recursion and physical correction, including (O(\tau^{2-N})\) divergence error. `transport-matching.tex` obtains bounded weighted transferred pairs, then supported planar comparisons and holomorphic dependence at fixed physical coordinates. `coefficient-recovery.tex` proves the conic-bundle rigidity and closes coefficient recovery by a finite-type ODE. We do not replace any of these steps by an unrestricted auxiliary matrix DN map.
- **M**: `Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026`. The main theorem is rank two, trivial bundle, zero potential, zero frequency, known manifold, same input/output patch. The full boundary/source section, matrix-moment section and final gauge/globalization section were read. In particular `bdy:evaluations` uses unrestricted scalar-principal system two-jets; `mat:spanning` and `mat:projected-equation` need arbitrary trace-free Hessians in **each** fiber component with vanishing gradient. The two prolongations and Gronwall argument in `mat:finite-type` and `mat:improvement` are accepted lower operations. `glob:conformal` uses absence of an additional potential to make a scalar conformal factor harmonic; it is not a theorem for unknown (V\).
- **C**: `Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026`. Main patch theorem and its scalar consequence were read in the introduction, and the entire `06-bootstrap.tex` was read. Its normalized discrepancy gains (r^{3/2}\) from exact source transfer and a fixed spanning family, with derivative order (m\ge\lceil10+3(10+n/2)\rceil\). This does not identify (r\) with noisy boundary data. M is the stronger coupled companion; scalar uniqueness cannot simply be applied to a matrix boundary map.

The complete pinned tree has **13,223 entries, 749 manuscript directories, and 10,373 original blob positions**. The I88 augmented map, reusing I14 and I79 originals, was copied only as a JSON index. It covers 9,340 I14 originals and 1,033 additional originals, including 776 PDF texts. All original Git blob and SHA-256 hashes were checked. Two full-domain lexical expressions produced **479 and 72 matched-line records**, preserving exact expressions, line text, match spans, and multiplicities. This is **full-domain lexical search, not full semantic reading**. Title/path and lexical screening found the three relevant smooth source families above and the rough-conductivity counterexample family; the latter's bounded-measurable category is not used against smooth premises. No recursive corpus copying or whole-corpus download was done. The live upstream HEAD response observed during this run equals the pinned commit, so no later upstream revision was observed.

External version checks observed DFS v2, CJLT v1, Rüland–Salo v1, and Lin–Nakamura v1 as their latest arXiv submissions in the retrieved metadata. The Rüland–Salo author-hosted PDF was also saved. Complete relevant Runge/SVD/local-data proofs were read through their endings. CJLT's exact hypotheses and its separation/quasianalytic partial-data proofs were read through their endings, including the need for full data in the last simultaneous-recovery step. DFS's contract was screened, not claimed as fully semantically read. The current Li–Chen(-Cheng) Lamé Runge publication was located, but the direct publisher retrieval returned HTTP 403 and no complete primary proof was obtained. Its abstract is discovery evidence only; **no quantitative Lamé Runge theorem or constants from it are used**. An institutional Imanuvilov–Yamamoto preprint was retrieved; its conditional-stability statements explicitly retain interior-distance dependence. We do not claim an audited new rate from that preprint.

## 3. A genuine gauge obstruction for V

**G112 (author proof; technical counterexample).** Let (n\ge3\), let (g\) be any smooth Riemannian metric on a compact manifold with boundary, and take (A=0,V_1=0\) on a trivial rank-two Hermitian bundle. Choose any real \(\omega\in C_c^\infty(M^\circ)\). Put
\[
 g_2=e^{2\omega}g,\quad \phi=(n-2)\omega/2,\quad
 V_2=-e^{-2\omega}(\Delta_g\phi+|d\phi|_g^2)I.
\]
Then the full zero-energy DN forms of ((g,0,0)\) and ((g_2,0,V_2)\) agree. Both Dirichlet realizations are invertible. For suitable \(\omega\ge0\), their metrics are not isometric even without a boundary-fixing requirement.

**Proof.** With \(\Delta_g=\operatorname{div}_g\nabla_g\), direct differentiation of the conformal Laplacian formula gives
\[
 (-\Delta_{g_2}+V_2)(e^{-\phi}u)
       =e^{-2\omega-\phi}(-\Delta_g u).
\]
Indeed the first-order terms cancel, and the remaining term before adding (V_2\) is (e^{-2\omega-\phi}(\Delta_g\phi+|d\phi|^2)u\). Multiplication by (e^{-\phi}\) bijects zero-Dirichlet kernels, so invertibility follows from that of (-\Delta_g\). It bijects the solutions with any prescribed boundary trace. All coefficients and the multiplier are unchanged in a boundary collar; hence normal derivatives, boundary densities and boundary energy pairings agree there. This proves full and therefore partial DN equality. On a Euclidean ball, choose nonzero \(\omega\ge0\) compactly supported in its interior. Its total metric volume increases strictly, excluding an isometry. Internal unitary gauges do not change metric volume. The proposed diffeomorphism/unitary-only conclusion is false. This construction neither adds a potential to the accepted source theorem nor audits that theorem. ∎

## 4. Route A: exterior sources and the physical-jet interface

Write (m=\mu\), (k=\lambda+\mu\), \(\ell=\lambda+2\mu\). Let (L=\operatorname{div}\sigma\) have the sign convention of E, and let (P=-L\) be its positive Dirichlet operator. The augmentation (R,S\) and the scalar operator (P_m=m\Delta+\nabla m\cdot\nabla\) are exactly E's equations `augmented-operators` and `augmented-identity`:
\[
 Lu=R(u,\operatorname{div}u),\qquad
 \operatorname{div}R(u,d)-S(u,d)=P_m(\operatorname{div}u-d).
\]
No equality of unrestricted augmented Cauchy data is assumed.

### A1. Quantitative cap transfer, with its actual prerequisite

**C112 (author proof; technical estimate).** Suppose two smooth admissible Lamé pairs on a fixed smooth enlarged domain (N\) coincide on an exterior cap (E=N\setminus\overline\Omega\), attached through (P_0\Subset\Gamma\), with common smooth extensions across the attachment. This prerequisite is weaker than agreement in an interior collar but includes exact compatibility of all jets at the attachment. Assume their energy forms on (H_0^1(N;\mathbb C^3)\) have coercivity at least (a>0\). Let (T\) bound restriction to (\partial\Omega\) from (H^1(N)\) in (H^{1/2}\). For (F\in C_c^\infty(E;\mathbb C^3)\), set (w_j=P_{j,D}^{-1}F\). Then, with the same-patch DN norm \(\epsilon\),
\[
 \|w_1-w_2\|_{H^1(E)}
 \le a^{-2}T^2\epsilon\|F\|_{H^{-1}(N)}. \tag{C112}
\]
The constant uses only the indicated coercivity and trace constants; coercivity can be bounded from the lower shear/bulk energy bounds and the fixed-domain Korn/Poincaré constants. No small-coefficient-difference assumption is needed. When \(\epsilon=0\), the physical (3\times3\) Dirichlet Green matrices agree on (E\times E\) away from the diagonal.

**Proof.** The first weak solution obeys \(\|w_1\|_{H^1_0(N)}\le a^{-1}\|F\|_{H^{-1}(N)}\). Its trace (f\) on the original boundary is supported in the attachment patch. Define \(\widetilde w\) by leaving (w_1\) unchanged on (E\) and replacing its restriction to \(\Omega\) by the second-medium harmonic extension of (f\). Matching traces make \(\widetilde w\in H_0^1(N)\). For any (v\in H_0^1(N)\), let (t\) be its original-boundary trace. The two interior energy contributions are \(\langle\Lambda_1 f,t\rangle\) and \(\langle\Lambda_2 f,t\rangle\); the exterior ones are equal. Thus
\[
 a_2(\widetilde w,v)-\langle F,v\rangle
       =\langle(\Lambda_2^\Gamma-\Lambda_1^\Gamma)f,t\rangle.
\]
Both traces are supported in \(\Gamma\). The right side is bounded by \(\epsilon T^2a^{-1}\|F\|\|v\|_{H^1}\). Subtract the weak equation for (w_2\) and apply coercivity. On (E\), \(\widetilde w=w_1\), proving C112. At zero error, all smooth source responses agree; the Schwartz kernel identity and off-diagonal elliptic regularity give Green-matrix equality. This argument is the energy replacement in M/E with an explicitly retained residual. It does not produce the common cap from noisy boundary jets. ∎

### A2. Exact attainable physical jets

**J112 (author proof; technical).** Let (N\subset\mathbb R^3\) be a bounded connected smooth domain with smooth admissible Lamé coefficients, and (E_0\Subset N\) a nonempty open source set. At any finite set of distinct points outside \(\overline E_0\), the jets through order (s\ge2\) of (P_D^{-1}F\), (F\in C_c^\infty(E_0;\mathbb C^3)\), fill exactly the direct sum of the formal solution-jet spaces
\[
 \partial^\alpha Lu(p)=0\quad (|\alpha|\le s-2).
\]
Values and first jets are unrestricted. In particular, the two-jets of physical pairs ((u,d)=(u,\operatorname{div}u)\) at a source-free point fill exactly
\[
 R(u,d)(p)=0,\quad S(u,d)(p)=0,\quad
 d(p)=\partial_i u_i(p),\quad
 \partial_a d(p)=\partial_a\partial_i u_i(p),\quad a=1,2,3. \tag{J112}
\]
This space has complex dimension **32**, whereas all formal two-jets of the unconstrained four-component augmentation have dimension **36**. The algebraic lift below has explicit coefficients depending on (m(p)^{-1},k(p)\) and finite coefficient jets. Realization by remote sources has no quantitative source-norm estimate here.

**Proof of finite-jet surjectivity.** A functional annihilating all these source jets is a vector distribution (T\) of order at most (s\), supported at the chosen points. Distributional transposition gives (v=P_D^{-1}T\), zero on (E_0\), and (Pv=T\). Away from the finite support, elasticity open-set unique continuation implies (v=0\), since a connected three-domain remains connected after removing finitely many points. This UCP follows from E's scalar-principal augmentation, with actual divergence, and the ordinary smooth scalar-principal system UCP used in M. Therefore (v\) is point-supported. If its highest derivative order is (r\), its image has exact highest order (r+2\): its leading vector polynomial is multiplied by
\[
 m|\xi|^2 I+k\xi\xi^T.
\]
This polynomial matrix is injective on vector polynomials. Its determinant is a nonzero polynomial (it is positive for real nonzero \(\xi\)); multiplication by the adjugate proves injectivity in the polynomial integral domain. Thus (r\le s-2\). Consequently the annihilator consists exactly of linear combinations of the point functionals \(\partial^\alpha Pu(p)\), \(|\alpha|\le s-2\). Finite-dimensional duality proves surjectivity, including simultaneous jets. For (s=0,1\), the same order argument leaves no nonzero annihilator. This is the point-distribution construction of M, with the actual Lamé principal symbol checked, not an appeal to unrestricted augmented sources.

**Proof of the physical two-jet range.** Necessity of J112 follows from the displayed compatibility identity. For sufficiency, prescribe a two-jet ((u,d)\) obeying J112. We must extend the prescribed (u\) two-jet to a three-jet with prescribed Hessian (B=(\partial_a\partial_b d)\), satisfying (Lu=0\) and its three first derivatives. At the point, write the latter equations as
\[
 m A_{is}+k B_{is}+F_{is}=0,\qquad
 A_{is}=\partial_s\Delta u_i,
\]
where (F\) is explicitly the part of \(\partial_s Lu_i\) obtained by differentiating a coefficient; it depends only on the already prescribed (u\) two-jet and the coefficient two-jet. Set (A=-(kB+F)/m\). The trace compatibility required for a cubic displacement is \(\operatorname{tr}A=\operatorname{tr}B\). To check it without discarding variable-coefficient terms, direct differentiation of E's physical operator gives
\[
 \operatorname{tr}F=2\nabla k\cdot\nabla d+2\nabla m\cdot\Delta u
   +2\sum_{i,q}(\partial_i\partial_qm)\partial_i u_q+(\Delta\lambda)d.
\]
Here the prescribed zero/first defect jets justify substituting (d=\operatorname{div}u) and its first derivatives. This expression is exactly the part of (S(u,d)(p)) not containing the Hessian of (d). Thus the assumed scalar equation in J112 says
\[
 \ell\operatorname{tr}B+\operatorname{tr}F=0.
\]
Since (A=-(kB+F)/m), this implies (m\operatorname{tr}A=-k\operatorname{tr}B-\operatorname{tr}F=m\operatorname{tr}B). The required trace compatibility is now established before constructing any third derivatives.

Here is the promised explicit lift, valid in every (n\ge2\). For any linear vector polynomial (a(x)=Ax\) and quadratic scalar polynomial (b(x)=\tfrac12 x^TBx\) with \(\operatorname{div}a=\Delta b\), put
\[
 v_0=\frac{|x|^2a(x)}{2n+4},\quad h=b-\operatorname{div}v_0,
\]
\[
 v=v_0+\frac{n+2}{n(n+4)}
       \left(xh-\frac{|x|^2\nabla h}{n+2}\right). \tag{L112}
\]
The function (h\) is harmonic because \(\Delta v_0=a\). Homogeneity gives
\[
 \Delta(xh)=2\nabla h,\quad
 \Delta(|x|^2\nabla h)=(2n+4)\nabla h,
\]
\[
 \operatorname{div}(xh)=(n+2)h,\quad
 \operatorname{div}(|x|^2\nabla h)=4h.
\]
Thus \(\Delta v=a\) and \(\operatorname{div}v=b\). This homogeneous cubic has exactly the required third-derivative contractions and changes no lower jet. Its coefficient norm is at most (C_n(|A|+|B|)\), directly from its displayed finite formula. Add it to the prescribed Taylor polynomial. The finite-jet surjectivity just proved at (s=3\) realizes this full jet by a source solution. Its physical divergence has precisely the prescribed two-jet.

For the dimension count, (u\) has 30 two-jet coordinates. The three independent equations (Lu=0\) leave 27. The value and gradient of (d\) are fixed by (u\); its six Hessian coordinates obey one independent scalar equation, leaving five. Total: 32. For the unconstrained augmentation, 40 coordinates obey four independent second-order equations, leaving 36. Smooth source choices spanning any one fiber can be fixed finitely and retain rank in a neighborhood, but their conditioning is a property of the chosen sources, not an a priori quantitative bound. ∎

### A3. What physical jets can recover, and what they cannot replace

**R112 (author proof; technical local rigidity).** On a connected open set (W\subset\mathbb R^3\), suppose that at every point every formal two-jet satisfying (L_1u=0\) also satisfies (L_2u=0\), in the **same physical coordinates and displacement components**. For smooth admissible pairs, there is a positive constant (c\) with \((\lambda_2,\mu_2)=c(\lambda_1,\mu_1)\) on (W\). Equality of one coefficient at one point fixes (c=1\).

**Proof.** First set all lower jet coordinates to zero. The two principal maps from symmetric vector Hessians onto \(\mathbb C^3\) have the first kernel contained in the second, so the second map is (T\) times the first. Surjectivity follows by prescribing the Hessian with all second derivatives in one fixed real direction and using its invertible principal symbol. Consequently for every real \(\xi\ne0\),
\[
 m_2|\xi|^2I+k_2\xi\xi^T
 =T(m_1|\xi|^2I+k_1\xi\xi^T).
\]
For (v\perp\xi\), this gives (Tv=(m_2/m_1)v\). Every real vector is perpendicular to some nonzero real vector, so (T=cI\), (c=m_2/m_1\), and then (k_2=ck_1\). Thus \(\lambda_2=c\lambda_1,\mu_2=c\mu_1\) pointwise, with smooth positive (c(x)\). For arbitrary lower jets choose a Hessian making (L_1u=0\). The differential expression satisfies
\[
 L_2u-cL_1u=\sigma_{\lambda_1,\mu_1}(u)\nabla c.
\]
The gradient of (u\) is unrestricted; choose it to be (I\). Its stress is ((3\lambda_1+2\mu_1)I\), a nonzero scalar matrix. Hence \(\nabla c=0\). Connectedness finishes. This argument does not assume, or establish, that partial DN equality matches these jets in the interior. ∎

The missing step is substantive. Even for constant coefficients, (U=(0,1)\) solves the augmentation but is not a physical displacement–divergence pair. With zero **augmented** value and gradient, physical Hessians satisfy both componentwise trace constraints and
\[
 \sum_i \partial_a\partial_i u_i=0\quad(a=1,2,3).
\]
Their dimension is **17**, instead of the 20 trace-free four-component Hessians used by a scalar-principal system. For example (H^1_{12}=H^1_{21}=1\) with all other components zero is trace-free but violates the (a=2\) constraint. The extra scalar component can supply a physical value frame (J112 allows arbitrary (u(p)\) and \(\operatorname{div}u(p)\)), but such a frame does not remove the codimension-four differential constraint. Frame changes preserve that codimension.

Consequently M's `mat:projected-equation` cannot be applied to the physical source family: its prescribed (H_se_\alpha\) tests are not all attainable. A viable continuation argument would have to propagate physical Green data across an interior frontier while preserving the divergence relation, then obtain a displacement/coordinate comparison to which R112 applies. Neither C112 nor J112 produces this continuation or excludes nonphysical first-moment directions. This is the precise unresolved Route A input. It is not the assertion that all scalar-principal systems are covered by M.

## 5. Route B: physical Runge transfer, its complete restricted closure, and its cost

This route keeps the physical system throughout. It first asks whether partial data can recover the full bilinear identity used by E. There is a complete result when the coefficient difference stays in a fixed interior set; this is a lower-operation reduction, not P112.

**K112 (author proof; technical restricted theorem).** Let \(\Omega,\Gamma,\lambda_j,\mu_j\) satisfy P112. Suppose there are a compact (K\) and a smooth domain (D\) with
\[
 K\Subset D\Subset\Omega,\qquad \Omega\setminus\overline D\text{ connected},
 \qquad (\lambda_1,\mu_1)=(\lambda_2,\mu_2)\text{ on }\Omega\setminus K.
\]
Then equality of same-patch static maps implies equality of both coefficients everywhere. The topology condition is explicit; we do not silently assume that collars of different boundary components are connected.

**Proof.** For a single medium, the restrictions to (D\) of physical solutions with smooth boundary traces supported in \(\Gamma\) are dense in the restrictions of all smooth solutions on \(\Omega\), in (L^2(D)\). Indeed, if (F\in L^2(D;\mathbb C^3)\) annihilates the former, solve (P_D^{\Omega}w=1_DF\) with zero boundary displacement on \(\Omega\). Green's identity gives zero traction on \(\Gamma\). In \(\Omega\setminus\overline D\) the equation is homogeneous. Boundary Cauchy uniqueness and open-set UCP give (w=0\) throughout this connected exterior. To see boundary Cauchy uniqueness, extend the smooth coefficients across a smaller patch and extend (w\) by zero: zero displacement and traction eliminate the interface distribution, after which the same UCP applies. Thus (w\) is supported in \(\overline D\). Distributional integration by parts against any smooth global homogeneous solution gives \(\langle F,u\rangle_D=\langle Pw,u\rangle=\langle w,Pu\rangle=0\). Hilbert-space orthogonal-complement duality proves density. Interior elliptic estimates upgrade convergence to (H^1(K)\), using its positive distance from \(\partial D\).

For first-medium (u\) and second-medium (v\) define
\[
 \mathcal I(u,v)=\int_\Omega
  (\lambda_1-\lambda_2)\operatorname{div}u\operatorname{div}v
  +2(\mu_1-\mu_2)e(u):e(v)\,dx. \tag{I112}
\]
Use complex bilinear pairings, extending the real symmetric maps complex linearly. The weak equations and symmetry show that this is
\(\langle(\Lambda_1-\Lambda_2)\operatorname{tr}u,\operatorname{tr}v\rangle\): in the first energy form the second solution may be replaced by the first-medium solution with its trace; in the second form the analogous replacement is valid. Supported traces therefore give \(\mathcal I=0\). Approximate arbitrary smooth global (u,v\) in (H^1(K)\) by supported solutions in their respective media. Since the integrand is supported in (K\), continuity of the bilinear integral gives \(\mathcal I(u,v)=0\) for arbitrary smooth boundary values. Thus the full maps agree by density, and E's accepted full theorem gives coefficient equality. Every step is explicit and stays in the physical displacement system. ∎

**B112 (author proof; technical boundary-cost obstruction).** Suppose a smooth domain contains a flat boundary cylinder (Q\times(0,t_0)\), with (Q\subset\mathbb R^2\) of finite positive area and (Q\times\{0\}\) contained in the inaccessible open boundary. For (0<t<t_0/2\), every (v\in H^1(Q\times(0,2t);\mathbb C^3)\) of zero trace on its base that satisfies
\[
 \|v-e_1\|_{L^2(Q\times(t,2t))}\le\tfrac12\sqrt{|Q|t}
\]
obeys
\[
 \|\partial_3v\|_{L^2(Q\times(0,2t))}^2\ge\frac{|Q|}{8t}. \tag{B112}
\]
The assertion applies in particular to constant-coefficient Lamé Runge approximants of the actual solution (u=e_1\).

**Proof.** On almost every vertical fiber, the trace condition and the one-dimensional fundamental theorem for (H^1\) functions give
\(|v(y,s)|^2\le s\int_0^s|\partial_3v(y,r)|^2dr\). Integrating over (Q\times(t,2t)\) bounds its squared norm by (2t^2\|\partial_3v\|^2\). The triangle inequality and the assumed error bound give that squared norm at least (|Q|t/4\). Combine. Smooth bounded domains with such a flat patch exist; rounding the boundary away from a smaller cylinder leaves this argument unchanged. Global (H^1\) approximation of (e_1\) by supported traces is impossible even without a rate, because continuity of the trace map would force its trace to vanish on that inaccessible patch. B112 gives a quantitative interior-collar version of the obstruction. It does **not** disprove P112 or every possible Runge strategy. ∎

The exact error budget makes the remaining issue visible. Let (w_j\) be supported-trace homogeneous solutions, approximating homogeneous target solutions (u_j\) on an interior set (K\), and put
\(\eta_j=\|u_j-w_j\|_{H^1(K)}\), \(A_j=\|u_j\|_{H^1(K)}\), \(M_j=\|\operatorname{tr}w_j\|_{H^{1/2}}\). If (b=\|\lambda_1-\lambda_2\|_\infty+\|\mu_1-\mu_2\|_\infty\), then
\[
 |\mathcal I_K(u_1,u_2)|\le
 \epsilon M_1M_2+C b(\eta_1A_2+\eta_2A_1+\eta_1\eta_2)
 +C b_{\Omega\setminus K}
 \|w_1\|_{H^1(\Omega\setminus K)}\|w_2\|_{H^1(\Omega\setminus K)}. \tag{BUDGET}
\]
Here (b_{\Omega\setminus K}\) is the same coefficient-difference bound restricted to that set, and (C\) depends only on dimension. To prove this estimate, use I112 for (w_1,w_2\), split its integral into (K\) and its complement, and expand the two factors in (\mathcal I_K(u_1,u_2)-\mathcal I_K(w_1,w_2)\). Cauchy–Schwarz, (|\operatorname{div}w|\le\sqrt3|\nabla w|\) and (|e(w)|\le|\nabla w|\) give every displayed term. No unstated uniform Runge constant occurs in this inequality.

K112 sets the last term exactly to zero. P112 does not. On an inaccessible collar the coefficient difference is not known to vanish, even to first order. B112 prevents bounding the approximant energies uniformly while moving the recovery set to that boundary. A small collar volume alone does not bound this energy product. Rüland–Salo's full quantitative proof likewise uses a fixed recovery region and an exactly zero outside coefficient difference; even its polynomial-cost version has geometry-dependent constants. No quantitative system version is silently imported. In the pinned CGO route, lack of global exterior matching also removes the compact support of the displacement–divergence difference needed in E's supported Carleman estimate. The unresolved Route B input is a **physical boundary-to-interior comparison controlling the inaccessible-collar term (or a replacement boundary Carleman construction) uniformly in the approximation, collar and CGO parameters**. Merely sending the approximation error to zero is not this input.

## 6. Contribution assessment and evidence contract

The algebraic lift L112 is an actual construction, and C112 retains an actual data-error estimate. J112 pinpoints the realizable jet space and R112 proves what that space would determine after an identity comparison. But their full scope is reproduced by accepted distributional jet duality, the explicit Laplacian/divergence polynomial right inverse, elementary principal-symbol algebra, and the accepted augmentation. K112 reduces completely to physical Runge duality, the elastic integral identity and E. G112 is the classical conformal conjugation mechanism with its exact potential and normalization written out. B112 is a one-dimensional energy estimate. These are **technical results**, not a split of an accepted finding or a substantial nomination. There is no claim that classical tools automatically make a result insubstantial; here the complete reductions are given.

P112 needs the additional constrained continuation or controlled boundary construction stated above. Q additionally needs noisy chart/gauge recovery and a uniform source-conditioning/continuation budget before any shrinking argument can be optimized. Neither target is replaced by a conditional theorem credited as a finding.

Evidence lives only in `frontier/sources/i112_inverse_boundary_discovery/` and `frontier/experiments/i112_inverse_boundary_discovery/`, plus this report. `read-manifest.json` records exact source paths, versions, hashes, labels and read passages. Original corpus representations and originals are immutable references, not copied corpora. The four allowed drifting ledgers are used via frozen snapshots; live AGENTS and immutable source metadata are checked. The line conventions are explicitly **Python `str.splitlines()` for original corpus lexical searches/TeX passages**, and **LF splitting for newly extracted PDF text passages**; form-feed page separators are retained. No line-number convention is silently exchanged.

`verify.py` is offline and read-only: no downloads, writes, bytecode, repairs, or resealing. It checks exact owned inventory, hashes of all original positions and represented texts, exact lexical multisets, passage hashes, and 84 rational cubic-basis tests plus the finite jet-dimension checks. It selectively re-extracts only the Rüland–Salo and CJLT PDFs to stdout for byte comparison; it does not re-extract the 776 inherited PDF texts or recursively invoke earlier verifiers. `validation.json` records pre-seal validation. One final seal binds that result and all other owned artifacts; the final invocation checks the seal without modifying it. Retained failures include initial wrong-cwd reads, a missing optional HTML parser, the publisher 403, an initial coordinate/path filter corrected before corpus screening, and the MathDB browser page error. They were retrieval/orchestration failures, not repaired mathematical proof failures.

Passing evidence replay identifies source bytes and checks the specified finite algebra. It is not a universal proof verifier, contribution certification, human review, or worldwide-priority claim. The parent should review J112's variable-coefficient compatibility and both route gaps independently before using any of these technical deductions.

[E]: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026
[M]: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026
[C]: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026
[CJLT]: https://arxiv.org/abs/2609.20134v1
[DFS]: https://arxiv.org/abs/1902.04838v2
[DB]: https://mathdb.com/database?tag=inverse-problems
[RS]: https://arxiv.org/abs/1708.06307v1
