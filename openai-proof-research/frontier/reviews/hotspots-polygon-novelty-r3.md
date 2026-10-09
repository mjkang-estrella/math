# Hot spots on simply connected polygons: novelty and prior-art review, round 3

Date: 2026-10-08. Object of review: `frontier/reviews/hotspots-multiplicity-r2.md` (the "multiplicity report"), read with `frontier/reviews/hotspots-review-r2.md`. Corpus revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; family 369 `thm:main` is accepted as true, as the user instructed. The scope is three claims: Statement P, surjectivity of the traceless shape derivative at double polygonal eigenvalues, and reachability of every eigenline as the lower branch. I also sanity-checked the proof.

Writes: this file and `frontier/sources/hotspots_polygon_novelty_r3/` only (PDFs, text extractions, `manifest.json` with URLs and SHA-256 hashes, plus the search list). No shared-file edits, staging, commits, or nested agents.

**Parent integration note (2026-10-08):** all ten cached PDF hashes and sizes were verified, and Marrocos–Pereira Lemma 2 and Theorem 9, case ii, were checked in the primary text. One precision correction applies wherever this review paraphrases Lemma 2: its printed assertion that one whole boundary function vanishes is too strong for arbitrary $C^2$ functions (nonzero smooth functions with disjoint supports are counterexamples). The displayed gradient-flow proof establishes the sufficient pointwise conclusion $f(x)g(x)=0$ for every boundary point. For eigenfunction traces, a nonzero trace on a patch then forces the other trace to vanish on that patch, and Neumann data plus boundary Cauchy uniqueness give the contradiction. Thus the prior-art mechanism and the polygon argument stand; no global vanishing assertion for arbitrary boundary functions is needed. The parent adopted the demotion recommendation and corrected the candidate report. The separate proof review is still pending.

## Verdict

**Mathematics: I accept the polygon theorem (Theorem E plus the §6 conclusion), with minor presentational repairs.** I found no gap at reentrant vertices, at the $3\pi/2$ resonance, or in the multiplicity handling. See §4.

**Novelty: this is a careful, competent extension of a known mechanism. It is not a genuinely new significant advance.** Here is how the claims decompose:

| Claim | Status in the literature | Genuinely new content |
|---|---|---|
| Statement P on smooth boundaries | **Known.** It is Uhlenbeck's lemma: if $\nabla_{\partial\Omega}f\cdot\nabla_{\partial\Omega}g-\lambda fg=0$ on a compact $C^2$ boundary, then $f$ or $g$ vanishes there. It is stated and proved as Lemma 2 of Marrocos–Pereira (arXiv:1310.5178), any dimension. | None |
| The polarization $h=f+g$, $k=f-g$ that turns the diagonal-difference condition into a cross-stress condition | **Known.** It is the same step as Marrocos–Pereira, proof of Theorem 9, "case ii". Gomes–Marrocos (arXiv:1510.07067), proof of Theorem 2, uses the analogue $\eta=\varphi+\psi$, $\xi=\varphi-\psi$ for metrics. | None |
| Surjectivity onto $\mathrm{Sym}_0(E)$ (codimension 2 / "SAH2" for double eigenvalues) as a target property | **Known framework.** Arnold, Colin de Verdière; Lupo–Micheletti 1993 for Dirichlet $C^3$ domains (secondary citation); Micheletti–Pistoia and Gomes–Marrocos Theorem 2 for metrics with Neumann boundary; Teytel 1999 abstract version. For smooth Neumann domains it follows in two lines from Uhlenbeck's lemma plus the Hadamard formula. | None in the smooth case |
| Statement P **at polygon vertices** (convex corners, and reentrant corners via two-edge averaging) | **No published polygon/corner version found** in a bounded search (§3). It uses standard Bessel sector expansions (Judge–Mondal 2020, §4, eqs. (6) and (10)) and the standard parity $\cos(n\nu\beta)=(-1)^n$. | **Yes, but small:** a roughly half-page endpoint lemma, $hk=0$ at every vertex |
| Lower-branch selection of a prescribed eigenline, given surjectivity | **Standard.** First-order degenerate (Rellich–Kato) perturbation: the one-sided derivatives of a double eigenvalue are the eigenvalues of the boundary matrix (e.g. Marrocos–Pereira Theorem 5/Corollary 1 for Neumann smooth domains). The one-sided-$t$ variational proof in the report is correct but routine. | None beyond writing it out |
| Generic simplicity for polygons | **Known and weaker.** Hillairet–Judge, Proc. AMS 137 (2009), Theorem 1.1: almost every simply connected $n$-gon, $n\ge4$, has simple Dirichlet/Neumann spectrum. The proof uses analytic continuation from an irrational rectangle (Cor. 2.2, Prop. 2.3), with **no** transversality. It gives no per-eigenline control. | The report correctly says that generic simplicity does not imply per-line control (§2) |
| Conditional strict hot spots for **every** eigenfunction on **every** simply connected polygon | No published identical statement found. It is a composition of (a) the accepted corpus theorem, (b) the classical spectral transfer already judged routine in round 2, (c) the corner lemma, and (d) standard perturbation theory. | **New to this project; a corollary-level extension** |

So the honest attribution is: **"Uhlenbeck's boundary lemma, extended to polygons by a short vertex analysis, gives Arnold-type transversality for double Neumann eigenvalues of polygons. Standard perturbation theory then gives eigenline selection."** The one new mathematical item is the vertex endpoint lemma. Its two-edge averaging trick is neat but elementary: at $\beta=3\pi/2$ one can equally sum the two single-edge identities (see §4.2). It is not a new proof mechanism of the kind the user requested. **Recommendation: record it as a technical lemma and a corollary that is new to this project. Do not present it as a significant novel MathDB advance.** The importance tier stays at the named (not celebrated) hot-spots target and is further diluted by the fact that the hard input is the accepted corpus theorem.

The report already disclaims literature priority. That disclaimer should now be strengthened: the smooth half of Statement P and the polarization step have a **specific prior source**. The report's phrasing "may overlap known shape-derivative folklore" understates this.

## 1. Sources actually inspected

All are cached with hashes in `../sources/hotspots_polygon_novelty_r3/manifest.json`. Round-2 caches were reused where noted.

1. **L. Hillairet, C. Judge, *Generic spectral simplicity of polygons*, Proc. AMS 137 (2009) 2139–2145; arXiv:math/0703616v3.** Theorem 1.1 covers $n\ge4$, almost every $P\in\mathcal P_n$, Dirichlet and Neumann. Lemma 2.1 gives analytic dependence under uniformly bi-Lipschitz analytic families. Corollary 2.2: simplicity at one $t_0$ implies simplicity for all but countably many $t$. Proposition 2.3 is a Fubini argument. §3 exhibits a rectangle with $(s_1/s_2)^2\notin\mathbb Q$. The paper contains **no** shape derivative, no corner expansion, and no transversality. The intro credits Uhlenbeck building on Albert for generic simplicity of smooth domains and metrics. **It does not anticipate Statement P or per-line selection.**
2. **L. Hillairet, C. Judge, *The eigenvalues of the Laplacian on domains with small slits*, arXiv:0802.2597** (TAMS 2010). It extends generic simplicity to multiply connected polygons via slit degeneration. Same mechanism, again no transversality.
3. **C. Judge, S. Mondal, *Euclidean triangles have no hot spots*, Ann. Math. 191 (2020) 167–211** (round-2 cache). The relevant items:
   - §4, eq. (6), p. 179: the sector expansion $u=\sum c_n r^{n\nu}g_{n\nu}(r^2)\cos(n\nu\theta)$ for any sector angle $\beta$, with Neumann conditions on the two rays.
   - eqs. (9)–(12), p. 180: termwise $\partial_\theta$, $\partial_r$ derivatives.
   - Lemma 5.1, Theorem 5.2, Corollary 5.3, and **Corollary 5.4** (p. 183): multiplicity at most 2 for second Neumann eigenfunctions of a simply connected polygon, proved via the vertex map $u\mapsto(c^v_0,c^v_1)$. It is described there as a consequence of Nadirashvili 1986.
   - §12, Lemma 12.2: crossing of analytic branches along a path of triangles.
4. **C. Judge, S. Mondal, *Erratum: Euclidean triangles have no hot spots*, arXiv:1802.01800v5** (Ann. Math. 195 (2022) 337–362 per citing literature; I did not open the journal version). The erratum says **Lemma 3.4 is false as stated**, so Lemma 7.6 is unproven. The incomplete list is Theorem 1.1 (acute case, re-proved there as Theorem A), Thm 7.7, Cor 7.8, Prop 10.5, Lemma 11.2, Thm 13.1, Cor 13.2, Prop 13.3, Thm 13.4, and Cor 13.5. **§4 and Corollary 5.4 are not affected**, so the report's use of them stands. Lemma 3.4 is not used, as the report correctly states.
5. **M. A. M. Marrocos, A. L. Pereira, *Eigenvalues of the Neumann Laplacian in symmetric regions*, arXiv:1310.5178v1 (2013).**
   - **Lemma 2** (§5.1), introduced as "a technical result due to Uhlenbeck": for $\Omega\subset\mathbb R^n$ bounded and $C^2$, $\lambda>0$, and $f,g\in C^2(\partial\Omega)$, the identity $\nabla_{\partial\Omega}f\cdot\nabla_{\partial\Omega}g-\lambda fg=0$ on $\partial\Omega$ forces one function to vanish on $\partial\Omega$. The proof uses the boundary gradient flow of $f$ and exponential growth of $g$.
   - **Proof of Theorem 9:** the Hadamard matrix is $M_{ij}=\int_{\partial\Omega}\sigma(\nabla\phi_i\cdot\nabla\phi_j-\lambda_0\phi_i\phi_j)$. In "case ii" the condition $|\nabla\phi_i|^2-\lambda\phi_i^2=|\nabla\phi_j|^2-\lambda\phi_j^2$ is rewritten with $\psi^\pm=\phi_i\pm\phi_j$ as a cross-stress identity and killed by Lemma 2.
   - Theorems 4–5 and Corollary 1: analytic branches whose first derivatives are the eigenvalues of $M$.
   
   This is the report's §3.1 plus §4, verbatim in structure, for $C^2$ boundaries. (With Neumann conditions, $\nabla\phi_i\cdot\nabla\phi_j=\nabla_{\partial\Omega}\phi_i\cdot\nabla_{\partial\Omega}\phi_j$ on the boundary.)
6. **J. N. V. Gomes, M. A. M. Marrocos, *On eigenvalue generic properties of the Laplace–Neumann operator*, arXiv:1510.07067v4.**
   - Remark 2 defines SAH2: $f_{11}-f_{22}$ and $f_{12}$ are linearly independent. For a double eigenvalue this is exactly surjectivity onto the traceless part.
   - Theorem 2(1)–(3): SAH2 and meagre codimension 2 for **metric** perturbations of a compact manifold with Neumann boundary, via Teytel's Theorem A as quoted there.
   - Introduction: Micheletti–Pistoia [Thm 4.1, 4.3] codimension $\tfrac12m(m+1)-1$.
   
   Metric perturbations are interior, so this does **not** cover Euclidean domain deformations. It does show that the target property is a standard notion.
7. **P. D. Lamberti, M. Lanza de Cristoforis, Glasgow Math. J. 44 (2002) 29–43**, p. 30. It reports that Lupo–Micheletti, JMAA 172 (1993) 106–116, proved that $C^3$ domain perturbations preserving a double **Dirichlet** eigenvalue form locally a manifold of codimension $\tfrac12m(m+1)-1=2$. JMAA 193 (1995) 990–1002 covers related elliptic operators. *I did not retrieve Lupo–Micheletti themselves; this is a secondary citation.*
8. Context only: Bérard–Helffer, arXiv:2202.06587v2 (multiplicity bounds survey; Nadirashvili's $2k-1$ bound for smooth planar domains, Dirichlet/Neumann). Maji–Mukherjee–Saha, arXiv:2507.04928 (uses the standard rank-two Riesz projection, lower/upper split branches $\lambda^-_j<\lambda^+_j$, for metric perturbations). Pereira, EJDE 2004/114, and Chitour–Kateb–Long, arXiv:1303.4358 (Henry's transversality framework). Greilhuber–Kepplinger, arXiv:2312.16939 (Arnold transversality conjecture/SAH for metrics, abstract only).

**Not obtained as primary text, so no theorem number is asserted:** Uhlenbeck, Amer. J. Math. 98 (1976) 1059–1078; Albert, Proc. AMS 48 (1975) 413–418; Teytel, *How rare are multiple eigenvalues?*, CPAM 52 (1999) 917–934; Henry, *Perturbation of the Boundary in Boundary-Value Problems of PDEs*, LMS LNS 318 (CUP 2005); Micheletti, Ann. SNS Pisa 26 (1972); Nadirashvili, Dokl. 286 (1986). The attribution of the smooth lemma to Uhlenbeck rests on Marrocos–Pereira's statement. **Its exact locator inside Uhlenbeck 1976 is unverified**, so cite Marrocos–Pereira Lemma 2 as the checked statement.

## 2. Generic simplicity vs per-line control: the report gets this right

- **Hillairet–Judge** give "almost every polygon is simple". This is a measure statement on polygon space and says nothing about which eigenline survives as the lower branch near a given double polygon.
- **Non-scalar image** (some $V$ with $q_V^0\neq0$) suffices for local splitting. A one-dimensional image $\mathbb R A$ only reaches the two eigenlines of $A$: use $\pm V$, since $q_{-V}=-q_V$ exchanges lower and upper.
- **Full image** $\mathrm{Sym}_0(E)\cong\mathbb R^2$ is needed to reach every line. The eigenline at angle $\varphi$ corresponds to the direction $2\varphi$ in $\mathrm{Sym}_0$.

The report's statement that "Generic simplicity alone would not establish it" is correct, and its $\mathrm{diag}(0,t^2)$ example is apt. The full-image property is exactly SAH2, and for smooth Neumann domains it follows directly from Uhlenbeck's lemma.

## 3. Search record and absence claims (bounded)

Queries are listed in the manifest. They covered Teytel/codimension two for domains, Henry-style Neumann transversality, Lupo–Micheletti persistence, Neumann double-eigenvalue codimension under domain perturbation, polygon/corner Bessel transversality, the Nadirashvili Neumann multiplicity paper, Uhlenbeck's lemma, and "strong Arnold"/codimension two for corners/Lipschitz/polygons.

**I found no published statement of** (i) Uhlenbeck's lemma on polygons or other cornered/Lipschitz boundaries; (ii) SAH2/codimension two for Neumann double eigenvalues under domain deformation of polygons; (iii) per-eigenline approximation of polygon Neumann eigenfunctions by simple-eigenvalue smooth domains; or (iv) the conditional all-eigenfunction polygon hot-spots corollary.

These are **search-bounded non-findings, not absence proofs**. Several plausible homes were not checked in primary text: Henry's monograph (its Neumann examples), Teytel 1999, Lupo–Micheletti 1995, the Lamberti–Lanza de Cristoforis Neumann papers, and corner-singularity literature (Grisvard, Dauge, Nazarov–Plamenevskii) on shape derivatives at corners. Given how short the corner step is, I would not be surprised if it appears as a remark somewhere.

## 4. Proof sanity check

### 4.1 Statement P, convex corners
For $\nu=\pi/\beta>1$, the expansion of item 3 above gives $h=A+O(r^{\min(\nu,2)})$ and $\partial_rh=O(r^{\min(\nu-1,1)})\to0$. This holds also for integer $\nu$ (e.g. $\beta=\pi/2$, where reflection gives smoothness). The limit of (P) is $\lambda AB=0$. Correct.

### 4.2 Reentrant corners, $\tfrac12<\nu<1$
On $\theta=0$, $\cos(n\nu\theta)=1$; on $\theta=\beta$, $\cos(n\nu\beta)=(-1)^n$. This confirms the $\pm$ pattern in (3.1). The remainder $O(r^{3\nu}+r^2)$ correctly absorbs $J_0$'s $r^2$ term and $J_\nu$'s $r^{\nu+2}$ correction. (3.2) follows by the termwise differentiation of JM eq. (10), with tail control as described.

- Single side: $h'k'=\nu^2ac\,r^{2\nu-2}\pm2\nu^2(ad+bc)r^{3\nu-2}+O(r^{4\nu-2}+r^\nu)$. The products of the $\nu$-mode with the $3\nu$-mode carry sign $+$ on both rays and are $O(r^{4\nu-2})$. Boundedness of $\lambda hk$ forces $ac=0$.
- Average: the $r^{3\nu-2}$ terms cancel, the rest is $o(1)$ because $4\nu-2>0$, and the limit is $\lambda AB$. Correct.
- $\nu>\tfrac12$ is used exactly here; a slit ($\nu=\tfrac12$) gives $4\nu-2=0$ and is rightly excluded.
- **Remark on the advertised "resonance":** at $\nu=2/3$ the single-side limits are $\lambda AB=\pm2\nu^2(ad+bc)$. Adding the two equations already gives $AB=0$. For $\nu<2/3$ one can also argue side by side: boundedness kills $ad+bc$, and so on. The averaging is the clean way to package this, not an indispensable new idea. The algebra check `experiments/hotspots_multiplicity_r2/check_corner_parity.py` is consistent with this.

### 4.3 Finishing P
- $hk$ is continuous on each closed side, zero at the vertices, and analytic inside. A nonzero interior extremum contradicts §3.1, since $a+b=0$ and $ab=\lambda>0$ are incompatible.
- So $hk\equiv0$ on each side. By analyticity on an open side, $h\equiv0$ or $k\equiv0$ there. Cauchy uniqueness after even reflection then gives a contradiction.
- Orthogonality and simple connectivity are not used. Holes are harmless.

### 4.4 Surjectivity (§4)
- The Hadamard formula (4.2) for $V$ supported away from the vertices is legitimate. Eigenfunctions are analytic up to open straight sides by reflection, and the cross-stress tensor is divergence-free. I verified $\operatorname{div}T=0$ for $T=(\nabla v\cdot\nabla z-\lambda vz)I-\nabla v\otimes\nabla z-\nabla z\otimes\nabla v$.
- $V\cdot n$ ranges over $C_c^\infty$ of every open side, giving a pointwise identity.
- A traceless annihilator, diagonalized as $\mathrm{diag}(\rho,-\rho)$ in an orthonormal $f,g$, gives (P) for $h=f\pm g$, which are orthogonal and nonzero. Correct.
- The deformed domains have curved sides. That is fine, because they are only intermediates before Ball–Zarnescu smoothing.

### 4.5 Lower branch (§5.1)
- The upper bound $\mu_t\le\mu+t\alpha+O(t^2)$ is correct: the mean correction enters the mass at order $t^2$.
- The eigenvector identity $q_V(v,\cdot)=\delta\langle v,\cdot\rangle$ follows from $a_t(v_t,z)=\mu_tb_t(v_t,z)$ for all $z\in H^1$, using $a_0(v_t,z)=\mu b_0(v_t,z)$ for $z\in E$ and $\mu_t-\mu=O(t)$.
- $\delta\le\alpha$ together with simplicity of $\alpha$ gives $v=\pm u$.
- Eventual simplicity follows from the two-orthonormal-limits argument. Only $t>0$ is used. Correct.

### 4.6 Smoothing and diagonal sequence (§5.2)
- Compact $K\subset P$ lies in $P_t$ for small $t$, since $\Phi_t\to\mathrm{id}$ uniformly, and then in $D_\varepsilon$ for small $\varepsilon$.
- Simplicity on $D_\varepsilon$ and the sign choice give convergence to $u_t$. The diagonal choice is fine.
- The output meets the round-2 definition of $\mathcal L$ (local uniform convergence plus eventual containment of compacts); round 2 showed this already forces eigenvalue and $C^\infty_{\rm loc}$ convergence.

### 4.7 Multiplicity at most two on Lipschitz domains (§2)
I checked §§2.1–2.4: the Lipschitz Dirichlet gap; traces change sign via $u^-\in H^1_0$; the full-support annihilating measure; the two-nodal-domain/no-four-alternation argument; and $F=\cos(\theta-c)-\cos(w)\in\mathrm{span}\{1,\cos,\sin\}$. I found no error.

**For the polygon theorem it is redundant:** Judge–Mondal Corollary 5.4 (unaffected by the erratum) suffices. The Lipschitz extension is a regularity adaptation of the corpus `prop:multiplicity` argument and of classical Nadirashvili-type bounds. Its novelty is not material, and I did not search its priority exhaustively.

### 4.8 Required wording repairs
1. **Novelty.** In §8 of the report, replace "may overlap known shape-derivative folklore" with an explicit attribution: the smooth-boundary Statement P and the $f\pm g$ polarization are Uhlenbeck's lemma as in Marrocos–Pereira, arXiv:1310.5178, Lemma 2 and proof of Theorem 9. Say that the new content is the vertex endpoint lemma (§§3.2–3.3).
2. **Overclaim.** "This is a genuine additional argument beyond generic simplicity or spectral convergence" is true. Do not paraphrase it as a new mechanism. "Why the averaging matters" should note that summing the single-edge limits also works at $3\pi/2$.
3. **Scope.** Keep "strict boundary-only extrema", not nonvanishing gradient. Keep "every bounded simply connected polygon" meaning the interior of a simple closed polygon, with no slits. Keep the corpus dependence explicit.

## 5. Bottom line for the parent

- **Validity:** the conditional polygon theorem is sound as written, modulo the attribution repairs.
- **Novelty:** the only literature-new piece I can identify is a short corner extension of Uhlenbeck's boundary lemma. Arnold/SAH2 transversality and lower-branch selection are standard consequences once that lemma holds. Hillairet–Judge generic simplicity is weaker and uses a different method.
- **Significance:** a **routine-to-modest corollary** extending a conditional hot-spots transfer from simple-eigenvalue polygons to all simply connected polygons. It does **not** meet the user's bar of a genuinely novel, significant MathDB advance. Archive it as a correct, new-to-project technical note with the attributions above. The all-Lipschitz eigenline-selection problem remains open, as the report says.
