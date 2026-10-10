# I24 resumed — centered source histories, with the unimodality gap retained

Date: 2026-10-09. Premise: all pinned proofs in **openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are accepted as requested. **Disposition: completed scoped-gap research report; general elementary unimodality remains unproved. No substantial finding is submitted for acceptance.**

The interrupted I24 task ended **CANCELLED**, with no pending child runs and no report. Its cancellation cause is not established. Its progress commentary was an unverified lead, not a completed proof. This fresh task reconstructs that lead below: rational wall transport commutes with the appropriate bar anti-involution; every jump belonging to a nonempty fixed-shape history is consequently a finite, centered, palindromic Laurent polynomial. This gives an effective energy-reversing involution preserving the history skeleton and source shape. It does **not** prove that these polynomials have nonnegative centered character multiplicities. That is the precise unresolved step in the first route. The second route still lacks a coefficient-preserving identification to a chart covered by a Lefschetz theorem.

The parent's objective was not paused or cancelled. The accepted count remains four; this report assigns no finding number, count increment, priority claim, independent proof PASS, or significance PASS. No agent was spawned. All writes are confined to this report and `frontier/{sources,experiments}/i24_elementary_unimodality_resumed/`. The original I24 trees remain read-only.

## 1. Premises, preserved state, and exact target

For every integer (n\geq0), every weakly increasing (h:[n]\to[n]) with (i\leq h(i)\leq n), and the graph with edges (i<j\leq h(i)), put (M=|E(G)|) and

\[
\chi_G(X;q)=\sum_{\lambda\vdash n}c_\lambda(q)e_\lambda(X).
\]

The target is symmetry about (M/2) and unimodality of **each elementary coefficient**. More explicitly, writing (c_\lambda(q)=\sum_{d=0}^{M}a_{\lambda,d}q^d), the missing inequalities are (a_{\lambda,d+1}\geq a_{\lambda,d}) for integers (0\leq d<M/2). For odd (M) the middle comparison is equality by symmetry. Zero coefficients and the empty graph are included. Elementary positivity and symmetry are already supplied premises, not new findings.

At entry, all **80** files listed in the parent's [interruption checkpoint](../experiments/i24-interrupted-checkpoint.json) matched their byte lengths and SHA-256 hashes. The resumed [integrity snapshot](../sources/i24_elementary_unimodality_resumed/inherited-integrity.json) records each comparison. The current rules, current ledger, complete I19 report, checkpoint and both task records were frozen in [inputs.json](../sources/i24_elementary_unimodality_resumed/inputs.json); [full-brief.txt](../sources/i24_elementary_unimodality_resumed/full-brief.txt) preserves this task's scope. Historical launch statuses in those snapshots remain historical, including the resumed task's then-running launch record.

The inherited complete inventory contains **749 manuscript directories** and is explicitly not truncated. The inherited search covered **9,340 cached text records**; it is a search record, not a claim to have read all manuscripts. This task reused that search and the **22** selected pinned files, verifying SHA-256, Git blob identity and the complete inventory entry. [Pinned references](../sources/i24_elementary_unimodality_resumed/pinned-references.json) give the old local paths and immutable raw URLs. The old bytes were neither recopied wholesale nor repaired. [Source contracts](../sources/i24_elementary_unimodality_resumed/source-contracts.json) and [read locators](../sources/i24_elementary_unimodality_resumed/read-locators.json) separate read construction/proof passages from merely retained companion files.

Let **EP** denote the pinned *Elementary Positivity of Chromatic Quasisymmetric Functions*, under `preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/build/sections/`. The contracts actually used are:

- `01-introduction.tex`, `main:theorem`: a terminating partition-valued witness and coefficientwise positivity; it explicitly makes no elementary-unimodality assertion. `main:hessenberg` gives abstract degreewise Young permutation modules and explicitly no preferred isomorphism or cup-product compatibility.
- `02-graphs.tex`, `graph:torus`, `graph:kernel`, `graph:reciprocity`: centered multiplication (X_aX_b=v^{\Omega(a,b)}X_{a+b}), the elementary/monomial coefficient pairing, and color-reversal symmetry.
- `03-reordering.tex`, `alg:reordering`, `alg:shifts`, `alg:shifted-degree`, `alg:slope-factor`, `alg:strings`, `alg:output-parameter`: positive unit factors obtained from graded shuffle quotients and **infinite polynomial strings**, with explicitly shifted parameters.
- `04-walls.tex`, `wall:three-factors`, `wall:incoming-prescription`, `wall:unit`, `wall:factors`, `wall:recursion`, `wall:mutation`: uniquely normalized rational wall data, positive oriented jumps, and coefficient transport subject to the stated completion and finite-polynomial hypotheses.
- `05-triangle.tex`, `tri:embedding`, `tri:domination`, `tri:monomial`, `tri:positive-coefficient`: for a triangular embedding and (x_\lambda=\sum_i\lambda_i d_i),
  \[
  P_\lambda(v):=[X_u]\Theta_{x_\lambda}^{H_-}=v^{-M}c_\lambda(v^2).
  \tag{1}
  \]
- `06-witness.tex`, `route:finite`, `route:switch`, `route:history-series`, `route:return`, `route:parity`, `route:exact`, `route:witness`, and `07-completion.tex`: energy-preserving finite packet switches, histories independent of composition, zero-energy terminal anchors, and the reversible conversion to words of a fixed shape.

These source theorems are used as true. Nothing below purports to audit or replace their proofs.

## 2. Reconstructing bar invariance in the actual normalization

### Proposition A: normalized rational wall operators commute with bar

Work first over (\mathbb Q(v)), completed in the free positive root cone (C^+). Every coefficient of the source's normalized wall system lies in this rational subfield: the initial coefficients are rational, and at each root order the incoming prescription, three-factor decomposition, multiplication and inversion use finitely many rational operations. This is EP `wall:recursion`, with its preceding uniqueness constructions.

Define

\[
\overline{f(v)X_a}=f(v^{-1})X_a.
\]

This is a semilinear **anti**-involution, since

\[
\overline{X_aX_b}=v^{-\Omega(a,b)}X_{a+b}
=X_bX_a=\overline{X_b}\,\overline{X_a}.
\tag{2}
\]

The definition is coefficientwise on the root completion over (\mathbb Q(v)). It is **not** a substitution on arbitrary elements of (\mathbb Q((v^{-1}))): such substitution need not preserve the Laurent-series completion. All bar comparisons are rational identities first; only then are coefficients expanded at infinity or recognized as Laurent polynomials.

For the prescribed simple unit

\[
D_p=\prod_{j\geq0}(1+v^{-1-2j}X_p),
\]

the coefficient of (X_{kp}) in its logarithm, for every (k\geq1), is

\[
\ell_k(v)=\frac{(-1)^{k+1}}{k}
            \frac{v^{-k}}{1-v^{-2k}}
=\frac{(-1)^{k+1}}{k(v^k-v^{-k})}.
\tag{3}
\]

Thus (\ell_k(v^{-1})=-\ell_k(v)), (\overline{\log D_p}=-\log D_p), and (\overline{D_p}=D_p^{-1}). This uses the actual (-1) shift in (D_p=E_{p,-1}).

For a constant-term-one root series define (\tau(g)=\overline g^{-1}). Reversal in (2), followed by inversion, gives

\[
\tau(gh)=\tau(g)\tau(h).
\tag{4}
\]

The operation preserves each subgroup supported on positive, zero or negative values of a fixed covector. Hence if (g=g_+(h)g_0(h)g_-(h)), uniqueness of the source's three-factor decomposition yields

\[
(\tau g)_\bullet(h)=\tau(g_\bullet(h)).
\tag{5}
\]

Moreover (\log\tau(b)=-\overline{\log b}). Applying this to the middle factor at (V(r)) shows that (\tau(g)) satisfies exactly the same incoming prescription as (g): (3) changes sign under bar, and the extra minus sign restores it; the nonsimple prescribed coefficients stay zero. Degreewise uniqueness of `wall:incoming-prescription` now proves (\tau(g)=g). By (5),

\[
\overline{g_0(h)}=g_0(h)^{-1}
\tag{6}
\]

for every middle factor, in particular every generic wall element. This argument does not assume positivity of a factorization or apply bar termwise to its potentially infinite list of shifted units.

For a wall crossing (W=\operatorname{Ad}(g_0)^\varepsilon), with (\varepsilon=+1) from positive to negative and (-1) in reverse, (2) and (6) give

\[
\overline{W(F)}
=\overline{g_0}^{-\varepsilon}\,\overline F\,
  \overline{g_0}^{\varepsilon}
=g_0^{\varepsilon}\overline F g_0^{-\varepsilon}
=W(\overline F).
\tag{7}
\]

In particular every rational jump coefficient (J(a,j;v)=[X_{a+jp}]W(X_a)) satisfies

\[
J(a,j;v^{-1})=J(a,j;v).
\tag{8}
\]

This conclusion holds for both crossing orientations. Positivity is a **separate** statement: the history recursion only uses crossings with (\varepsilon\Omega(p,a)\geq0), precisely EP `wall:factors` and `wall:recursion`. In the zero-pairing case conjugation fixes the entire monomial line, so only the zero jump occurs. No orientation is changed by bar.

The same reasoning gives rational bar invariance of the theta sections: transport commutes with bar, their incoming coefficients are the constants (\delta_{n,x}), and incoming-coordinate triangular uniqueness identifies the barred section with the original one. For (1), Laurent-polynomial finiteness then gives the already-known symmetry of (c_\lambda). The next proposition is more local.

### Proposition B: every jump used by a nonempty fixed-shape history is a finite centered polynomial

Fix the source's embedding and rational path choices. A **skeleton** retains the stopping label, all chamber/crossing choices, and the exponent increments of a total history, forgetting jump energies and decoration indices. The finite cone interval (B=\{y:nd_1\leq_C y\leq_C u\}), its bounded arrangements, and the strict height decrease give only finitely many skeletons. For a skeleton (s) ending at (x_\lambda), let its nonzero-jump coefficient functions be (J_{s,1},\ldots,J_{s,k}). Paths depend on chamber and exponent only, not on the decorations. Thus its decoration enumerator is the product

\[
P_s(v)=\prod_{i=1}^{k}J_{s,i}(v),\qquad
P_\lambda(v)=\sum_{s\text{ ending at }x_\lambda}P_s(v).
\tag{9}
\]

Empty products are one. A skeleton is called nonempty here if it has at least one decorated realization, equivalently all its factors are nonzero. Every factor expands in (\mathbb N((v^{-1}))) in the positive direction; (9) is the source's `route:history-series`. There is no extra torus phase in (9): `route:jump-decoration` already uses centered monomials, histories add jump energies, and terminal anchors have energy zero. The cross-packet terms in `route:product-energy` and `route:cross-energy` are accounted for by the packet switch before this history identity.

By (1) and `route:parity`, the nonnegative sum (9) has finite support inside ([-M,M]\cap(M+2\mathbb Z)). Fix a nonempty skeleton and one term with positive coefficient from every factor except (J_{s,i}). Each exponent in the support of (J_{s,i}), translated by this fixed sum, contributes positively to (P_s), hence to (P_\lambda). Its support must therefore be finite. All coefficients are finite integers by the source's Laurent completion. Consequently every (J_{s,i}\in\mathbb N[v,v^{-1}]). Its Laurent expansion identifies the underlying rational function, so (8) proves ordinary palindrome symmetry centered at zero.

Each factor also has a single parity of exponent: otherwise, keeping the other terms fixed would produce both parities in (9). Let (R_i=\max\operatorname{supp}(J_{s,i})). Symmetry gives minimum (-R_i) and (R_i\geq0). The product's extreme coefficients cannot cancel, so

\[
\sum_i R_i\leq M,\qquad
\sum_i\operatorname{par}(J_{s,i})\equiv M\pmod2.
\tag{10}
\]

In particular every factor on such a skeleton is supported in ([-M,M]). This proof asserts finiteness **only for jumps belonging to a nonempty skeleton with this terminal shape and graph target**. It does not assert that every positive jump of every source wall is finite. Even the general implication “positive rational and bar-invariant implies finite” is false:

\[
\frac{v^2}{(v^2-1)^2}=\sum_{j\geq1}jv^{-2j}
\]

is bar-invariant and coefficientwise positive at infinity but is not a Laurent polynomial. The finite target and nonnegative product argument are essential.

### Corollary: an explicit symmetry involution, not a raising operator

A decorated jump is ((j,e,t)), where (1\leq t\leq[v^e]J(a,j;v)). Replace it by ((j,-e,t)), leaving its wall, input exponent and output exponent fixed. Proposition B proves that this is defined and involutive on every jump of a nonempty fixed-shape skeleton. Applying it to all jumps reverses total energy and preserves the skeleton and shape. It can be computed using the source's local rational coefficient algorithms, without supplying the final elementary coefficient list.

Conjugate this involution by the source's bijection (\Phi_\varnothing), with the unique weakly decreasing anchor word of multiplicities (lambda). It becomes a terminating involution on the admissible words assigned shape (lambda), complementing graph inversion degree (d\leftrightarrow M-d). Reversal transfers it to the source's original (D_G^0) convention. This constructs symmetry within the source witness. It gives no injection from degree (d) to degree (d+1), and symmetry was already known from `graph:reciprocity`. This is technical progress, not a qualifying resolution or novelty claim.

## 3. First constructive route: centered chains and the exact local gap

Write

\[
L_r(v)=v^{-r}+v^{-r+2}+\cdots+v^r\quad(r\geq0).
\]

For a finite palindromic polynomial (J(v)=\sum_e a_ev^e) of one parity, expansion in these characters is unique:

\[
J(v)=\sum_{r\geq0}m_r L_r(v),\qquad m_r=a_r-a_{r+2},
\tag{11}
\]

with the unused parity set to zero. This follows by telescoping (a_e=\sum_{r\geq|e|,\ r\equiv e\bmod2}m_r). Nonnegativity of every (m_r) is exactly centered unimodality. Positivity of (a_e) and palindrome symmetry do not impose its sign.

**Conditional construction.** Suppose every jump on every nonempty skeleton ending at (x_\lambda) has (m_r\geq0) in (11). At each energy, order the source's decoration indices and match them to the ordered labels

\[
(r,b,e),\quad 1\leq b\leq m_r,\quad e=-r,-r+2,\ldots,r.
\]

For fixed ((r,b)), raising changes (e\mapsto e+2) until the top and lowering reverses it. The matching is finite and reversible. It uses only local jump coefficients. These are chains of decorations, not an assertion that the source shuffle multiplication itself supplies a Lefschetz operator.

For two chains with ranks (0,\ldots,a) and (0,\ldots,b), a symmetric chain decomposition of their product is, for (k=0,\ldots,\min(a,b)),

\[
(0,k),(1,k),\ldots,(a-k,k),
(a-k,k+1),\ldots,(a-k,b).
\tag{12}
\]

Removing each bottom row and right column leaves the next rectangle. This proves disjoint coverage, unit rank increments, and endpoint-rank sum (a+b). Applying (12) successively decomposes a product of any number of local chains; its total energy runs in steps of two and every chain is centered at zero. Then (9) is a disjoint union of centered chains, still at fixed shape. Transport by (\Phi_\varnothing^{-1}) gives reversible raising/lowering on the corresponding graph words. With the (v^M) shift and (q=v^2), every chain has center (M/2). Thus the conditional construction would prove the target.

What is **proved** here is this implication and its explicit reversible algorithm. What is **missing** is the nonnegativity of (11) for the graph-relevant source jumps. The local condition is sufficient, potentially stronger than necessary: a graph's total coefficient might be unimodal through compensation between skeletons even if an individual factor or skeleton is not.

### The exact shift of an elementary unit

Let (U_{p,k,f}=\prod_{j\geq0}f(v^{k-2j}X_p)), where (f(T)=1+T) or ((1-T)^{-1}). Put (t=\Omega(p,a)\ne0), (A=|t|), and take the positive orientation (\varepsilon=\operatorname{sign}(t)). The source's ratio is, to the right of (X_a),

\[
\prod_{\ell=1}^{t}f(v^{k+2\ell}X_p)\ (t>0),
\qquad
\prod_{\ell=t+1}^{0}f(v^{k+2\ell}X_p)\ (t<0).
\]

Conversion (X_aX_{jp}=v^{-jt}X_{a+jp}) is necessary. The resulting scalar alphabet is

\[
\{k+2\ell-t\}
=\{k+1+(1-A),k+1+(3-A),\ldots,k+1+(A-1)\}.
\tag{13}
\]

Accordingly the (j)-jump coefficient is

\[
v^{j(k+1)}e_j(v^{1-A},\ldots,v^{A-1})
\quad\text{or}\quad
v^{j(k+1)}h_j(v^{1-A},\ldots,v^{A-1}).
\tag{14}
\]

The centered parts are characters of exterior or symmetric powers of the (A)-dimensional irreducible (mathfrak{sl}_2)-module. The (E) coefficient vanishes for (j>A); the (H) coefficients can continue. But their centers are **(j(k+1))**. Only the normalized simple factor (k=-1) is automatically centered. For units with argument (bp), use pairing (bt) and count their selected multiplicity (j) as total increment (bjp).

A useful sufficient repair would group, separately by argument and by (E/H) type, the shifts (k+1) into finite nonnegative sums of centered irreducible characters. The crossing alphabet of such a group is the tensor product of this shift module with the pairing module; exterior/symmetric powers, and then products over groups and choices of total increment, give centered characters. One still needs that grouping for the actual wall, with the source's finiteness bounds. This is a normalization-specific instance of the representation mechanism already present in Davison–Mandel Lemma 3.5, not a new representation theorem.

### Why the existing positivity factors do not prove the repair

The algebraically allowed same-ray wall

\[
g_p=E_{p,1}E_{p,-3}
\]

has, at (\Omega(p,a)=1), the entire positive crossing expansion

\[
\operatorname{Ad}(g_p)X_a
=X_a+(v^2+v^{-2})X_{a+p}+X_{a+2p}.
\tag{15}
\]

Indeed the right-hand ratio is ((1+v^3X_p)(1+v^{-1}X_p)); the centered shifts are (v^{-1}) and (v^{-2}) for its first and second coefficients. Its one-jump polynomial is finite, positive and bar-invariant, yet

\[
v^2+v^{-2}=L_2-L_0.
\]

Its trivial-character multiplicity is (-1). It is even pre-Lefschetz in DM's terminology (a sum of two even monomials), so adding that weaker property does not help. The source's allowed-unit positivity theorem permits (15), for example as replacement incoming data. **There is no identification of (15) with a wall occurring in the normalized triangular chart or with a graph-relevant history.** It refutes an inference from the stated algebraic factor class, not the graph conjecture, and does not establish failure of the sufficient local condition in that chart.

The primitive strings offer no automatic alternative. In EP `alg:strings`, (D_dT_d-T_dD_d=1), (D_d) is locally nilpotent, and (T_d) generates degrees (h,h+1,h+2,\ldots). These are infinite Weyl strings. Already (D=d/dx,T=x) on (\mathbb Q[x]) illustrate the issue: (D) does not descend to (\mathbb Q[x]/(x^{r+1})), because (D(x^{r+1})=(r+1)x^r). If multiplication is truncated by hand at degree (r), the top commutator becomes (-r), not (1). The source's auxiliary filtration, original degree, and output parameter (k=u(d)-2h) cannot be relabeled as a finite hard-Lefschetz structure.

## 4. Second route: cluster or geometric identification

The actual chart has forward-difference roots, not vertex roots. In its first two levels, let (a_0,\ldots,a_5=(d_1,b_{1,1},d_2,b_{2,2},b_{1,2},d_3)) and (c_i=a_{i+1}-a_i). Their matrix, calculated in I19 from the source's allowed rational times, is

\[
\begin{pmatrix}
0&-2&0&1&0\\
2&0&-1&-1&1\\
0&1&0&-1&-1\\
-1&1&1&0&-1\\
0&-1&1&1&0
\end{pmatrix}.
\tag{16}
\]

The arrows (c_0\to c_3\to c_1\to c_0) form a directed triangle. In fact the same submatrix is present in **every initial triangular chart with (D\geq3)**: the first two forward lists contain exactly these six vertices, and `tri:phase-order` always restricts to (\theta_{2,2}<\theta_{1,1}<\theta_{1,2}). Their adjacency depends only on that ordering. Later vertices do not change their pairings. Symplectic enlargement restricts to the same form. Thus neither a larger embedding nor this enlargement makes the initial simple-root quiver acyclic.

This is not a mutation-invariant impossibility statement. The inherited search visited 17,760 states with **every intermediate matrix entry bounded by 6**, discarded 29,520 edges, and found no acyclic seed within that component. Paths leaving the cap were not explored. No repeat mutation search was run here.

The strongest retained DM version, [1910.12915v3](https://arxiv.org/abs/1910.12915v3), distinguishes the following interfaces:

- Theorem 2.15 supplies positive wall polynomials and preserves bar invariance and pre-Lefschetz type.
- Conjecture 2.17 is the stronger preservation of **Lefschetz type** under general scattering. Theorem 2.18 proves it when simple incoming polynomials equal one and the incoming quiver is acyclic.
- Conjecture 3.13 is the general coefficient-level implication; Theorem 3.14 assumes those unit incoming polynomials and an **acyclic, nondegenerate** pairing matrix. Theorem 1.5 gives the acyclic cluster case. Merely adding dual lattice directions does not meet the acyclicity requirement.
- Proposition 3.12 already proves bar preservation in their framework, and Lemma 3.5 supplies the centered packet mechanism. The source-specific proof in Section 2 is a check of normalization and applicability, not a claim of a new general scattering principle.

The initial dilogarithm normalization is compatible at the level of rational coefficients: DM (18) gives (\log\Psi_v(X_p)=\sum_{k\geq1}(-1)^{k-1}X_{kp}/(k(v^k-v^{-k}))), identical to (3). Their displayed infinite product uses another parameter expansion; equality is justified by this logarithm, not by silently identifying expansions at zero and infinity. The source works in dual covectors with incoming direction (V(r)=\Omega(\cdot,r)); translating between diagram conventions also requires the corresponding skew-dual identification and crossing signs. Section 2 avoids needing an external theta identification for bar symmetry.

For a **Lefschetz** proof by this route, one must actually supply: (i) a suitable seed/representation object with the theorem's hypotheses, (ii) identification of the normalized diagram and the specific theta sections, (iii) transport of (x_\lambda,u,H_-) and the coefficient functional, and (iv) a common zero center with no uncontrolled coefficient mixing. Finding a quiver with a familiar name or a symplectic extension is insufficient. Even the source's `wall:mutation` compares actual coefficients under a finite-polynomial initial-value identity and specified sides of each cut; it does not allow arbitrary transport of an individual extracted coefficient to an unrelated all-negative chamber. No qualifying acyclic chart and transport have been produced.

The 2026 [Davison survey, 2601.08004v1](https://arxiv.org/abs/2601.08004v1), Example 3.11 and Conjecture 3.12, still labels the relevant generalized two-wall Lefschetz assertion conjectural and explains that an effective BPS interpretation is missing. The stronger theorem is not supplied by merely replacing the older DM reference with this survey.

The retained pinned *Equivariant cohomological Hikita conjecture for arbitrary quivers*, `introduction.tex`, `thm:main`, concerns equality of coefficient-map kernels and a graded isomorphism

\[
H_F^*(\mu^{-1}(0)^{\nu\text{-stable}}/G)
\cong\mathbb C[Y_{\mathfrak f}^{\nu}],
\]

under regularity (semistable equals stable and the gauge action is free). It permits arbitrary finite quivers and relates cohomological to BFN homological grading. It does not identify the graph-history multiplicity spaces with these rings, nor assert the required projective hard-Lefschetz statement. No choices of dimension vectors, framing, regular stability, or maps identifying (1) with suitable primitive multiplicities have been established here. The other retained companion sections are explicitly marked as not applied, rather than being invoked through their titles.

Finally, the existing Hessenberg route still has I19's exact obstruction. The formal function

\[
F=(1+q^2)e_2+qe_{1,1}=(1+q+q^2)s_{1,1}+qs_2
\]

is elementary-positive, palindromic and Schur-Lefschetz. After applying (\omega), a commuting (S_2\times\mathfrak{sl}_2) realization has Young permutation modules (h_2,h_{1,1},h_2) in degrees (0,1,2). Nevertheless its (e_2)-multiplicities are (1,0,1). Thus equivariant Lefschetz plus degreewise permutation decompositions does not imply elementary unimodality. This is an abstract countermodel, not a claimed graph or Hessenberg counterexample. A shape-preserving multiplicity-space action is the missing geometric datum.

## 5. Literature and significance limits

[Primary contracts](../sources/i24_elementary_unimodality_resumed/primary-contracts.json) retain exact statement passages and primary version histories. [Literature references](../sources/i24_elementary_unimodality_resumed/literature-references.json) retain original URLs, retrieval times, hashes and status codes by reference to the unchanged original files. Only two direct archive-page checks were made in this task, to verify the two identified version/theorem concerns; there was no restarted literature search. They confirmed DM v3 (15 June 2021) and Kafidov v2 (1 August 2026).

Shareshian–Wachs [1405.4629v2](https://arxiv.org/abs/1405.4629v2), Conjecture 1.3, separates the elementary-unimodality assertion from positivity. Foster Tom [2311.08020v2](https://arxiv.org/abs/2311.08020v2), Corollaries 4.18 and 4.20, already treats **almost-K-chains**, not merely ordinary K-chains, with an explicit common-center calculation. These are not candidate new families here.

Cho–Huh [1711.07152v2](https://arxiv.org/abs/1711.07152v2), Theorem 3.3, provides positivity in its stated family; Theorem 4.2 provides the more specialized explicit unimodality formula. These conclusions are not interchangeable. Huh–Nam–Yoo [1812.03445v1](https://arxiv.org/abs/1812.03445v1), Theorem 4.9, treats melting lollipops. Abreu–Nigro [2006.00657v2](https://arxiv.org/abs/2006.00657v2), Proposition 3.6, already proves elementary positivity and unimodality for **all abelian Hessenberg functions**, by positive contributions with equal centers. A repackaging of any of these families would not close the requested significance gap.

The strongest retained [2607.20595v2](https://arxiv.org/abs/2607.20595v2) is *Log-concavity of elementary coefficients for low-rank abelian Hessenberg graphs, with a counterexample in general*. Its PDF SHA-256 is

`201f540dc765db1adfeb7ed3734d6a0e1e0e9c4c503e330dce4bacbba58fb86b`.

Theorem 1.1 covers all abelian complement-Ferrers diagrams with at most three rows **or** at most three columns, proving the stronger log-concavity property. Theorem 1.2 gives (h=(2,4,4,6,7,10,10,10,10,12,12,13,13)) and the coefficient of (e_{(6,5,1,1)}), whose nonzero coefficient sequence is

\[
1,6,38,128,257,362,400,362,257,128,38,6,1
\]

in degrees (5,\ldots,17). It is explicitly positive, palindromic and unimodal. Only log-concavity fails ((6^2<1\cdot38)). It is **not** evidence against the present target. The older v1 remains historical evidence; it was not used in place of v2. This task did not re-enumerate that 13-vertex graph or claim independent verification of the paper's graph identity.

The old publisher retrieval for the Davison survey returned HTTP 403; the retained arXiv v1 full text supplies the quoted contract. The [query record](../sources/i24_elementary_unimodality_resumed/queries.json) honestly notes one unrecoverable provenance limit: the old web evidence contains `initial` and `followup` result strings but not the exact original query payloads. They have not been fabricated. The corpus terms and results, primary retrieval bytes and version histories are retained. None of these bounded checks establishes worldwide priority or an exhaustive absence of other approaches.

No new infinite graph family beyond these known regimes has been proved. The symmetry lemma, constructive conditional reduction and normalization diagnostics are useful to prevent repeating incorrect bridges, but do not meet the substantial-finding gate.

## 6. Diagnostics, sealing, and handoff

The unchanged original `results.json` reports 1,360 unit-shift cases, 200 centered-packet cases, and 100 rectangle cases. Its graph portion enumerates all natural unit interval functions through (n=7), with counts (1,2,5,14,42,132,429), 1,852 nonzero elementary coefficients and 33,218 tested inequalities. It uses proper-coloring monomial counts and exact elementary/monomial inversion, **not** the source's wall witness. Its mutation scope is the capped component described above. These remain inherited finite diagnostics; this resumed task did not rerun them or claim their reproduction on the parent's behalf.

The retained `diagnostics.py` was modified after the retained results. In particular it now includes rational sign checks of logarithmic dilogarithm coefficients for (j=1,\ldots,12), which were not separately counted in `results.json`. This chronology is retained, not silently repaired. The parent was separately reproducing that script in isolation; this report does not claim the outcome of that work.

New [check.py](../experiments/i24_elementary_unimodality_resumed/check.py) addresses the identified bar-normalization concern using standard-library exact rational arithmetic. It reconstructs the source's incoming group by its actual degreewise three-factor prescription for a two-root example and the five-root matrix (16), through total root degree three, at (v=2,5/3) and their reciprocals. It independently checks all prescribed incoming logarithmic coefficients, the identity (\overline g=g^{-1}), all three factors at three covectors, and forward/inverse adjoint coefficients on two monomial inputs. It makes **4,752 adjoint coefficient comparisons**, including zero slots. A separate direct convolution of the source's rational (D_p)-coefficients and their inverse verifies **108** normalized finite-alphabet coefficient comparisons, including zero pairing and both positive crossing orientations. These tests are finite specializations; the universal proof is in Section 2. They do not implement the full graph witness or demonstrate that (15) occurs in its chart.

The new [results.json](../experiments/i24_elementary_unimodality_resumed/results.json) also records the explicit polynomial (15) and the positive, infinite bar-invariant rational series. The former is a closed-form diagnostic, not an extra searched graph. The new checks do not inflate the old result counts.

From the project root, run:

```sh
python frontier/experiments/i24_elementary_unimodality_resumed/check.py --check
python frontier/experiments/i24_elementary_unimodality_resumed/verify.py
```

The first command recomputes only the new bounded checks and compares the exact saved JSON without rewriting it. The second verifies the report/artifact seal, all 80 checkpointed old files, seven newly frozen inputs, 22 pinned identities against the full tree, 41 source statement contracts, 36 read passages, 26 primary contracts, and inherited retrieval hashes. It separately reports live shared-ledger drift. Frozen corruption, old-tree mutation, or non-ledger dependency drift is not disguised as concurrent index drift. [Completed state](../sources/i24_elementary_unimodality_resumed/completed-state.json) and the artifact seal snapshot the finished scoped-gap result while referring to the original bytes. Seal integrity is not an independent mathematical proof review.

**Precise handoff.** The residual first-route obligation is nonnegativity of (a_r-a_{r+2}) for each graph-relevant jump, or a different construction that allows compensation between skeletons while preserving shape. The second-route obligation is an actual coefficient-preserving identification to objects with a proved centered Lefschetz action. Equations (2)–(10) settle normalization, common centering and relevant-jump finiteness, so these need not be assumed or rediscovered. Neither obligation is proved here. The completed evidence supports a scoped-gap disposition and further targeted research, not acceptance as a fifth substantial finding.
