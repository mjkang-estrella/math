# I163: Contribution of the corrected fixed-sector BFSS Weyl law

## Recommendation

**TECHNICAL ONLY for the entire corrected theorem.** Retain the exact spectral result, but do not count it as a ninth substantial finding.

The strongest plausible additional contribution is control of all singular collars and the noncompact commuting horn on the original physical form. It is real work, not supplied by a compact equivariant Weyl theorem. Nevertheless it reduces to an energy-scale cell-count argument once the stipulated source's **sector gradient-plus-linear confinement** is retained. FNT's diameter bound applies to the actual log-concave singular-value weight, with no lower bound on that weight and no deterioration at intersections of walls. One complex mean per fiber component per eligible cell suffices. The remaining horn estimate is a three-dimensional lattice sum. Sections 3–5 give this full reduction, including domain, multiplicity and constant, rather than declaring the ingredients “standard.”

This is a contribution judgment under the project's nonroutine-bridge standard, not a claim that an older paper states this exact theorem. No exact full-scope published duplicate was established. Worldwide priority remains uncertain. **No new correctness objection was found in the corrected chain.** That does not reverse the original exact-operator failure.

| Question | Disposition |
|---|---|
| Original S155 exact matrix/form assertion | **FAIL retained**, coefficient four times the source |
| Separately corrected leading-law deduction | Supported; the reduction below introduces no further repair |
| I158 broader review and evidence | **INCOMPLETE, unsealed**; stale prevalidation is not a sealed PASS |
| I162/parent evidence PASS | Integrity/finite checks only, not proof or substantiality certification |
| Full corrected contribution | **TECHNICAL ONLY** |
| Acceptance/count | No acceptance action; eight remain eight |

All OpenAI theorems **and lower operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. Nothing here audits upstream truth or draws a conclusion from a contradiction. External publications are ordinary evidence. Only the assigned I163 report/source/experiment paths are authored. No children, ancestor executions, corpus copies, shared edits, staging, commits, publication or interference with I161.

## 1. Exact object and the explicit correction

For each **fixed source-constructed confined physical Spin(9) type** $\lambda$, let $H_\lambda$ be the operator part of the original closed SU(2)-invariant supercharge form. Count the **full isotypic space**:

$$
N_\lambda(E)=\operatorname{rank}\mathbf1_{[0,E]}(H_\lambda),\qquad
N_\lambda(E)\sim d_\lambda m_\lambda
\frac{\sqrt2\,\Gamma(1/4)^2}{270\pi^{3/2}}E^{9/4},
\quad m_\lambda=\dim(V_\lambda^*\otimes F)^K.
$$

Here $K$ is the full principal stabilizer, including its finite components and spin lifts. The explicit nonzero example is $\lambda=(3086,3080,0,0)$, with $M=6,C=1024,m=3072,c_m=3$. The threshold integer $m$ is **not** $m_\lambda$. Constants can depend on the fixed representation. There is no claim about the full Hamiltonian, uniformity in $\lambda$, sector mixing, a massless gap, or a newly selected wall realization.

Write **P** for the complete pinned positive-eigenvalue source TeX:
`preprints/Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026/build/positive-eigenvalues-relative-su2-bfss.tex`.
Its SHA-256 is `c6d02247561556ab27c8015579045a8a71f20214261a14c810175979970621ce`. P was freshly read in full, including proofs and bibliography. Line citations here use LF lines of this TeX or the retained primary text, not PDF page counts.

P, `lem:form`, `eq:potential`, lines 236–256, and its computation at 310–318 both give

$$
B_{\rm src}(X)=\frac i2 f_{abc}x_i^a\gamma^i_{\alpha\beta}
\theta_\alpha^b\theta_\beta^c,\qquad f_{abc}=\sqrt2\varepsilon_{abc}.
$$

S155 line 141 instead has $2i$; its line 83 exact coefficient is wrong as well. The parent correction agrees with the source. In the same summation convention the entrywise gamma bound 64, two color orders, and $\|\theta\|=1/\sqrt2$ give

$$
\|B_{\rm src}(X)\|\le32\sqrt2\sum_{i,a}|x_i^a|
\le96\sqrt6\,|X|<1024|X|.
$$

Keeping the loose upper bound does not keep the false equality. Every $B$ below means $B_{\rm src}$. In particular we do **not** apply the source's sector confinement to a Hamiltonian with fourfold Yukawa coupling. I162 supplies an actual-sector nonvanishing check for the discrepancy. The separate correction preserves the threshold, type, physical domain and leading law.

The unchanged S155 report hashes to `c6e05a0853e3232f86c8a8049cb9ecb373c9358ca58bfc1cb42c6e81d4b15f44`; the complete I162 review to `c2632983c859686fd8f71007d0f41002a885abb6efee9afd8e41235d7f46f70f`; its seal to `1da3611744b48f35763cb7d16f30fb3ce8e6c05e5f136e9ba07a50a71c0f7448`. The parent correction is a separate immutable reference. Both original task briefs, including embedded reports and finalized responses, were read in bounded decoded ranges through their endings, with their other fields separately read and lossless reconstruction checked. Their historical `running` fields are launch snapshots.

## 2. What the strongest inspected antecedents actually supply

### 2.1 Pinned operations, not just theorem titles

P's `lem:form`, `lem:rotations`, `lem:branching`, `lem:slice`, `lem:oscillator`, `prop:confinement` and `lem:large-sectors` supply the original core, commuting compact-group projections, the exact kinetic/quartic/linear form, exclusion of low transverse oscillator levels, and a nonzero polynomial highest-weight section. In particular P already supplies

$$
q_\lambda\ge \tfrac14\|\nabla\psi\|^2+c_m\int |X||\psi|^2,\qquad c_m>0.
$$

This is much stronger than abstract compact resolvent for the present purpose. It is the decisive BFSS input in the reduction. It is not a pointwise lower bound for $V+B$.

The threshold companion was checked beyond its abstract: its complete introduction, charge/domain section, separated-center fast analysis and final counting section were read through their endings. `lem:domains` explicitly proves constant-symbol cutoff, convolution and compact-group averaging in the minimal graph domain. `lem:slice` retains the orbit-volume normalization and square-root density unitary. `lem:fast-line` and `lem:fast-projection` concern a neutral rank-one fast projection in specified bounded-graph or growing-mass regimes; their remainder is projected, not a uniform all-mode estimate. `prop:massive-tightness` uses annular localization, and the final dimension count concerns massive null profiles and the massless kernel. These are genuine lower operations, not a high-energy fixed-type Weyl law. No threshold-state uniqueness, whole-block recovery, or unread dependency of that kernel proof is used here. Its intermediate massive-index, lift and profile proofs were not freshly read in full and are not asserted to have been.

The complete mapped lexical search covered 9,340 corpus texts and 776 retained PDF texts, with 257 binary-only originals hash-checked but not searched. It verifies all 10,373 original positions against the complete 13,223-entry tree and finds 46 occurrences with the recorded bounded same-line expression. This is **lexical**, not 749-paper semantic coverage. Actual relevant hits were followed:

* *Uniform excess charge*, complete `03-localization.tex`: `lem:loc-identity` expands a Lipschitz squared partition on physical forms; `lem:loc-cubes` derives the Neumann kinetic coefficient by integer lattice counting with explicit boundary-frequency error. These are antecedent localization/counting operations, not a BFSS reduction.
* *Coulomb ground-state density without Kohn–Sham ensemble representation*, complete `03-angle-spectrum.tex`: weighted mean-zero gaps, core approximation, and weighted IMS/tail retention. Its special orbital weights and low spectral gap are not FNT's arbitrary convex-cell diameter estimate.
* *Universal optimality of the triangular lattice*, lines 813–949 of `08-arithmetic-verification.tex`, including the complete local weighted Poincaré/trace/extension argument at 881–945: weights $|y|^\gamma$, $-1<\gamma<1$, with integrable reciprocal. This is not directly usable for $J$, whose wall powers include six. No transfer from that reciprocal-integrability argument is claimed.
* *Sharp one-dimensional matrix Lieb–Thirring*, introduction and complete `spectral.tex`: finite matrix trial spaces, compact form passage and negative spectral moments for integrable whole-line matrix potentials. This does not directly give the three-dimensional degenerate-weight physical Weyl law. The action/trace construction on which its sharp inequality depends is not invoked or claimed freshly read.

The other lexical contexts include random-matrix counting, harmonic link counting and symplectic/LQG uses of “Weyl.” No corpus-wide no-duplicate claim is drawn from excluding those contexts.

### 2.2 External primary comparisons

The relied primary proof operations were read, rather than inferred from inherited notes. Exact reading coverage and PDF/text hash pairs are in `reading.json` and `bindings.json`.

| Primary | Operative content and limit |
|---|---|
| Halpern–Schwartz, `hep-th/9712133v1`, complete retained text, appendices A–G | Equations (2.4)–(2.6) already give three singular values, radial divergence operator and $(s_1s_2s_3)^{d-3}\prod\lvert s_i^2-s_j^2\rvert$. Appendix B retains gauge connections; C treats the Yukawa spectrum; G treats angular separation. Generalized projection retains the second-order term missed by naive Born–Oppenheimer. The selected-channel expansion through $R^{-2}$, and its conjectural completeness ending, are not an all-mode counting remainder. |
| Lüscher, NPB 219 (1983), model opening, §5 and complete Appendix D | Scalar bosonic oscillator slicing, trace-square-root control and averaging yield confinement/discreteness. This is an antecedent of confinement, not the fermionic fixed-type law. The field-theoretic perturbation sections are unread and unused. |
| Simon, JFA 53 (1983), retained papers 158 and 159, both complete | The Fefferman–Phong exposition uses energy-scale cubes and at most one low mode per cube (158, Appendix, especially A.5, lines 503–507). This is a concrete counting antecedent. The unequal/equal-channel nonclassical asymptotics show that valleys can change powers or add logarithms. The “sliced bread” comparison is a **trace inequality**, not an eigenvalue-by-eigenvalue comparison. |
| Danielsson–Ferretti–Sundborg, `hep-th/9603081v2`, complete | Fast boson/fermion multiplicities, residual gauge charge and slow cone/angular terms are retained. Born–Oppenheimer/WKB has restricted validity, especially near the origin/lowest channel. No uniform growing-mode replacement is licensed. |
| Aref'eva–Koshelev–Medvedev, `hep-th/9911149v1`, complete | Two spatial color vectors, six bosonic variables, eight-dimensional fermion module; reduced Jacobian $fg(f^2-g^2)$, scalar/matrix sector equations, Laguerre and Airy/WKB asymptotics. The approximate slow endpoint condition is not the original Spin(9) physical wall domain. |
| FNT, `1207.0680v2`, complete | Theorem 1.1, lines 94–104, allows nonnegative log-concave weights on bounded convex sets. The one-dimensional comparison and convex slicing proof finish at 443–444. At $p=2$ it gives exactly the needed diameter-squared constant. The paper itself notes earlier $p=2$ antecedents. |
| Weich, `1311.2436v2`, lines 1–665 | Setup and complete §3 equivariant Weyl proof: compact inverse energy band supplies compact symbol support for functional calculus/singular stationary phase. The commuting BFSS horn violates this hypothesis. Later Gutzwiller material is unread and unused. |
| Küster–Ramacher, `1508.03540v2`, lines 1–290 and 1142–1445 | Compact boundaryless manifold, reduced semiclassical Weyl statement and its proof. Intervening trace machinery and appendices are not freshly read; no theorem from them is used. This is not a global noncompact-horn theorem by substitution. |

FNT plus the elementary dimension argument below suffices; no theorem of Simon, Weich or Küster–Ramacher is needed as a black box for the global asymptotic. In particular this recommendation does not pretend that inapplicable compact theorems already state S155.

**Current-search limit.** Dedicated searches also returned the 2025 noncompact Schrödinger Weyl paper `2504.15551`, its v2 HTML listing, and `2605.07200` on complete Riemannian manifolds. The responses available here supplied metadata/short summaries, not their complete hypotheses or proofs; refined hypothesis queries did not resolve that limitation. They are **unread leads**, not claimed applicable or inapplicable theorems. Gaussian/large-$d$ BFSS counting leads likewise are not exact interacting-operator comparisons in this review. Fresh queries did not certify the latest version of every older arXiv comparison; the versions in the table are the versions actually bound and read. `web-scope.json` records three exact fresh queries and their results, and explicitly limits the earlier search history retained only in the conversation summary. None of these limitations establishes novelty. They leave a stronger *publication-level* comparison open, but not a missing logical input to the demonstrated technical reduction.

## 3. A domain-respecting weighted-cell transfer

Here is the reusable operation, with stronger-than-necessary hypotheses sufficient for this model. Let $\mathcal C=\{s_1>s_2>s_3>0\}$ and let $w$ be positive inside and nonnegative on its closure, smooth inside, log concave, and locally integrable. Let a closed semibounded form on $L^2(\mathcal C,w;\mathbb C^r)$ have:

1. A core whose restrictions to bounded convex cells satisfy FNT, and whose form norm controls their weighted first derivatives.
2. The global lower bound
   $$
   q[u]\ge\int w\{a|\partial u|^2+(\epsilon V+b|s|)|u|^2\},\quad
   a,\epsilon,b>0,\quad V=\sum_{i<j}s_i^2s_j^2.
   \tag{T}
   $$
3. All compact regular smooth $\mathbb C^r$-valued sections in its core, and invariant Lipschitz localization preserving the form with the kinetic IMS error.
4. On each fixed bounded regular polyhedron, after $s=E^{1/4}t$, a flat unitary realization of $q/E$ with principal part $-h^2\Delta/2+V(t)I$, $h=E^{-3/4}$, and uniformly bounded $O(h)+O(h^2)$ matrix terms.

Only the **actual core completion** is meant in (1), not an arbitrary maximal weighted Sobolev space. Compact embedding is available from the BFSS source; the cell argument itself bounds dimensions without defining any degenerate Neumann operator.

For a cube $Q$ of side $\ell=\kappa E^{-1/2}$, intersected with the chamber, FNT gives

$$
\|u-u_Q\|_{L^2(w,Q)}^2
\le\frac{3\ell^2}{\pi^2}\|\partial u\|_{L^2(w,Q)}^2,
\qquad u_Q=\frac{\int_Qwu}{\int_Qw}.
$$

Choose $\kappa$ so $a\pi^2/(3\kappa^2)>3$. Call $Q$ eligible if the infimum of $W=\epsilon V+b|s|$ over the **whole cell** is at most $2E$. For any subspace with every Rayleigh quotient at most $3E/2$, vanishing of its $r$ complex means on all eligible cells is impossible for a nonzero vector: eligible cells then cost $>3E$, and ineligible cells cost at least $2E$. Thus the map to the list of means is injective. It gives

$$
\dim L\le r\,\#\{\hbox{eligible cells meeting the support}\}.
\tag{M}
$$

Real and imaginary parts yield **one complex constraint per component**, not two. Positivity of the potential terms in (T) is essential. One never applies the original physical confinement inequality to an arbitrary cell restriction. Apply (T) to a physical supported vector first, then split its nonnegative scalar integral. This removes the feared physical-domain interface altogether.

### Horn and collar counts, with endpoints

Eligibility puts the cell within $O(\ell)$ of a point with $|s|\le2E/b$. At first coordinate $u>0$, $V\ge u^2(s_2^2+s_3^2)$ gives at most $C(1+E/u)^2$ transverse cells. For support $s_1>A=RE^{1/4}$, retain whole cells meeting it. For fixed $R\ge1$ and large $E$, their first intervals start at least at $A/2$; the last ends by $CE+O(\ell)$. Integral comparison includes the first summand:

$$
\#Q\le C\left[
E^{1/2}\int_{A/2}^{CE+O(\ell)}(1+E/u)^2\,du
+(1+2E/A)^2\right]
\le C\left(\frac{E^{9/4}}R+E^{3/2}\log(2+E)+E^{3/2}+1\right).
\tag{H}
$$

The constants in the last bound can be independent of $R\ge1$; the large-$E$ threshold is at fixed $R$. If the interval is empty, there is no additional tail. The additive one in the transverse count retains the narrowest cells even when the horn width is below $\ell$. Linear confinement, not a conjectured oscillator cancellation, ends the count at $O(E)$.

Inside $s_1\le RE^{1/4}$, the entire singular set is covered by the three wall slabs for $s_3=0,s_1=s_2,s_2=s_3$. A scaled $\delta$-slab enlarged by one cell has

$$
C_R\bigl(\delta E^{9/4}+E^{3/2}+1\bigr)
\tag{C}
$$

cells. Indeed its two tangential lengths are $O(RE^{1/4})$, and its normal thickness is $O(\delta E^{1/4}+\ell)$. Divide their product by $\ell^3$, keeping endpoint terms. A union bound includes all multiple collisions, rank loss, intersections and the origin. It does not require separate estimates whose constants blow up when two strata approach.

Equations (M)–(C) are the entire global counting interface. They work for any weight meeting (1), irrespective of its wall vanishing order, and for any compatible form realization satisfying (2)–(4). This is why the application is routine **after the source coercivity is supplied**, although confinement or finite classical volume alone would not suffice.

## 4. Verification of every transfer hypothesis in the physical model

### Fiber, measure and nonzero example

For $G=\mathrm{Spin}(9)\times SO(3)$, $X\mapsto AXR^t$, special-orthogonal SVD gives one ordered positive chamber. An unwanted left orientation is corrected in the six-dimensional perpendicular space. At distinct positive singular values,

$$
K=\text{full spin preimage of }
\{(\operatorname{diag}(D,Q),D):
D=\operatorname{diag}(\pm1,\pm1,\pm1),\det D=1,\ Q\in SO(6)\}.
$$

Thus $K^0=\mathrm{Spin}(6)$ and $K/K^0$ is the Klein four group. A gauge $2\pi$ loop rotates sixteen real fermion planes, so its Clifford lift ends at $+1$; the action descends to $SO(3)$. Keeping SU(2) gives the same invariants.

Evaluation of an intertwiner acts by $T\mapsto R_F(a,R)T\pi_\lambda(a)^{-1}$. This proves the dual convention and

$$
E_\lambda=(V_\lambda^*\otimes F)^K,\qquad
m_\lambda=\tfrac14\sum_D\operatorname{Tr}(A_D|_{\operatorname{Hom}_{\mathrm{Spin}(6)}(V_\lambda,F)}).
$$

The sign-component operators are commuting involutions on that invariant space because their squares and commutators lie in $K^0$. The spin center is already imposed there. No ambient $2^{24}$ fiber rank or additional factor $1/4$ is substituted.

The 24 fermion rotation planes of first speed $1/2$ have a unique top first-weight line of weight six; sign balance gives other weights zero. Its Spin(7) centralizer and commuting gauge group have no nontrivial character. This supplies the gauge-fixed vector of weight $(6,0,0,0)$ and $M=6$. P's highest polynomial with $k=1540$ then has type $(3086,3080,0,0)$. At columns $s_1e_1,s_2e_3,s_3e_5$ its value is $(s_1s_2)^{2k}v\ne0$. Evaluation therefore proves $m_\lambda>0$. For every nonzero source polynomial type, nonvanishing on the dense regular set gives the same conclusion.

Every compact regular section $T(s)$ lifts by
$$
I_T(w)(gD_s)=R_F(g)T(s)\pi_\lambda(g_{\rm left})^{-1}w.
$$
The $K$-condition makes it well defined; local singular frames and smooth zero extension away from singular matrices put it in the physical projected core. Schur averaging gives orbit norm $\operatorname{Tr}(T^*T)/d_\lambda$; a constant unitary normalization removes the orbit-volume constant. The complete isotypic space is consequently
$$
V_\lambda\otimes L^2(\mathcal C,J\,ds;E_\lambda).
$$
Full counting is $d_\lambda$ times reduced counting.

The 18 perpendicular-image directions give $\prod_i s_i^6$. Each left/right image-pair metric block is
$$
\begin{pmatrix}s_i^2+s_j^2&-2s_is_j\\-2s_is_j&s_i^2+s_j^2\end{pmatrix},
$$
with determinant $(s_i^2-s_j^2)^2$. Therefore
$$
J=(s_1s_2s_3)^6\prod_{i<j}(s_i-s_j)(s_i+s_j),\qquad \deg J=24.
$$
Its log is a positive sum of logs of positive affine functions, hence concave. Angular energy is a sum of nonnegative squares with inverse-square denominators. For a fixed type it is a finite matrix, bounded on compact regular sets. The corrected linear $B$ preserves $E_\lambda$ by equivariance. These facts retain all components without diagonalizing their coupled spectrum.

### Original closure and localization

Combine P's sector inequality with its exact source bound
$$
q\ge G/2+V_1-CR_1,\qquad q\ge G/4+cR_1.
$$
For $\epsilon=c/[2(c+C)]$, their convex combination has
$$
a=(1+\epsilon)/4,\quad b=c/2,\qquad
q\ge aG+\epsilon V_1+bR_1.
$$
Apply it to differences of core approximants. Closedness of differentiation and multiplication gives convergence of gradients, $\sqrt V$- and $\sqrt{|X|}$-multiples. The $B$-form is continuous in the last weighted norm. Thus no quartic integrability is assumed when passing to the closure. Dropping angular squares gives (T).

Restrictions of smooth physical core maps to the linear diagonal section are smooth through coordinate walls. On each bounded convex cell FNT applies directly; if desired, replace every affine factor $l$ of $J$ by $l+\eta$, apply the smooth positive-weight inequality, and pass uniformly to $J$. Derivative control from the preceding core-difference argument and continuity of weighted means extend it to the **actual restricted completion**. There is no need for a new density theorem for an arbitrary degenerate Neumann domain.

Ordered singular values are globally Lipschitz in the Frobenius norm. An invariant bounded Lipschitz multiplier with bounded gradient preserves the minimal physical closure: mollify it with an invariant ambient mollifier, multiply compact core approximants, and pass using the charge commutator and the controlled weighted norms. Compact-group projections commute with these multipliers. The charge commutator is bounded Clifford multiplication by the gradient, already explicit in the threshold companion's domain operation. Consequently, for a squared partition,
$$
\sum_jq[\chi_j\psi]=q[\psi]
+\tfrac12\int\sum_j|\nabla\chi_j|^2|\psi|^2.
$$
Sine/cosine profiles of one Lipschitz angle avoid a square-root derivative singularity. At scale $E^{1/4}$ the error is $O_{R,\delta}(E^{-1/2})$.

The physical domain remains the closure of the ambient projected core. At every singular orbit its smooth members satisfy full stabilizer-equivariant slice matching, not just a scalar parity rule. Neither the upper mean constraints nor the interior trial functions change this domain. Full stabilizer information enters the fixed fiber and the core; (H)–(C) bound every omitted neighborhood without needing to solve its boundary problem. Singular strata themselves have ambient measure zero and furnish no extra $L^2$ summand.

## 5. Local law, global comparison and exact constant

On a fixed bounded regular polyhedron $\Omega$, the weighted measure scales as $E^{27/4}J(t)\,dt$. The flat unitary includes $E^{27/8}J(t)^{1/2}$. Dividing the form by $E$ gives
$$
P_h=-\tfrac{h^2}{2}\Delta+V(t)I+hB_{\rm src}(D_t)+h^2C_\lambda(t),
\qquad h=E^{-3/4}.
$$
All extra matrix coefficients are bounded there. They need not be bounded near walls or uniformly in $\lambda$.

For the Dirichlet form, scalar potentials $V\pm O(h+h^2)$, each repeated $m_\lambda$ times, bracket this matrix operator. Fixed small interior cubes give the lower bound; an exterior cube union with Neumann splitting gives the upper bound for a Dirichlet polyhedron. Count the integer frequencies of $-h^2\Delta/2$; the coordinate-plane discrepancy is $O(h^{-2})$ for each fixed cube. First $h\to0$, then cube size $\to0$, gives
$$
h^3N_\Omega(1)\longrightarrow
m_\lambda(2\pi)^{-3}\frac{4\pi}{3}2^{3/2}
\int_\Omega(1-V)_+^{3/2}\,dt.
$$
This argument uses no Neumann domain-monotonicity assertion and no identification of weighted Neumann with flat Neumann. The latter would have a Robin correction; it is unnecessary.

For the global lower bound, extend all interior Dirichlet trial sections by zero and lift them to the original physical form, using every fiber and representation direction. Exhaust the chamber.

For the upper bound, fix $R,\delta$, and split a vector into good support in a bounded regular region and bad support in the enlarged collars and horn. The map $\psi\mapsto(\chi_g\psi,\chi_b\psi)$ is an isometry on the **entire** subspace below $E$. IMS bounds its direct-sum Rayleigh quotient by $E+O_{R,\delta}(E^{-1/2})$. Use the closed supported physical form spaces for this min–max step; their compactness is inherited from P. The good space embeds in a slightly larger regular Dirichlet domain. Apply (M)–(C) to the bad space at the shifted threshold, eventually below $3E/2$. Overlap of collars and horns can only overcount cells. Restoring $d_\lambda$ yields
$$
\limsup_{E\to\infty} E^{-9/4}N_\lambda(E)
\le C_{\rm phase}+C_\lambda/R+C_{\lambda,R}\delta.
$$
Take **$E\to\infty$, then $\delta\downarrow0$ at fixed $R$, then $R\to\infty$**. No uniformity of $C_{\lambda,R}$ in $R$ is asserted. The interior exhaustion gives the opposite liminf.

For convergence of the phase integral, $s_1=u\ge1,V\le1$ implies $s_2^2+s_3^2\le u^{-2}$, with area at most $\pi/(4u^2)$. Its tail is $O(R^{-1})$. A small regular region gives positivity. Tonelli and a Gaussian integration in $s_3$, followed by polar coordinates in $s_1,s_2$, give
$$
\int_{(0,\infty)^3}e^{-V}\,ds=\frac{\Gamma(1/4)^3}{16},
\qquad
\int_{\mathcal C}(1-V)_+^{3/2}\,ds
=\frac{\Gamma(1/4)^3\Gamma(5/2)}{96\Gamma(13/4)}.
$$
The second identity uses degree-four homogeneity and divides by six permutation chambers once. Since $\Gamma(13/4)=45\Gamma(1/4)/64$, multiplication by the momentum factor gives exactly
$$
d_\lambda m_\lambda\frac{\sqrt2\,\Gamma(1/4)^2}{270\pi^{3/2}}.
$$
There is no second Jacobian, orbit-volume, component-group or chamber factor.

## 6. Why this meets the technical, not substantial, classification

This assessment does not reason “each lemma is familiar, so the synthesis is routine.” The possible new synthesis has been isolated and discharged:

* The physical constraint causes no new high-energy channel analysis. Equivariant evaluation fixes one finite fiber; all regular sections lift. Finite components change that fiber, not the cell mechanism.
* The wall singularity causes no new weight-dependent local estimate. The full needed uniformity is **exactly** FNT's existing convex-diameter inequality. Its proof and hypotheses allow vanishing weights; core approximation avoids introducing a different boundary domain.
* The noncompact end needs more than compact resolvent. But P already supplies the stronger gradient/radius inequality, and a convex combination restores quartic control. Eligible cells are cut off at $CE$. Their remaining count is precisely (H), including the sub-cell-width endpoints. No cancellation, higher-order expansion, growing spectral projection, new microlocal calculus or uniform-in-type bound is required.
* Local comparison and IMS never leave the physical form until a comparison-space enlargement with the correct min–max direction. Hence there is no unpaid domain transfer hiding in “standard bracketing.”

The new interface is therefore a finite-codimension adaptation of the familiar energy-scale cube method, replacing the unweighted cell gap by the already available weighted one. The three-dimensional horn geometry needs only $\int u^{-2}du$, and all singularities need one finite union of slabs. This reduction applies without knowing the detailed angular spectrum or the Yukawa eigenvectors. That insensitivity is important evidence that it is a routine transfer, not a newly solved BFSS channel problem.

S155 is a useful exact new-to-project statement, substantially sharper than Q153's coarse powers. Its correctness required care, as the normalization error demonstrates. Neither that improvement, the extensive bookkeeping, nor the explicit gamma constant establishes a nonroutine bridge under the acceptance standard. The source's genuinely strong confined-sector construction is stipulated prior input and cannot be recounted as the candidate's contribution.

## 7. Evidence, validation and remaining limits

Owned evidence:

* `frontier/sources/i163_corrected_bfss_contribution_astra/`
* `frontier/experiments/i163_corrected_bfss_contribution_astra/`

The initial 135-reference baseline preserves original reports, task records, I155/I158/I162 evidence and preparation, including untracked ancestor files. Additional source/primary references and their PDF/text pairs are separately bound without copying their contents. Reading receipts distinguish fresh complete text, selected operations, inherited bytes, and metadata-only search leads. Passage hashes/endings verify the ranges recorded, not whether a machine understands their mathematics. The complete pinned map is replayed once per verification with exact lexical occurrence reconstruction.

The first preparation attempt failed because a tree lookup wrongly removed the `preprints/` prefix. The owned preparation code was corrected before any seal; already created baseline files were preserved and checked equal. Truncated broad ledger displays and unsuccessful/refined web queries are recorded as limits, not semantic coverage. I158's old prevalidation is neither executed nor repaired: its read manifest changed from the old recorded 8,756 bytes to 37,110 bytes, and it has no seal.

The package uses one canonical sorted owned-file inventory, validated read-only before one exclusive final seal. The new offline verifier checks all owned and referenced immutable bytes, all mapped original/blob/text bindings, decoded task views and search/read receipts **before** finite arithmetic. It installs a guard denying writes, filesystem mutations, network, process creation and bytecode output. No ancestor program is imported, compiled or executed.

Run from any directory:

```sh
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i163_corrected_bfss_contribution_astra/verify.py
```

The post-seal result belongs in the handoff, not in an after-the-fact edit to this report. Evidence PASS cannot certify universal mathematics or substantiality.

**Remaining limits:** the exact theorem's worldwide publication status; complete hypotheses/proofs of the two new noncompact leads; latest-version certification for every older comparator; unread sections explicitly excluded in §2. None is used to assert an absence of prior art or to pay a step of the reduction. There is no identified unpaid analytic prerequisite for the corrected leading law in this contribution review. Parent acceptance/integration is not performed.

The unrelated triangular critical-stability premise and external-provenance FAIL remain. I153's historical Bose screen remains incomplete; I155's claimed later closure is separate work, not retroactive completion and not a B153 theorem. No Ising, Bose or adiabatic audit is reopened.
