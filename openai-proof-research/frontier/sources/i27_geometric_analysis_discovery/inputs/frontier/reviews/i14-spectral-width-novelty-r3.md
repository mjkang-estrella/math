# I14 spectral graph width — final prior-art/significance review R3

**Verdict: TECHNICAL ONLY. Preserve the independent proof PASS; do not count I14 as a fifth accepted substantial finding.** The candidate is a valid, useful general-coefficient extension of the stipulated three-dimensional source, but it does not meet this task's stricter requirement of a substantial nonroutine new mechanism. This is not a DUPLICATE verdict: I did not locate an existing theorem with precisely its full conclusion and hypotheses. Nor is it a GAP verdict. The decisive reduction uses **published local estimates plus the pinned source's proof**, rather than applying a global band-width theorem.

Review date: 2026-10-09. The user's resumption supersedes historical pauses. The accepted list supplied for this review is R006, R008, R009, R010; counts of three in R2 and the parent experiment are stale bookkeeping, not mathematical evidence. The ten-result target has no bearing on this verdict. No worldwide-priority certification or MathDB score is made. No subagents, shared-index edits, staging, commits, or candidate changes were used.

## 1. Claim and frozen inputs

I read the **complete 300-line candidate**, **complete 239-line R2 proof review**, and the parent experiment frontier/experiments/i14-spectral-width-r2-parent-verification.json. Versions:

- Candidate SHA-256: 22557dd8004e06a0a300919daeaaeb7393319906907b2fe2381f0999b2a0c052.
- R2 review SHA-256: 6ee328eab654c6fed4b8c1958f5987a3ad3a02aa73f6e4f615a1067dabae3040.
- Upstream: openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

With \(\Delta=\operatorname{div}\nabla\), W assumes a complete connected smooth boundaryless Riemannian three-manifold and
\[
 \int_M(a|d\phi|^2+\mathrm{Scal}\,\phi^2)\ge
 \lambda\int_M\phi^2\quad(\phi\in C_c^\infty(M;\mathbb R)),
 \qquad4\le a<6,\quad\lambda>0.
\]
It concludes a continuous map to a locally finite simplicial graph, with its usual polyhedral topology, whose **entire fibers** have original-metric diameter at most
\[
 500\lambda^{-1/2}s_a,\qquad s_a^2=\frac{8-a}{2(6-a)}.
\]
There are no orientation, spin, compactness, bounded-geometry, or auxiliary-weight bounds. At \(a=6\), the complete metric \(dt^2+e^{2t^2}(dx^2+dy^2)\) on \(\mathbb R^3\) satisfies the quadratic lower bound four and has infinite Urysohn 1-width; the same example works for every \(a\ge6\). The coefficient interval, not 500, is sharp. The \(a\le4\) implication is elementary source monotonicity, not another finding.

All applicable pinned results are accepted as true. This review checks deductions and source contracts, not upstream truth. The [input manifest](../sources/i14_spectral_width_novelty_r3/input-manifest.json) and [corpus manifest](../sources/i14_spectral_width_novelty_r3/corpus-manifest.json) identify the frozen evidence.

## 2. Entire pinned corpus and strongest companions

I parsed the complete sources/preprints-tree.json: **13,223 entries, truncated:false, 749 manuscript directories**. I retrieved and Git-blob verified **all 9,340 textual files** in that inventory: 8,007 TeX, 521 bibliography, 784 Markdown, and 28 text files, totaling 141,349,121 bytes. There were no identity or retrieval failures. The truncated root tree was not used.

The reproducible full-text searches include Urysohn/Uryson, spectral scalar, graph width, codimension-two width, torical band, stabilized/weighted scalar, macroscopic dimension, coefficient/parameter contexts, and per-manuscript scalar-curvature/operator co-occurrence. Whitespace was normalized. Logs and scripts are in [the experiment directory](../experiments/i14_spectral_width_novelty_r3/). This is a whole-corpus text search, not a claim to have manually read every unrelated paper or every rendered PDF. Unexpected notation can evade a text search; negative matches do not certify novelty.

The substantive width matches are the two spectral titles and the pointwise-width companion. The alternate spelling also finds a Papasoglu reference in the Bass-trace manuscript, which is a bibliography occurrence. Other scalar/operator matches concern mass inequalities, Ricci flow, algebraic geometry, and unrelated scalar terminology.

**S: Spectral scalar curvature and Urysohn width in dimension three.** I read all six complete section files. In build/sections/01-introduction.tex, thm:main assumes the displayed quadratic inequality with **4** replacing \(a\), for every complete connected smooth boundaryless three-manifold, and concludes an entire-fiber graph bound \(500/\sqrt\lambda\). Section 06 constructs a locally finite graph. Consequently whole fibers, nonorientability, unrestricted noncompact geometry, compactly localized minimization, and controlled collar gluing are already supplied by S.

**C: Spectral scalar curvature and uniform Urysohn width.** The actual introduction.tex thm:main is for \(n\ge4\), still with **\(-4\Delta+\mathrm{Scal}\ge1\)**, and gives entire-fiber width \(C_n\) into an \((n-2)\)-complex. I read the actual interface:width, pre:reserve, stretch:local, and assembly:round contracts. The reserve theorem enlarges a complete metric and changes an arbitrary drift, but retains the input \(D_1(h,w)\) in its lower bound. The partition interface requires stabilized scalar curvature at least \(2/5\), a dominating complete metric, prescribed pair separations, and locally finite compactly supported log warps. Neither the main theorem nor these stronger interfaces starts from \(D_\beta\ge1\) with \(\beta<1\). Their stated dimension is at least four.

**P: Positive scalar curvature and uniform codimension-two width.** Introduction.tex thm:main assumes \(n\ge4\) and the **pointwise** bound \(\mathrm{Scal}_g\ge1\), and concludes entire-fiber \((n-2)\)-width \(C_n\) for arbitrary complete connected smooth boundaryless manifolds. The countable:initial and countable:construction statements and their invariant start from stabilized scalar data, not a larger Laplacian coefficient. The coefficient \(4k/(k+1)=3.99\) in that construction is below four, not a hidden \(4<a<6\) theorem. The closed-cover corollary gives a qualitative macroscopic-dimension result for universal covers of closed PSC manifolds.

I also checked the actual main statements of An integral scalar-curvature bound for real simplicial volume and Positive scalar curvature forces rational inessentiality. These concern closed oriented manifolds and integral or topological conclusions. Neither gives original-metric uniform width under W's spectral hypothesis.

The corpus manifest records every exact path, pinned raw URL, Git blob, and SHA-256. In particular, the 15 cached TeX files of S and C agree with both the earlier source manifest and the independent whole-inventory retrieval.

## 3. Primary literature and actual theorem scopes

Primary PDF bytes, converted text, current metadata pages, versions, and hashes are preserved in [literature](../sources/i14_spectral_width_novelty_r3/literature/). Secondary discovery pages were not used as theorem authorities.

**Hirsch–Kazaras–Khuri–Zhang (HKKZ), IMRN 2024, arXiv:2301.08270v2.** The author-hosted cached PDF has SHA-256 7776c3df07fac8c6a3ec7ea9405f8b293a8399d67d9450f33b9c1733b8273872. Theorem 1.1 assumes an oriented open three-manifold, a closed hypersurface separating the ends into two nonempty classes, no spherical classes in \(H_2(M;\mathbb Z)\), \(\inf R>-\infty\), \(c>1/6\), and positive spectral constant \(\Lambda_c\) for \(-\Delta+cR\). It bounds the sum of the two end distances by \(\pi/\alpha\), where
\[
 \alpha^2=\frac{\Lambda_c(6-c^{-1})}{2c(8-c^{-1})}.
\]
Theorem 1.2 assumes a compact odd-dimensional **spin \(\widehat A\)-overtorical band**, \(c>(n-1)/(4n)\), and \(\Lambda_c>0\). It bounds its boundary distance by
\[
 2\pi\sqrt{\frac c{\Lambda_c}
 \frac{(4c-1)n+2-4c}{(4c-1)n+1}}.
\]
For \(n=3,c=1/a,\Lambda_c\ge\lambda/a\), both give the scale \(2\pi s_a/\sqrt\lambda\). **Both six and this exact length scale are prior art.** Theorems 1.3 and 1.4, respectively concerning nonspin overtorical bands through dimension seven and cubes, fix \(c=1/2\); neither is a hidden arbitrary-manifold graph theorem. [Primary manuscript](https://www.math.stonybrook.edu/~khuri/Blackhole_existence.pdf).

**Chai–Sun, Band width estimates with lower spectral curvature bounds, arXiv:2504.10142v2, 7 April 2026, accepted CVPDE version.** PDF SHA-256 911bc343e955b9e2277fd2e3c57f47041152bcecae33372d8c02c9d73978a579. Theorem 1.4 assumes a compact torical band \([-1,1]\times\mathbb T^{n-1}\), \(3\le n\le7\), a smooth positive interior \(u\) with zero boundary values, and
\[
 -q\Delta u+\tfrac12Ru\ge\Lambda u,\quad
 \Lambda>0,\quad0<q<\frac{2n}{n-1}.
\]
Its conclusion is
\[
 \operatorname{width}\le\frac{\pi}{\sqrt{\Gamma_n\Lambda}},
 \qquad \Gamma_n=\frac{2n-(n-1)q}{4(n-1)-2(n-2)q}.
\]
Here \(q=a/2,\Lambda=\lambda/2\). Crucially, its **proof**, Lemma 2.4 and equations (4.3)–(4.6), already contains the general stable-surface inequality needed below, before torus topology is used. That is a stronger significance comparator than the main theorem alone. [Primary v2](https://arxiv.org/abs/2504.10142v2).

**Chai–Sun, Some rigidity theorems for spectral curvature bounds, arXiv:2604.04052v1, 5 April 2026.** PDF SHA-256 2fad15f7b03a3879dc8feb5302ff8b902afe660b5a6cf16c890989fe5198149a. Theorem 1.4 concerns complete oriented stable \(u^q\)-weighted surfaces in complete three-manifolds with \(-qu^{-1}\Delta u+R/2\ge0\): its compact case has \(0\le q<4\), its noncompact classification \(0\le q<3\). Theorem 1.12 gives a torical-band comparison for \(0\le q<2(n-1)/(n-2)\), the spectral bound, weighted boundary-mean-curvature inequalities, and the ODE \(\Gamma_n\eta^2+\eta'+\Lambda=0\) on an interval of a decreasing solution. It bounds band width by that interval length, with rigidity. Theorems 1.20–1.23 impose torus-product, torus-connected-sum, or absolutely weighted-area-minimizing-cylinder conditions. Lemma 2.6 and §2.3 Case II explicitly perform the general second-variation square completion. None states W. [Primary v1](https://arxiv.org/abs/2604.04052v1).

**Gromov, Four lectures, arXiv:1908.10612v6, §3.10.1.** PDF SHA-256 5c9fd01047cce6f0082f46bff4d83a7e7dbfe9e83bc83e35ac00297021a2d871. Theorem (G) assumes a complete **orientable** three-manifold with a torus extension of scalar curvature \(\ge\sigma>0\), with mean-convex boundary if present; it concludes \(\operatorname{width}_1<36\pi/\sqrt\sigma\). Width is defined using entire point inverse images. Lemma (A) gives bounded-width gluing for a proper locally contractible space covered by closed locally contractible pieces without triple intersections, with bounded-diameter locally contractible overlap components of vanishing rational first homology. The global graph principle is established prior art. [Primary v6](https://arxiv.org/abs/1908.10612v6).

**Gromov, Product inequalities for torus-stabilized scalar curvature, SIGMA 20 (2024), 038.** Journal PDF SHA-256 def8fa47b5832a75f9391384340f8802397e3532a219bbe8f8d0ac08fd8e05be. §§1.A–1.B give the multiple-warp formula and the compact Dirichlet \(1/4\)-proposition identifying stabilized scalar curvature with the bottom of \(-4\Delta+R\), not with \(-a\Delta+R\) for \(a>4\). [Primary journal copy](https://www.imath.kiev.ua/~sigma/2024/038/sigma24-038.pdf).

**Liokumovich–Wang, arXiv:2308.04044v1.** Theorem 1.1 assumes a complete noncompact three-manifold with **pointwise** \(R\ge6\). It produces a proper Morse function such that each connected level component has ambient diameter below \(18\pi\) and area at most \(33\pi\). Passing to an appropriate Reeb graph distinguishes components; the fact that the real-valued function has disconnected fibers does not invalidate its width consequence. Its curvature hypothesis is the obstruction here. PDF SHA-256 a8b773fe3708b9ac8ce96167a4120e6b54ea9f8d5f88c1a9da012fe7c0c16242. [Primary v1](https://arxiv.org/abs/2308.04044v1).

**Chodosh–Li, Generalized soap bubbles, arXiv:2008.11888v4 / Annals 2024.** Lemma 16 assumes a closed surface and positive \(v\) satisfying \(\Delta v\le-(K_0-K)v+\tfrac12v^{-1}|dv|^2\); it bounds diameter by \(\pi\sqrt{2/K_0}\). Lemma 18 gives the stable-surface estimate inside its particular weighted slicing construction; Proposition 12 supplies weighted-bubble minimization. These do not state W. Current PDF SHA-256 c7f13ac9d21b4d3f13dfdb06373b4a0af9198b5f05759063f802e5102b64be0c; archived arXiv metadata identifies v4, 20 September 2023. [Primary v4](https://arxiv.org/abs/2008.11888v4).

**Chai–Chen–Pyo, arXiv:2606.19858v1, 18 June 2026.** Theorem 1.9 still concerns \([-1,1]\times\mathbb T^2\), \(0\le q<3\), \(\Gamma=(3-q)/(4-q)\), a positive weight, and weighted boundary inequalities; it concludes the model band-distance bound. Its positive-mass theorem imposes asymptotically hyperbolic toroidal-end data. PDF SHA-256 a215c81caf32ac5ef0af1b7a8382dcc695c37da546aab928aad3bb412b3fb231. This later primary paper supplies no full-scope graph theorem. [Primary v1](https://arxiv.org/abs/2606.19858v1).

Current metadata was archived on the review date. The bounded modern-literature search found no exact replacement for W; it does not establish worldwide priority.

## 4. The strongest reduction: the necessary local input is already known

Normalize \(\lambda=1\). Put \(q=a/2\in[2,3)\), \(\beta=2/q\), \(T=-q\log u\). The candidate's area density is exactly \(u^q\), the Chai–Sun functional. On any stable two-sided weighted \(\mu\)-surface, **before using torus topology**, their equation (4.6) in dimension three gives
\[
 \int_\Sigma\left(\frac4{4-q}|d\psi|^2+K\psi^2\right)
 \ge\int_\Sigma\left(\frac{D_\beta(h,T)}2+
 \frac{3-q}{4-q}\mu^2+\nu\mu\right)\psi^2. \tag{R1}
\]
The formula holds for compactly supported test functions. To obtain it directly from Lemma 2.4, complete its tangential square and the normal quadratic:
\[
 \tfrac34(\mu-qz)^2+q(\mu-qz)z+qz^2
 =q(1-q/4)\left(z-\frac\mu{4-q}\right)^2+
 \frac{3-q}{4-q}\mu^2,\qquad z=\nu\log u.
\]
The sign on the right of (R1) is \(+\nu\mu\). The trace-free second-fundamental-form term is nonnegative and may be dropped. These local calculations work on relatively compact domains and use densities and a two-sided normal; global orientation, torus topology, and completeness of the sheet are unnecessary.

Set
\[
 \gamma_s=(4-q)/2=2-a/4,\qquad
 c_\beta=2(3-q)/(4-q)=2(6-a)/(8-a).
\]
If \(D_\beta+c_\beta\mu^2-2|d\mu|\ge c>0\), twice (R1) implies
\[
 -\frac4{\gamma_s}\Delta_\Sigma+R_\Sigma\ge c.
\]
On a closed surface or a relatively compact smooth larger domain, take a positive first eigenfunction \(v\), and put \(U=-2\gamma_s^{-1}\log v\). Then
\[
 D_{\gamma_s}(k,U)=R_k-\frac4{\gamma_s}\frac{\Delta v}{v}\ge c.
\]
This \(U\) need not equal the candidate's particular \(T-\log w\); it supplies the same **sufficient interface**. S's existing conformal-index argument, retaining the coefficient, now gives
\[
 L\le2\pi\sqrt{\frac{\gamma_s}{(2\gamma_s-1)c}}
   =\frac{2\pi s_a}{\sqrt c}.
\]
Its only changed inequality is
\[
 X^2-zYX-\frac{2\gamma_s-1}{4}z^2Y^2
 =\frac{2\gamma_s}{2\gamma_s-1}X^2-
 \frac{2\gamma_s-1}{4}
 \left(zY+\frac{2X}{2\gamma_s-1}\right)^2.
\]
Use the eigenfunction on a larger domain than the compact path region, just as S lem:stable-exit does. No conformal completeness of an open sheet is needed. Integrating on a closed surface gives positive Euler characteristic, hence sphere or projective plane.

This recovers every changed closed-diameter, topology, and local-exit input to the cutting argument. The candidate's pointwise square identity is correct and clean, but its needed consequence is already Chai–Sun's general weighted stability estimate followed by S's index method. It is not a new curvature-transfer mechanism.

## 5. The remaining seam check and global assembly

The reflected collar is the strongest remaining claim to nonroutine content. It is an essential check: simply citing S's coefficient-one smoothing lemma would be invalid. But it uses **the same variables, mollifier, cutoff, compactness argument, and metric comparison** as S.

S already introduces \(m=\log(dA_{k(r)}/dA_{k(0)})-T\), with \(m'(0)=0\) from weighted minimality. This cancels the potentially singular second normal metric derivative. Writing \(A=k'/2\), the generalized normal contribution is
\[
 -|A|^2-(m')^2-2m''+(1-\beta)(\operatorname{tr}A-m')^2.
\]
At a seam-approaching sequence \(m'\to0\), and the averaged first derivative is \(\kappa A+o(1)\), \(|\kappa|\le1\). Thus
\[
 Q_\beta(A)=-|A_0|^2-(\beta-\tfrac12)(\operatorname{tr}A)^2,
\]
\[
 Q_\beta(\kappa A)-Q_\beta(A)
 =(1-\kappa^2)(|A_0|^2+(\beta-\tfrac12)(\operatorname{tr}A)^2)\ge0.
\]
The requested range has \(\beta>2/3>1/2\). This extends S's negative-squared-norm argument by an elementary trace decomposition. It introduces no new smoothing construction or analytic estimate. Separate compact-collar choices at infinity are also already in S.

Once this and (R1) are available, the remainder is S's proof with a single enlarged length scale:

- Positive-ground-state exhaustion works for each fixed positive coefficient with local Harnack estimates.
- Maximal cuts, mod-two local-finiteness detection, antisymmetric integral currents on the orientation cover, boundary retraction, and neat separation use the replaced surface estimates and smooth positive density.
- The pressure \(s_a\cot(\pi(\rho-A)/(B-A))\) on a band wider than \(69s_a\) gives the same \(1/4\) reserve. The derivative and quadratic-pressure coefficient scale together.
- The common interface, complementary-region tree, multiplicity-two slab cover, grouped compact partition supports, locally finite nerve, and anchored collar homotopy are S §§5–6. The bound becomes \(440s_a+2(2\pi+2)s_a<500s_a\).

The difficult global generality cannot be credited again as a new I14 mechanism: the pinned source expressly establishes it. Conversely, the torical-band theorem **alone** does not imply W. The reduction uses S's complete proof architecture and the coefficient-compatible seam check.

## 6. Other strongest shortcuts tested

**Monotonicity and homothety fail as black-box reductions.** For \(a>4\), subtracting \((a-4)\int|d\phi|^2\) need not preserve a lower bound. Also \(D_1=D_\beta-(1-\beta)|dT|^2\) has an uncontrolled loss. Homothety leaves \(a\) unchanged.

**Torus stabilization does not reach this coefficient.** For \(P=\sum p_i\), the multiple-warp scalar is \(R-2\Delta P-|dP|^2-\sum|dp_i|^2\). Equal splitting approaches coefficient one on the total log-gradient from above, not the required \(\beta<1\). Gromov's Theorem (G), C's interface, and P's stabilized construction therefore cannot simply be invoked. Adding a circle to use C in dimension four gives a two-dimensional target, not automatically a graph.

**A conformal PSC metric is insufficient.** No global conformal-factor bound supplies completeness or the needed original-distance comparison. Closed-manifold topological classification likewise gives no quantitative control of the metric in W.

**Band obstructions are insufficient by themselves.** An arbitrary slab or cut piece need not be overtorical, \(\widehat A\)-overtorical, or free of spherical homology. HKKZ's global scalar lower bound is not assumed. Exhausting by bands does not furnish compatible small whole fibers.

**Componentwise results must be compared fairly.** A real-valued function's bounded connected level components do not bound its entire fibers, but a proper Morse function admits the relevant Reeb-graph interpretation. Thus the connected-component wording alone is not a novelty argument against Liokumovich–Wang. Its pointwise scalar hypothesis is the actual difference.

**Neither exhaustion nor the orientation cover gives automatic descent.** Unrelated compact graph maps need not assemble into a locally finite target with uniform whole fibers. A graph map upstairs need not descend equivariantly, and collapsing deck-related images can join far-apart pieces. W avoids those mistakes by using S's existing direct construction.

These are genuine barriers to a **theorem-statement** shortcut. They do not establish nonroutine significance after the strongest local literature and complete S proof are combined.

## 7. Proof disposition and endpoint

I preserve R2's PASS, including its two precise clarifications:

1. The compact current-minimization region contains **both the initial competitor and the full intrinsic closed \(10s_a\)-neighborhood** of the detecting-form support. This is explicit in S lem:closed-separation and makes the competitor class nonempty.
2. On \(B\times[0,1]\), zero is the cut and one the interior end. The homotopy occupies \([1/2,1]\); the new path occupies \([0,1/2]\). This resolves the candidate's ambiguous inner/outer wording by the construction it expressly invokes.

I found no additional proof defect. The pressure sign, open-sheet local exit, nonzero second fundamental form at the seam, compact localization, whole-fiber anchoring, and local finiteness remain valid. A technical-only significance verdict does not reverse a proof PASS.

For the endpoint, write \(g=dt^2+f(t)^2|dx|^2\), \(q_0=f'/f\), \(u=f^{-1}\). Then
\[
 R=-4q_0'-6q_0^2,\qquad
 \Delta u/u=-q_0'-q_0^2,\qquad
 (-6\Delta+R)u/u=2q_0'.
\]
Taking \(f=e^{t^2}\) gives four. The ground-state transform establishes the quadratic inequality without \(u\in L^2\), and \(g\ge g_{\rm Eucl}\) gives completeness. A graph map lifts to a tree. On each Euclidean radius-\(R\) sphere, its compact image lies in a finite subtree, which embeds in the plane. Borsuk–Ulam gives a same-fiber antipodal pair at distance at least \(2R\). Every map therefore has unbounded supremum of entire-fiber diameters; one fixed fiber need not contain all the pairs.

I did not locate the identical Gaussian example as a stated result in the checked sources. Its construction is nevertheless an elementary borderline warped-product cancellation followed by a standard topological width obstruction. Given the known threshold, it is useful sharpness documentation, not a separate substantial mechanism. The higher-dimensional warped calculation is not another finding.

## 8. Final significance boundary and reproducibility

**Why TECHNICAL ONLY:** the new statement broadens a meaningful theorem, but the necessary local estimate is present in current primary literature; the noncompact, nonorientable, entire-fiber machinery is inherited from the stipulated source; and the residual seam task is an elementary quadratic extension of that source's same smoothing proof. Careful verification is necessary, but it does not create an additional research mechanism. Under a permissive “new statement with proof” criterion this is a legitimate extension. Under the requested substantial/nonroutine gate it contributes **zero** to the accepted-finding count.

**Why not DUPLICATE:** no exact full-scope theorem was found, and the band theorems do not imply W alone. **Why not GAP:** the candidate correctly supplies the needed interface and seam arguments, with R2's conventions. This verdict is a reasoned significance judgment, not a proof that every conceivable argument is routine or a claim that no publication could value this extension.

The [reduction diagnostic](../experiments/i14_spectral_width_novelty_r3/check_reductions.py) checks ten exact rational polynomial identities: parameter conversion, the two Chai–Sun squares, scale equality, the seam form and gain for an arbitrary symmetric \(2\times2\) tensor, collar cancellation, index completion, and endpoint cancellation. [Results](../experiments/i14_spectral_width_novelty_r3/reduction-checks.json) record its executable hash and Python version. There is no parameter sampling. These identities do not certify geometric existence or significance. An initial SymPy-based attempt could not run because SymPy is absent; the delivered standard-library diagnostic passed. Its polynomial arithmetic is attributed to the frozen R2 diagnostic.

The [artifact seal](../sources/i14_spectral_width_novelty_r3/artifact-seal.json) covers this report, frozen inputs, acquisition/search scripts, corpus, primary captures, query records, manifests, and diagnostics. It excludes its own hash. The associated verification checks unchanged original inputs and all pinned blob identities.

**Final disposition: TECHNICAL ONLY; proof PASS retained; no acceptance-count increment; worldwide priority unverified.**
