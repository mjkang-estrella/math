# I14 sharp spectral graph width — independent proof review R2

**Verdict: PASS, under the stipulated upstream premises.** The complete candidate proves Theorem W for every fixed \(4\le a<6\), including local finiteness of the target and the diameter bound on **entire** fibers, and proves the proposed failure for every \(a\ge6\). I found no blocking gap in the new transfer. The expansions below make explicit the delicate source substitutions and two harmless wording conventions. They do not change the candidate.

This is a proof verdict, **not a novelty/significance certification or project acceptance**. It neither credits the already known threshold six as new nor adds an accepted finding to R006, R008, R009. The ten audit items below are checks of one proposed result, not ten research findings. The requested ten-finding project target must not affect the proof verdict.

Review date: 2026-10-08. No subagents were used. Only this review and the assigned frontier/{sources,experiments}/i14_spectral_width_r2/ directories were written; no staging, commit, shared-index edit, or candidate edit was performed.

The reviewed candidate is frontier/iterations/i14-sharp-spectral-width.md, SHA-256:

    22557dd8004e06a0a300919daeaaeb7393319906907b2fe2381f0999b2a0c052

The immutable source revision is openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. I read AGENTS.md, sources/upstream.json, the relevant catalogue entries, **all six complete sections** of the dimension-three manuscript S, and the companion C's actual main and strongest applicable interface/reserve/stretching/assembly statements. The formal claims of the pinned repository are accepted as true; this review checks the new deductions and the applicability of lower-level constructions, not upstream truth.

All fifteen cached TeX files were independently SHA-256 checked and Git-blob checked against both the supplied manifest and the complete, nontruncated sources/preprints-tree.json inventory. The inventory contains exactly these fifteen build TeX files for the two titles. Twenty-eight inputs, including the candidate, instructions, inventory, all fifteen TeX files, both literature PDFs/texts, and the parent's diagnostics, are frozen in the review's source directory. [Input manifest](../sources/i14_spectral_width_r2/input-manifest.json), SHA-256:

    177450b5b9487eb042bafc2cf36f75f42085bd001b59952c476d8032690c818c

Here S means *Spectral scalar curvature and Urysohn width in dimension three*; C means *Spectral scalar curvature and uniform Urysohn width*, both October 5, 2026. The manifest supplies exact original paths, pinned URLs through its frozen parent manifest, Git blobs, and byte hashes. The [dependency ledger](../sources/i14_spectral_width_r2/dependencies.json) records which contracts are reused and which estimates are newly proved.

## 1. Scope, spectral normalization, and the actual source contracts

Candidate §§1–3, particularly (3.1)–(3.2), are correct. The asserted conclusion is a continuous map to a locally finite simplicial graph with its usual polyhedral topology, every entire fiber having \(g\)-diameter at most

\[
500\lambda^{-1/2}\sqrt{\frac{8-a}{2(6-a)}}.
\]

The assumptions are precisely a complete connected smooth boundaryless three-manifold and the compact-test-function quadratic inequality. No ambient orientability, spin, global curvature bound, bounded geometry, or weight bound is used.

S 01-introduction.tex, thm:main, assumes coefficient **4**, not arbitrary \(a<6\). S 06-graph-gluing.tex actually constructs a locally finite graph, although its main statement does not separately advertise that strengthening. C introduction.tex, thm:main, assumes coefficient 4 and \(n\ge4\). C interface:width requires \(n\ge4\), stretched separations and stabilized scalar data; pre:reserve preserves the input \(D_1(h,w)\) while adding a reserve; stretch:local and assembly:round operate with that same \(D_1\). None supplies this three-dimensional conclusion directly from \(D_\beta\ge1\). In fact \(D_1=D_\beta-(1-\beta)|dT|^2\), with no lower bound supplied for the last expression. There is no valid monotonicity shortcut for \(a>4\).

For \(g'=\lambda g\), both scalar curvature and the Laplacian acquire the factor \(\lambda^{-1}\), while distance acquires \(\sqrt\lambda\). Thus it is correct to prove the normalized theorem and divide the final diameter by \(\sqrt\lambda\).

The positive-weight exhaustion in S lem:positive-weight transfers to any fixed positive \(a\): Dirichlet eigenvalues decrease, lie in a fixed finite interval with lower endpoint 1, and the normalized eigenfunctions have locally uniform Harnack and interior estimates. On each fixed compact region the potential is bounded. Neither the Harnack constants nor derivatives of the limiting positive function need uniform control at infinity. Directly,

\[
2\Delta\bigl(-\tfrac a2\log u\bigr)
-\tfrac4a\bigl|d(-\tfrac a2\log u)\bigr|^2
=-a\Delta u/u.
\]

Thus the candidate obtains a smooth weight with \(D_\beta\ge1\). The range relations are

\[
\beta=4/a\in(2/3,1],\quad
\gamma=(2\beta-1)/\beta\in(1/2,1],\quad
c_\beta=(3\beta-2)/(2\beta-1)>0,\quad
s^2=\gamma/(2\gamma-1)=1/c_\beta\ge1.
\]

For \(0\le a\le4\), adding \((4-a)\int|d\phi|^2\) really does give S's coefficient-4 hypothesis. This is a different, valid direction of monotonicity.

## 2. Jacobi signs and the full universal square identity

Candidate §4, lines 79–133, passes. I independently checked the Gauss and normal Laplacian decomposition, not merely the already completed square. With the convention \(B(V,W)=h(\nabla_V\nu,W)\), variation of \(H-\nu T-\mu\) in normal speed \(f\) is

\[
-\Delta_{\Sigma,T}f-
(\operatorname{Ric}_{\nu\nu}+\operatorname{Hess}T_{\nu\nu}+|B|^2+\nu\mu)f.
\]

Consequently the pressure derivative is **plus** \(\nu\mu\) in \(Q\), and **plus** \(2\nu\mu\) after curvature transfer. Stability here is unconstrained stability, as required by the positive first Jacobi eigenfunction.

Let its eigenvalue be \(\eta\ge0\), \(p=\log w\), \(x=d_\Sigma T\), \(y=dp\), and \(v=\nu T\). The exact identity, retaining the eigenvalue remainder omitted by the candidate's inequality, is

\[
\begin{aligned}
D_\gamma(k,T-p)-D_\beta(h,T)
={}&(\beta-\gamma)|x|^2+2(\gamma-1)\langle x,y\rangle
 +(2-\gamma)|y|^2\\
&+\mu^2+(\beta-1)v^2+|B|^2+2\nu\mu+2\eta.
\end{aligned}
\]

For the stated \(\gamma\), its tangential quadratic expression is exactly \(\beta^{-1}|y+(\beta-1)x|^2\). Also, with \(H=\mu+v\),

\[
\mu^2+(\beta-1)v^2+\tfrac12(\mu+v)^2
=(\beta-\tfrac12)\left(v+\frac{\mu}{2\beta-1}\right)^2
+\frac{3\beta-2}{2\beta-1}\mu^2.
\]

Adding \(|B_0|^2\) proves (4.2). All discarded coefficients have the asserted signs on the entire interval, including \(a=4\). No coefficient-4 surface theorem is silently reapplied to \(D_\beta\). These identities apply equally to two-sided surfaces in nonorientable ambient manifolds; the normal bundle, not an ambient orientation, is what is needed.

## 3. Geodesic index, closed topology, and the local exit construction

Candidate §5 passes. For an index-stable segment in \(e^{-2U}k\), the Gaussian curvature formula gives exactly the candidate's index integral. A useful explicit completion, writing \(d=2\gamma-1>0\), is

\[
(\psi')^2-U'\psi\psi'-\frac d4(U')^2\psi^2
=\frac{2\gamma}{d}(\psi')^2
-\frac d4\left(U'\psi+\frac{2\psi'}d\right)^2.
\]

The remaining term is \(-\gamma(|dU|^2-(U')^2)\psi^2/2\le0\). The sine test therefore yields \(L\le2\pi\sqrt{\gamma/(dc)}=2\pi s/\sqrt c\). The calculation works for every \(\gamma>1/2\); it does not require \(\gamma=1\), or \(\gamma\ge1\). At \(\gamma=1/2\) it supplies no finite estimate, consistently with the endpoint.

On a closed surface, compactness makes the conformal metric complete, and the bound concerns the original induced metric \(k\), since it bounds \(k\)-length of a connecting path. Integration gives \(4\pi\chi\ge c\operatorname{Area}+\gamma\int|dU|^2>0\); densities or the orientation double cover justify Gauss–Bonnet without orientability. The surface is \(S^2\) or \(\mathbb{RP}^2\).

For an open sheet, the Jacobi eigenfunction must be taken on \(\Omega_1\supset\overline\Omega_0\). Its logarithm may diverge at \(\partial\Omega_1\), but is smooth on a neighborhood of \(\overline\Omega_0\). The compact Riemannian manifold with boundary \(\overline\Omega_0\) has a length minimizer from the chosen point to its boundary; stopping at its first boundary contact gives an interior geodesic and all required interior index tests. Hence the same \(k\)-length bound holds. The candidate follows this precise argument. Completeness of an open conformal sheet is never assumed or inferred.

## 4. Maximal family, nonorientable currents, detection, and neat separation

Candidate §6, lines 182–186, legitimately transfers the **proof** of S 03-cutting.tex; it does not invoke its coefficient-4 proposition with mismatched hypotheses. The two curvature inputs to that proof are now supplied independently: closed diameter/topology and local exit.

For completeness, the construction has the following dependency chain. Zorn's lemma applies because admissibility is tested on finite subfamilies. Every surface meeting a compact set lies in its compact closed \(2\pi s\)-neighborhood, by completeness of \(M\). For any finite subfamily, loops through the connected complement detect the mod-two classes independently. All surfaces in question lie in one compact smooth neighborhood, whose \(H_2(-;\mathbb Z/2)\) is finite dimensional; its image bounds the number of independent ambient classes. Thus the family is locally finite. Local cutting charts and a finite cover over each compact set give properness of the gluing quotient, and bounded closed subsets of a cut piece are compact in its intrinsic metric.

A nonseparating cooriented interior surface gives an algebraically nonzero crossing loop. Doubling an orientation-reversing loop and perturbing if necessary produces the orientation-preserving loop used by S. On the orientation double cover, the full lifted integral cycle is antisymmetric. A compactly supported closed Thom 2-form near one lift of the loop has nonzero evaluation. The minimization region must contain **both the initial competitor and the full intrinsic closed \(10s\)-neighborhood of the form support**; properness gives such a compact region. This explicit inclusion of the initial competitor is part of the cited source construction, not an extra restriction on the candidate's theorem.

The compact constrained integral-current minimization depends only on a smooth positive area density. Since \(e^{-T}g\) has precisely the weighted surface area, the same problem is available. Exactness of the form in small balls and paired opposite changes on disjoint deck translates preserve both constraints. At a cut boundary, the source's local minimal-disk foliation and its area-nonincreasing retraction give comparisons in a full smooth extension. This input depends on weighted minimality and local smoothness, not \(D_1\ge1\). In particular there is no unsupported appeal to regularity for a one-sided obstacle problem.

The source's full-neighborhood current regularity and maximum principle now give embedded sheets, locally constant multiplicities, and no crossing of the boundary. Ambient orientation and current orientation both reverse under the deck map, so the normal descends. The sheets are two-sided and stable under compactly supported variations preserving the detecting evaluation by the homotopy formula. This is the precise point at which ordinary mod-two minimization alone would have been insufficient; the candidate retains the integral-current construction.

A component meeting the form support has compact intersection with the intrinsic closed \(10s\)-ball around a meeting point: the support and its components are closed in the regular region, and their embedded topology is the subspace topology. If this component were noncompact, choose a relatively compact smooth domain containing that intersection and then a larger such domain. The boundary is more than \(10s\) away, contrary to the local exit path of length at most \(2\pi s<10s\). Thus the detected components are closed. There are finitely many near the compact form support by local regularity. If they all separated, compactly supported Stokes on their lifted sides would annihilate the detecting evaluation. A detected nonseparating component can therefore be added to the maximal family, a contradiction.

Finally, every boundary component has finite fundamental group. The source's circle-valued map of a nonseparating neat hypersurface has real lifts on boundary collars; only finitely many collars meet its compact support. Cutting these lifts off makes the map constant near all boundary components without changing its nonzero loop degree. A regular nonconstant level would give a nonseparating closed interior component. This establishes the required neat separation. No further coefficient, orientability, or global scalar hypothesis enters.

## 5. Even smoothing with a nonzero second fundamental form

Candidate (6.1)–(6.3), lines 188–213, pass. This is a genuine additional check needed to transfer S lem:double-smoothing.

Set \(A=k'/2\), \(H=\operatorname{tr}_kA\), and \(m'=H-T'\). The normal part of \(D_\beta\) before substitution is

\[
-|A|^2-H^2-2H'+2T''+2HT'-\beta(T')^2.
\]

Putting \(T'=H-m'\), \(T''=H'-m''\) yields exactly

\[
-|A|^2-(m')^2-2m''+(1-\beta)(H-m')^2.
\]

The cancellation of \(H'\) is essential: \(k''\) need not stay bounded when a non-totally-geodesic boundary is reflected. Weighted minimality gives \(m'(0)=0\) as an identity along the whole boundary, so the even extension of \(m\) is \(C^2\), with the needed tangential derivatives, whereas that of \(k\) is only locally Lipschitz in its normal variable. Normal mollification therefore gives uniform convergence of \(m''\) and of the tangential slice terms, and \(m'_\delta\to0\) at seam-approaching sequences.

For a sequence \((x_j,r_j,\delta_j)\to(x,0,0)\), near the seam the cutoff is identically one and

\[
A_{\delta_j}(x_j,r_j)=\kappa_j A(x,0)+o(1),\qquad -1\le\kappa_j\le1.
\]

The averaging takes place in fixed collar coordinates; \(k_{\delta_j}(x_j,r_j)\to k(x,0)\). The tensors being averaged are bounded locally, so replacing the varying inverse metrics by the limit metric changes the quadratic expression by \(o(1)\). Relative to that limit metric,

\[
Q_\beta(A)=-|A_0|^2-(\beta-\tfrac12)H^2\le0,
\qquad
Q_\beta(\kappa A)-Q_\beta(A)
=(1-\kappa^2)(|A_0|^2+(\beta-\tfrac12)H^2)\ge0.
\]

This supplies an explicit version of the candidate's Jensen step for every symmetric \(A\), including nonzero trace and off-diagonal components. The terms involving \(m'\) vanish at the seam. The lower limit is at least the one-sided original \(D_\beta\ge1\). Away from the seam, including the fixed cutoff transition, convergence is smooth. A compactness/contradiction argument on each changed compact collar therefore supplies one sufficiently small smoothing radius for the bound \(1/2\) throughout that collar. Uniform metric convergence supplies the stated factor-four comparison. Separately chosen radii on disjoint locally finite collars give global smooth even data. There is no need to set \(A=0\), to smooth \(T\) independently, or to posit uniform control of any derivatives at infinity.

## 6. Pressure derivative, actual barriers, and the reflected minimizer

Candidate §7, lines 217–242, passes. Properness is retained under \(g/4\le h\le4g\). Reflection and folding work in the smooth even metric, so the even radial function remains proper and 1-Lipschitz. The source's local partition smoothing gives the required approximation; indeed \(s\ge1\), so its original error less than one already suffices.

Writing \(w=B-A>69s\),

\[
d\mu=-\frac{\pi s}{w}\left(1+\frac{\mu^2}{s^2}\right)d\rho,
\quad
2|d\mu|\le\frac{4\pi s}{w}(1+c_\beta\mu^2)
<\tfrac14(1+c_\beta\mu^2).
\]

The amplitude \(s\) in the pressure is correct; the derivative bound and the transferred \(\mu^2\) coefficient scale together. Thus \(D_\beta+c_\beta\mu^2-2|d\mu|\ge1/4+3c_\beta\mu^2/4\).

Here are the actual barrier details behind the candidate's source reference. Pick regular compact levels \(A,B\). For sufficiently small \(\epsilon>0\), constrain the full phase to include \(\{\rho<A+\epsilon\}\) and exclude \(\{\rho>B-\epsilon\}\). Extend the pressure smoothly, evenly, and with compact support, keeping its original values on a neighborhood of the entire constrained closed band. BV compactness and lower semicontinuity apply on this fixed compact region, where the density has positive upper and lower bounds. The perimeter lattice inequality makes the union with the reflected minimizer another minimizer, now invariant under reflection.

Near \(A\), a fixed smooth compactly supported field equal to \(\nabla\rho/|d\rho|\) has bounded weighted divergence. On \(A+\epsilon\le\rho<A+2\epsilon\), the pressure tends uniformly to positive infinity as \(\epsilon\downarrow0\). Union with that larger sublevel strictly lowers perimeter minus pressure-volume unless the missing phase has zero measure. At the outer end apply the same argument to the complement and \(-\mu\). These comparisons give actual clearance from both constraints. The extension is allowed to depend on \(\epsilon\); its equality to the original cotangent on these shells is what matters.

Full local minimization, hence smooth two-sided perimeter support and unconstrained stability, follows on a neighborhood of every interface point. The generalized closed-surface estimate gives \(4\pi s\) for each connected closed interface. Reflection preserves the phases and hence its outward normal. A fixed point of reflection has normal tangent to the seam; therefore the interface meets the seam transversely, rather than lying in it. Restriction and folding give the asserted finite neat family with ambient intrinsic-\(P\) diameter at most \(4\pi s\). Its location follows from \(|\rho-r|<s\). The basepoint is in the inner phase since \(\rho(o)<s<A\), and \(r>\ell\) is in the outer phase since \(\rho>\ell-s>B\).

## 7. One common interface and the entire connected slab

Candidate lines 244–248 pass. S lem:region-tree uses only connectedness, two-sided neat bicollars, compactness, disjointness, and individual separation. Its finite complementary-region graph is a tree because every edge is a bridge. The slab component misses all interfaces and is connected, so it lies in one complementary region. Its phase differs from that of the basepoint. One edge of the tree path therefore selects **the same** interface \(F_i\) for all points of this slab component.

Proper length spaces are geodesic. For a minimizing basepoint-to-\(x\) path and a crossing \(z_x\in F_i\), its remaining length is exactly \(r(x)-r(z_x)<93s\). The ambient intrinsic-\(P\) distance between two crossings is at most \(4\pi s\); it need not be intrinsic distance within the folded \(F_i\). Thus the entire component, not just an individual path or one local part, has diameter below \(186s+4\pi s<220s\). For \(\ell<100s\), the basepoint triangle bound gives \(204s\). The factor two on projection back to \(M\) gives \(440s\).

The intervals centered at \(js\) with half-width \(3s/4\) cover all nonnegative radii and have multiplicity at most two. Their connected slab components are open because the cut manifold is locally path connected, and have compact closures by properness. No local finiteness of this initial component cover is claimed or needed.

## 8. Grouped partition, anchored homotopies, and entire fibers

Candidate lines 248–260 pass against the complete S 06-graph-gluing.tex. The initial refinement has a locally finite family of **compact supports**, each contained in an assigned slab component. Only finitely many can be assigned to a given component: they all meet its compact closure. Grouping therefore preserves compact supports and local finiteness. Multiplicity two is inherited from the original component cover, not asserted for an arbitrary refinement. The positive-coordinate nerve is a locally finite graph because a compact support meets only finitely many other supports. The map is locally in a finite subcomplex, giving continuity in the usual polyhedral topology.

For a point in the relative interior of an old simplex, any one vertex of that simplex is an anchor: every unmodified preimage has that partition coordinate positive and hence lies in the same cover set. The source's smallest subcomplex containing a boundary-collar inner-end image is finite and connected. Every vertex of it has a positive original coordinate at some point on that same inner end, including endpoints of edges whose interiors meet the image. This property survives taking a nullhomotopy within that subcomplex.

A boundary component has finite fundamental group, while the finite graph's fundamental group is free and torsion free. Its map lifts to a tree and contracts there, then projects to a homotopy wholly inside the chosen subgraph. The lift need not contract inside the actual image, and the proof does not require that stronger assertion.

To remove possible ambiguity in the candidate's phrase “outer half/inner half” at line 254, use exactly the source coordinates: on \(B\times[0,1]\), \(0\) is the cut and \(1\) the interior end; the homotopy occupies \(1/2\le t\le1\), and the added path occupies \(0\le t\le1/2\). The two cut copies take the same midpoint value. This is a coordinate clarification of the expressly retained source construction, not a gap requiring a new construction. Three edges and two fresh vertices produce a genuine simplicial graph even if both old endpoints agree. Local finiteness at an old vertex follows because every attached collar meets its compact original partition support.

The projected union of a pair of collars has diameter \(L_s=(2\pi+2)s\): project normally to the cut surface, join there, and add normal segments. If \(y\) is old, every modified collar point in its fiber is within \(L_s\) of the **same** anchored cover set \(q(U_v)\); the vertex \(v\) is fixed by the simplex containing \(y\), regardless of how many collars map there. Hence

\[
\operatorname{diam} f^{-1}(y)\le440s+2L_s=(444+4\pi)s<500s.
\]

If \(y\) is new, it belongs to exactly one added path away from the old graph, so all its preimages lie in that one paired collar union. Identifying the two cut copies via the quotient gives continuity on \(M\). This checks whole fibers, not merely connected components, and preserves the locally finite target. Rescaling gives exactly W.

## 9. Complete endpoint metric, ground-state transform, and infinite width

Candidate §8 passes independently. Put \(f(t)=e^{t^2}\) and \(u=f^{-1}\). For a warped product with two flat transverse directions, \(q=f'/f=2t\),

\[
\operatorname{Scal}=-4q'-6q^2=-8-24t^2,
\qquad
\Delta u/u=-q'-q^2=-2-4t^2.
\]

Thus \((-6\Delta+\operatorname{Scal}-4)u=0\). Completeness follows from \(g\ge g_{\mathrm{Eucl}}\) and local smooth metric equivalence at a Euclidean limit. For compactly supported \(\phi=u\psi\), integration by parts gives

\[
\int\left(6|d\phi|^2+(\operatorname{Scal}-4)\phi^2\right)
=6\int u^2|d\psi|^2\ge0.
\]

All integrals here use \(d\mathrm{vol}_g\). There are no boundary terms because \(\psi\) is compactly supported. In fact \(u^2d\mathrm{vol}_g=dt\,dx\,dy\), so \(u\) is not globally square integrable; this does not affect the identity. Adding \((a-6)\int|d\phi|^2\) proves the same lower bound 4 for every \(a\ge6\).

For any continuous graph map, the connected image lies in one graph component. As a graph with its usual CW topology it has a universal covering tree, and simple connectedness of \(\mathbb R^3\) gives a lift. For a sphere of Euclidean radius \(R\), its lifted compact image lies in a finite subtree. One can justify the compact-subcomplex step directly: if a compact set met infinitely many distinct open cells, choose one point in each of countably many such cells. Every subset of the selected points is closed by the weak topology, since every closed cell meets only finitely of them. They would form an infinite closed discrete subspace of a compact space, a contradiction. Add the finitely many tree paths needed to connect the resulting finite subcomplex.

A finite tree embeds in \(\mathbb R^2\). Borsuk–Ulam applied to the sphere followed by this embedding gives antipodal points with the same lifted image and therefore the same original graph image. Their \(g\)-distance is at least their Euclidean distance \(2R\). For every graph map the supremum of entire-fiber diameters is therefore infinite. The proof does **not** claim that one fixed fiber contains all these pairs; that stronger assertion is unnecessary. It applies in particular to locally finite graphs. The topology specification is essential to the stated general CW argument and is present in the theorem.

The auxiliary dimension-\(m+1\) computation is also correct: with \(u=f^{-m/2}\), scalar curvature is \(-2mq'-m(m+1)q^2\), and \(\Delta u/u=-mq'/2-m^2q^2/4\). At \(a=4(m+1)/m\), their difference is \(2q'=4\). No positive higher-dimensional theorem is inferred from this calculation.

## 10. Prior-art limits, diagnostics, and final proof disposition

The cached primary copies of [Chai–Sun, arXiv:2604.04052v1](https://arxiv.org/abs/2604.04052v1) and [Hirsch–Kazaras–Khuri–Zhang](https://www.math.stonybrook.edu/~khuri/Blackhole_existence.pdf) were read at the relevant statements; direct browser opens also confirmed the primary sources. Chai–Sun's parameter is \(a/2\). Its Theorem 1.4 concerns complete oriented stable surfaces, 1.12 torical bands with weighted boundary inequalities, and 1.20–1.23 topologically restricted splitting/Geroch consequences. None is the arbitrary-manifold, whole-fiber graph statement audited here.

HKKZ Theorem 1.1 already has \(c>1/6\), equivalent to \(a<6\), and its three-dimensional end-distance scale becomes exactly \(2\pi s_a/\sqrt\lambda\) upon setting \(c=1/a\), \(\Lambda_c=\lambda/a\). Thus even this coefficient-dependent length scale is not to be credited as newly discovered. That theorem requires orientation, no spherical second-homology classes, a global scalar lower bound, and a specified separation of ends. Its Theorem 1.2 requires a compact odd-dimensional spin \(\widehat A\)-overtorical band. These hypotheses do not follow from W. In particular W permits arbitrarily negative scalar curvature, and the endpoint example has scalar curvature unbounded below. I found no direct reduction from these actual statements; this is not an exhaustive novelty search or significance judgment.

The [independent diagnostic](../experiments/i14_spectral_width_r2/check.py) uses only Python's standard library. It verifies **14 exact formal polynomial identities**, after clearing the stated nonzero denominators, and **5 uniform constant inequalities** using \(\pi<22/7\). These include the unsimplified Gauss/Jacobi identity with its eigenvalue remainder, both surface squares, the index square, the collar cancellation and non-diagonal seam form, the pressure derivative/reserve, and the endpoint formulas. This is coefficientwise rational polynomial arithmetic, not a finite parameter sweep. [Results](../experiments/i14_spectral_width_r2/results.json) record the Python version and script hash. Reproduce with:

    python frontier/experiments/i14_spectral_width_r2/check.py

The parent's finite 3125/405/99 diagnostics were frozen as inputs, not treated as proof or rerun in its shared directory. The universal positivity ranges, compactness, current construction, smoothing limit, barriers, and topology are justified in the written audit above; computer identities do not certify those steps.

**Required mathematical repairs: none.** The explicit inclusion of the initial current competitor in the compact minimization region and the collar-coordinate convention above spell out details already contained in the source proofs the candidate invokes. Neither requires an added hypothesis, a changed constant, or a changed theorem. The complete transferred proof and endpoint argument pass under the stated premises. Separate final significance review remains necessary before project acceptance.

The [artifact seal](../sources/i14_spectral_width_r2/artifact-seal.json) hashes this review, the dependency ledger, diagnostics/results, input manifest and every frozen input. The seal omits its own hash to avoid self-reference. The review's candidate hash above identifies exactly which version this PASS covers.
