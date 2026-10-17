# Arithmetic discovery r15: two technical routes, no nomination

Status: **NO_NOMINATION_MULTIROUTE_CHECKPOINT**. Campaign remains 10 accepted toward 20. This is an author's discovery screen, not an independent proof or contribution verdict. No manuscript, formal theorem, acceptance, or upload is claimed.

The r15 brief was read completely. AGENTS and the source pin are unchanged: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The source theorems and their lower operations are stipulated truths. The complete 13,223-entry `sources/preprints-tree.json`, rather than the truncated root cache, supplies blob identities. Earlier complete context/history reads and r5–r14 exclusions remain in force. No old accepted/developed chain is nominated, and no work was done on O217 or the parent's family122 route. All new files are in this directory.

## 1. The unchanged family064 target

For **every** integer m≥1, take a holomorphic germ family F(x,t), x∈C³, over a neighborhood B of zero in C^m. Assume F(0,t)=0, each f_t has an isolated critical point at zero, and μ(f_t,0) is constant. The target is, after shrinking representatives and B, a parameter-preserving ambient right trivialization fixing the origin section, with jointly continuous map and inverse. No resolution, common Milnor radius, Whitney regularity, special singularity type, one-parameter restriction, or choice of covering base is added to this target.

R14 had paid the elementary transport argument *conditional* on a relative normal-crossing resolution, but had not established a general-base resolution. R15 resolves the relevant primary topological contract through King's original article. It does not claim a new general-base Laufer theorem.

### Original primary located and actually read

Henry C. King, **Topological Type in Families of Germs**, Invent. Math. 62 (1980), 1–13, DOI 10.1007/BF01391660. The Springer preview had not exposed the article, but the complete original scan was accessible from the Göttingen Digitalisierungszentrum:

https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0062/LOG_0007.pdf

The PDF has an added repository cover, so printed p1 is PDF p2. Printed pp1–4 and pp7–13 were visually read from rendered images, including **all of §§3–4**, the proofs of Theorems1–2. Printed pp5–6, part of the unrelated real counterexample, were not read. Text extraction recovers only the repository cover; it must not be mistaken for a text reading of the article. Rendered page images are retained. No OCR result is claimed (tesseract was unavailable).

The exact contracts are:

* King allows an arbitrary finite-dimensional real parameter space R^p. His definition on printed p1 is a jointly represented family, not an arbitrary assignment of germs.
* Theorem1, printed pp2–3, starts with no coalescence and an already continuous family of ambient zero-set homeomorphism germs. It produces a continuous family of right equivalences near the parameter origin. It **does not** start merely from equality of individual embedded types.
* Theorem2, printed p3, applies to conelike germs without coalescing critical points. It constructs comparison homology cobordisms W_z between links, well-defined up to attaching invertible cobordisms on either boundary. Its part3 states equivalence between a jointly continuous family of right equivalences and invertibility of every W_z in a small parameter ball.
* The detailed construction, printed pp10–12, transports a fixed outer link and function-level boundary by a parameterized submersion/isotopy construction, then removes a small conical neighborhood in the target fiber. Changing the transported collar does not change its isotopy class; changing either endpoint cone attaches an invertible cobordism. These are the choices whose independence is needed below.
* Printed p13 proves the necessity direction by choosing the transport from the trivializing homeomorphisms; W_z becomes the difference of two conical neighborhoods. For sufficiency, invertibility identifies punctured fibers with a fixed link times a half-open interval; the resulting family of zero-set homeomorphisms feeds Theorem1. Theorem1's proof ends with an **open embedding** of the total parameter product (printed p10), so the inverse is jointly continuous on its image. One need not infer inverse continuity from separate fiberwise bijectivity.

The frequently cited footnote in Greuel–Lossen–Shustin, *Introduction to Singularities and Deformations*, printed p267, was also read in context (web extraction lines14530–14614). Its terse statement that constant embedded type implies triviality suppresses distinctions made explicitly in King. It is not used as a replacement for the original theorem. Its whole book was not read or adopted.

### Operation-by-operation passage from the stipulated disk theorem

The following is a technical application of King, rather than a new resolution mechanism.

1. **Noncoalescence and conicality.** Constant Milnor number gives noncoalescence after shrinking, by conservation of the isolated critical-point multiplicity. Each isolated complex hypersurface singularity is conelike. These are precisely King's inputs, with real source dimension6, target dimension2, parameter dimension2m. His original discussion preceding Corollary3 explicitly identifies complex noncoalescence with μ-constancy. One cannot use Corollary3 itself: it excludes complex source dimension3.
2. **Fix the simultaneous comparison collars.** Apply King's construction over a sufficiently small ball in B, obtaining a common outer collar family and W_t. This is a construction on the punctured submersion locus and does not assume the conclusion.
3. **Restrict to one radial segment, without requiring a uniform disk trivialization in its direction.** For a fixed t in this ball, the holomorphic disk s↦st has constant μ. The stipulated pinned `thm:main` applies near each point of the compact real segment 0≤s≤1. A finite chain of such local right trivializations gives a right trivialization of the germ family over the entire segment. At a switching parameter s_i, compose the next local chart by its inverse at s_i and the previous endpoint chart; the two piecewise definitions agree there. Finitely many compositions permit a common smaller spatial representative, and inverse charts are glued in reverse order. This gives joint continuity along the segment and fixes the section. There is **no** assertion that these choices vary continuously with the direction t.
4. **Invertibility is an individual obstruction, not a selection of directional charts.** Restrict the comparison collars of step2 to this segment. Using the segment trivialization from step3, choose a smaller initial cone that fits its representative throughout the compact segment, and transport it by the trivialization. The endpoint cobordism for this choice is the difference of two conical neighborhoods, hence invertible, exactly as in King's necessity proof on p13. The original W_t differs only by the allowed choices of collars and endpoint cones; King's choice-independence proof on p12 attaches invertible cobordisms. Therefore the original W_t is invertible. Shrinking a cone for this fixed segment does not shrink the parameter ball in step2.
5. **Recover joint dependence once, through King.** Step4 applies to each t in the fixed small ball. Theorem2(3), not an assembly of directional charts, now supplies the jointly continuous ambient right trivialization over that ball. Normalize its central chart to the identity. The open embedding in Theorem1 supplies the jointly continuous inverse.

This keeps the full arbitrary-m target. The only substantive extra passage beyond the stipulated disk result is a classical theorem designed to perform precisely that passage. The finite segment gluing and the restriction/choice compatibility use King's stated and proved operations. A future independent audit may verify this technical corollary, but it is not offered as substantial new campaign work. In particular, **no simultaneous resolution over C^m has been proved here**. Laufer1983's full general-base statement remains unread and unused; Okuma2004's disk hypothesis is not enlarged.

### Source reads and feasibility

Pinned family064 introduction, §12 resolution, and §16 controlled-gradient appendix were read completely in r14; the introduction's complete theorem/historical portion was reread here. Their exact bytes are copied with receipts. Other numerical sections and the full §13 seam argument are not claimed as new reads. The source main theorem alone is used as the stipulated geometric input above.

Lean feasibility is limited: finite composition, inverse identities, and the logical reduction to an abstract comparison-cobordism interface can be formalized. Real topological submersions, conical neighborhoods, King's theorem, and the analytic source theorem would be explicit external assumptions. A formalized implication with those hypotheses would not be a formal proof of the analytic theorem. No Lean claim is made.

## 2. Distinct family050 interface: nefness versus small curvature deficits

The fresh interface examined is whether the source's fixed-twist strict-positivity failure can yield a genuinely new quantitative or approximation theorem. This was a prescreen, not a frozen candidate. Its natural examined statements are kept at full stated scope below, without substituting a smaller family after a difficulty.

Let S=P¹×P¹, P=O(1,1), f_m the coordinatewise mth-power map, and G the source's explicit rank-two graph bundle. The source supplies:

* `thm:main` / `prop:ampleness`: f_m^*G⊗P is ample for every positive integer m;
* `prop:limit`: positive metrics along an unbounded sequence of m yield a nonzero finite everywhere-defined fiberwise Hermitian quadratic psh function on G^∨;
* `prop:obstruction`: **every** such nonnegative quadratic psh function on G^∨ vanishes identically. This lower operation is stipulated as part of the source, not treated as new work.

### Two technical consequences and the exact changes to the proof

**A. A uniform linear twist barrier.** There is a real δ>0 such that, for every positive integer m and every integer a≥0 with a/m<δ, f_m^*G⊗P^a has no smooth Griffiths-semipositive Hermitian metric.

To see the proof and its contribution limit, replace the source trace summand's local mth root of f_m^*t by its ath power. For dual metrics on f_m^*G^∨⊗P^{-a}, the averaged squared norms are still nonnegative Hermitian quadratics and psh. Semipositivity suffices for the dual squared-norm Hessian calculation; strictness was not used in this step. The frame law is now

    q_{m,a,t'} = |g|^{2a/m} q_{m,a,t}.

If a_j/m_j→0, the transition errors tend to zero. Normalize using the background norm of t to the power −2a_j/m_j, and apply exactly the source's coefficient compactness, fixed-test-function noncollapse, radial convolution, polarization on every fiber, and overlap gluing. The output contradicts `prop:obstruction`.

The case a=0 is excluded directly: the finite trace of any such dual metric already has the untwisted frame law and is a globally defined nonzero quadratic psh function, with no limiting argument. If the uniform δ assertion failed, choose metric-bearing pairs with a_j/m_j<1/j. After excluding a_j=0, integrality implies m_j>j. Thus the required unbounded sequence exists, and the preceding limit excludes it. This proves the uniform assertion for all m, not just a tail. It supplies no explicit numerical value of δ.

**B. The graph bundle is nef but not approximately Griffiths-semipositive in fixed rank.** Nefness follows by finite descent of ampleness on P(G). If H is the tautological class and π:P(G)→S, the induced finite base change pulls back H+(1/m)π^*c1(P) to the tautological class for f_m^*G⊗P. Thus H+(1/m)π^*c1(P) is ample for each m, and H is nef.

Fix a smooth positive curvature form ω for P. There is c>0 such that no smooth Hermitian metric h on G has Griffiths curvature bounded below by −cω Id. Otherwise take h_j with lower bound −ε_jω Id, ε_j→0. On G^∨ the upper bound is ε_jω Id. Choose local potentials ψ_i with dd^cψ_i=ω. Multiplying the dual squared norms by exp(ε_jψ_i) makes them psh in each total-space chart (Chern curvature subtracts ε_j dd^cψ_i). Normalize the global dual norm to have maximum1 on a fixed background unit sphere bundle. The local transition errors exp(ε_j(ψ_i−ψ_k)) tend to1. The source's same noncollapse and everywhere-quadratic recovery then yield a forbidden nonzero q. This is a fixed-rank compactness argument already paid by §4.

Neither statement changes the source construction or resolves a new compactness obstruction. A uses the single substitution 1/m→a/m; B deletes the finite trace and uses vanishing local scalar corrections. They are therefore retained as **TECHNICAL_SOURCE_METHOD_EXTENSIONS**, not nominations. An explicit computable lower bound for δ or c would be a different, unpaid problem. The source explicitly provides an ineffective threshold; no effective estimate is derived here.

### Actual primary comparison

**Demailly–Peternell–Schneider**, *Compact complex manifolds with numerically effective tangent bundles*, JAG3 (1994),295–345: original author's manuscript downloaded from `https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/dps1.pdf`. The text from Definition1.9 through Proposition1.14 and its proof (extracted lines510–650, printed pp11–13) was read. Theorem1.12 characterizes nefness by metrics on **Sym^m E** with lower bound −mεω for sufficiently large m. Its converse uses a tautological metric, a barycenter modification providing relative positivity, and a symmetric-power metric construction. It does not produce arbitrarily small Griffiths deficits on E itself. Thus B does not contradict that theorem, but describing it as a failure of DPS's criterion would be false. The fixed-rank/symmetric-power distinction is already explicit in the primary contract.

**Du–Xie**, *Ample vector bundles without Griffiths-semipositive metrics*, arXiv:2609.26504v1: downloaded original PDF. Read extracted lines1–200 and275–365: introduction, Theorem1.1, curvature conventions, and §2.2 through Proposition2.3 and the start of its proof. Their actual obstruction uses a separable nonnegative test tensor, a horizontal-Levi differential operator linear in the candidate metric, and an integration-by-parts adjoint S_J≤−η Id. Proposition2.2 excludes every semipositive metric; Proposition2.3 gives an explicit coefficient continuity estimate under changes of holomorphic structure. These operations already yield robust, rather than merely isolated, metric exclusion. Their global moduli construction was read only in its introduction summary, not in its proof. No independent verification of their whole theorem is asserted.

**Liu–Wan**, *Stable ample vector bundles without semipositive Kobayashi curvature*, arXiv:2609.37309v1: downloaded original PDF. Read extracted lines1–190,360–435,585–630: all main introduction statements, Theorem3.2 with its setup, and its final adjoint estimate/proof. This primary explicitly constructs stable rank-two examples on every Hirzebruch surface and excludes strongly pseudoconvex Finsler metrics, a broader class than Hermitian metrics. The actual mechanism uses positive test forms for the separate line summands, angular averages of horizontal Levi forms, triangle-inequality control of norms, and adjoint coefficient convergence in a C⁴ neighborhood; its estimate requires no uniform candidate Hessian bounds. The intervening derivation of its angular estimates and its global moduli/exhaustion proofs were not read. One must not infer failure for all Finsler structures merely from the quadratic source obstruction; the triangle inequality and duality/regularization are additional operations explicitly paid by this primary.

The original source itself credits both recent primaries. The above comparison was performed on actual bodies, not title absence. Nothing here establishes a new-to-literature theorem.

### Source reading limits

All ten text files for the unique family050 manuscript were retrieved from the pin and their Git blob identities checked. §§1,3,4,5,6 were read completely (the initially truncated combined display was followed by complete separate reads of §§3–4). §2 construction was read through its local-basis proof in the combined display; its remaining tail was not claimed as read. The explicit bundle and both lower propositions are used as stipulated source facts. `paper.tex`/README were retrieved, not studied; references.bib was read only for the cited primary entries. No companion manuscript is listed for family050 in the complete catalogue/tree.

Supporting formalization could check the scalar exponent substitution, diagonal sequence argument, and curvature-sign bookkeeping under explicit analytic interfaces. It would not implement weak compactness, psh regularization, bundle geometry, or the no-invariant-measure source theorem. No implementation is presented or counted.

## 3. Output status and integrity

These are two substantive screens: the original King contract closes a precise general-parameter interface using a classical operation; the second route proves stronger metric-exclusion statements with source-paid operations. Neither is put forward for a campaign acceptance. No original target has been weakened and relabeled as solved.

The source receipts record raw pinned URL, exact local path, Git blob identity and SHA256. Primary receipts record origin and SHA256. The output inventory and external-anchor verifier cover this checkpoint, receipts, source copies and primary artifacts. Hash verification attests bytes and scope only; it is not mathematical proof. The final message supplies external anchors. The r14 frozen directory and all shared ledgers remain unchanged.
