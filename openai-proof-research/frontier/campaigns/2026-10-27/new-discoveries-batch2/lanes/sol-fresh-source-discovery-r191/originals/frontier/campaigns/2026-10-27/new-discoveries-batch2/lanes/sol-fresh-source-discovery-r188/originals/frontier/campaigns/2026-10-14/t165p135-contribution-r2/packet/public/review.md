# T165P135 contribution reassessment, round 2

**Verdict: TECHNICAL, conditional on correctness, for the entire unchanged frozen scope.**

Runner: Codex / GPT-6.1-Sol, high reasoning, default service tier. This is an independent explicit-objection reassessment of the unchanged author proof, not a correctness review, author response, repair, acceptance, count change, or worldwide-priority determination. The OpenAI/math pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, including its operative proof operations, is stipulated true. No upstream audit is undertaken.

The decisive comparison is with the *operations inside* the pinned bipartite proof. Its individual shifted walks, integral chord calculation, additive ambiguity, diagonal annihilator, lower-order matrix, polynomial subspace proof, and two-triangle factorization compose compatibly in characteristic two. The author makes this transport explicit and self-contained. After the strongest combined reduction below, I find no remaining nonroutine operation. This assessment does not assert that an identical full theorem was previously printed.

## 1. Full scope and the preserved prior assessment

For every positive integer m,n, put d_r=floor(r/2)floor((r-1)/2). The fixed drawing convention has distinct vertices, simple continuous edge arcs whose interiors avoid vertices, finitely many proper transverse double crossings, and no tangencies, triple crossings or common subarcs. For every even-adjacent drawing D of K_{m,n}, meaning every adjacent edge pair crosses evenly, the frozen claim is oc(D) >= d_m d_n, counting unordered oddly crossing edge pairs. Balanced-axis exactness requires no adjacent crossings and at most one crossing per pair. The frozen corollaries are ocr±=ocr+=pcr+=d_m d_n, and equality with ordinary cr(K_{m,n}) using pinned thm:main. There is no unrestricted ocr/iocr/pcr evaluation and no tripartite Harborth claim. The corollaries belong to this one package, not additional findings. The scope and proof hashes are respectively

- 1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d
- a12854336cc118cc9a49dd96bb72aeb142e618ab3466a2e1dc648ff77bf98f10

Round 1 returned SUBSTANTIAL at this full scope, conditional on correctness. Its affirmative case rests jointly on author Lemma 3 (one-sided shift and diagonal bookkeeping), Lemma 8 (order-matrix detector), and Section 8 (even adjacency and invertibility). It already credited the chord bit, additive-block relation, subspace transfer, deletion, and axis construction as classical or routine. It also recorded contrary weighting: every individual ingredient is small, no new tool is developed, and the inherited machinery does the lifting. Its positioning conditions PQ1–PQ5 require precise restricted-class labels, bounded novelty wording, full attribution, identification of the transport, and retention of correctness attention items. Those findings and limits are preserved in the actual immutable files and byte-identical private copies here; the old verdict is not rewritten.

The parent authenticated that review but did not adopt contribution closure. Its O1–O7 objections challenge mathematical premises and source/history readings, not the frozen theorem. No author response or revised proof exists. I did not use other nominees' contribution verdicts to select this grade. Incidental campaign-index and mandated round-1 references to other grades are not evidence for this verdict.

## 2. Strongest combined reduction: the geometric operation

Source references here are to the authenticated bipartite preprint's build/sections files at the pin; private/source-authentication.json maps all 11 bodies to tree objects, sizes, SHA-1 and SHA-256. All six companion bodies were also authenticated. Parent intake is artifact/limited-source evidence, not a mathematical gate.

In intersections.tex, eq:chord-formula (lines 62–86) says, for two directed chords with distinct boundary endpoints,

    I(C,E) = (1/2) sum_{u,w} eps_C(u) eps_E(w) T(u,w).

Let t(u,w) be the 0/1 comparison with the same cut. Over the integers T=2t-1, and each chord's two endpoint coefficients sum to zero. Therefore the same source calculation is exactly

    I(C,E) = sum_{u,w} eps_C(u) eps_E(w) t(u,w).                 (R1)

The constant term vanishes as the product of the two endpoint-coefficient sums. This is an integral rewriting before any field reduction; it does not reduce 1/2 modulo two. Reducing (R1) gives the author's mod-2 alternation sum because both signs become 1. Chord alternation parity is classical. The source's own local proof and the parity realizability bodies discussed below supply the operation.

Now retain eta_+ from the source construction, instead of averaging eta_+ and eta_-. The source already constructs *each* closed walk, separates shared tracks at crossings and bends, treats opposite traversals, and proves that each total signed intersection with gamma is zero (intersections.tex lines 92–177, especially eq:exterior-intersections at 125–136 and the cone/entrance-exit argument at 152–172). Taking absolute intersection count modulo two also gives zero, as the author does.

For distinct spokes the shifted comparison t equals their original cut comparison. For a shared spoke s it is a fixed bit delta_{v,s}, determined by the fixed edge orientation and chosen side, independent of the cycles. Thus (R1) and the existing one-sided walk give an integer corrected matrix K with off-diagonal entries

    K(e,f)=I(e,f)+sum_{v common} sigma_ve sigma_vf t_v(e,f),

and diagonal entries sum_v delta_{v,e}; the sigma squared on a shared spoke is 1. The existing zero-total identity is z^T K y=0 for signed simple cycles. Its mod-2 reduction is precisely the author's J_2 and Lemma 3: I becomes crossing parity, signs disappear, and the shared-spoke bits occupy only the edge-index diagonal. One can instead perform the same counting directly modulo two, as in author Lemma 3 Steps 2–5; no new topological device is required.

This reduction uses the source's *unaveraged* walk, not just the source's displayed averaged J. The exact choice of delta need not be solved to use it: the source already fixes the endpoint displacements and comparison signs. All diagonal values are later annihilated. The finite diagnostic checks both displacement directions with shared and unshared spokes, but the general explanation is (R1) and the source construction, not those finite cases.

The source begins with a polygonal drawing with no adjacent crossings because it studies ordinary cr. Allowing adjacent crossings outside the vertex disks changes only which distinct-edge crossings contribute to the exterior sum; its shifted-track and closed-walk counting operation is the same. This observation is conditional on the frozen proof's normalization being valid. I do not replace its continuous-arc Lemma 1 or certify that lemma. The original proof and all scope conventions remain fixed.

The subsequent block operation is already intersections.tex lem:additive, eq:additive-relation (lines 181–215). In characteristic two its four-cycle rectangular differences have plus signs. They yield J_2^{ik}+J_2^{i1}+J_2^{1k}+J_2^{11} in the row-plus-column space. Shared-edge diagonal terms are included in that identity; they need not be removed prematurely. This is the same four-cycle expansion, not an independent compatibility obstruction.

## 3. Strongest combined reduction: detector, field and assembly

In detector.tex eq:detector-definition (lines 111–123), write Pi for the source's F. For distinct nodes over any field,

    Pi'(x_p)=product_{k != p}(x_p-x_k) != 0,
    B_pq = (x_p-x_q)/(Pi'(x_p)Pi'(x_q)) h_pq h_pq^T.

This division is valid in characteristic two. The derivative polynomial need not have its leading characteristic-zero degree: its value at a simple root is the displayed nonzero product. Also x_p-x_q=x_p+x_q !=0 for p!=q, while B_pp=0. There is no numerical-order/sign function in this formula; the spoke order is a separate input matrix.

The source's eq:lagrange-vanishing and the following row/column sums (lines 134–164) use polynomial interpolation and degree at most n-2. They hold over the chosen characteristic-two field, and annihilate every additive matrix and diagonal matrix. The two-triangle proof (lem:triangular-basis, lines 13–83) uses distinct nodes, root bounds, monic factorization and relabeling; it has no order-of-field or characteristic-zero step.

The source then already introduces H(p,q)=1_{q<p} (lines 168–180), replaces the half-sign input by H modulo additive and diagonal matrices, subtracts a constant on each row p>s+1, obtains precisely Q_s, and factors the image as A_Q D_Q A_Q^T up to an overall sign (eq:detector-factorization, lines 182–190). There is no need to reduce the half-sign input itself.

For the author's strict upper-order matrix T(p,q)=1_{p<q}, in characteristic two

    T + H = 11^T + I,
    Phi(T)=Phi(H).                                             (R2)

The right side of the first identity is additive plus diagonal and is annihilated. Reducing the source's lower-order row subtraction produces value 1 on both triangles, because -1=1. Equivalently the author's upper-order row flip subtracts/adds 1 on p<=s+1; it has the same image. Hence the author's factorization is the source factorization over this field:

    Phi(T)=A_Q diag((x_p+x_q)/(Pi'(x_p)Pi'(x_q))) A_Q^T.

Every diagonal factor is nonzero and A_Q is invertible. Relabeling proves this for every spoke order with the same Phi, exactly as in the source. The new diagonal terms left by the one-sided construction fall in the *already present* kernel B_pp=0. There is no competing constraint between the geometric choice of side, the node tuple, and the order-detector relabeling.

Subspaces.tex lem:subspace and cor:rank-sum contain the full filtration, minor-degree and determinant-multiplicity proof. In particular eq:node-rank passes from non-nodes to a node by vanishing of polynomial minors on an infinite set; that is the relevant field-size requirement. F=GF(2)(t) supplies it and arbitrarily many distinct nodes. Evaluation kernels, Lagrange inversion, constant column changes and determinant divisibility use field operations valid here. No new bound or multiplicity estimate is introduced. Author Lemma 5 and Corollary 6 reproduce this paid argument over F.

In the source conclusion.tex eq:rank-family through eq:crossing-rank, diagonal blocks are half spoke-order matrices because adjacent crossings were removed. In the transported proof, even adjacency supplies

    J_2^{ii}=T_i+Delta_i,
    Phi(J_2^{ii})=Phi(T_i) invertible.

This is a sufficient hypothesis allowing the same diagonal-rank test. For i!=k, p!=q, the entry J_2^{ik}(p,q) is chi(ip,kq); the p=q entries, including common-second-endpoint terms, are again annihilated. Therefore the unchanged rank-sum mechanism gives

    2 d_m d_n <= sum_{i!=k} rank R_ik
                <= sum_{i!=k} oc_ik = 2 oc(D).

The final division by 2 is in the integers counting ordered versus unordered pairs, not a division in F. The source's vertex-deletion operation then gives every even n>=4 using n d_{n-1}=(n-2)d_n; even adjacency is hereditary and each odd independent pair survives n-2 deletions. The cases with d_m d_n=0 are vacuous. The classical balanced-axis drawing in source sec:formula has no adjacent crossings and each pair crosses at most once, so it gives all the frozen upper bounds and corollaries. This covers all positive m,n, without a monotone, rotation, piecewise-linear-only or semisimple substitute for the fixed scope.

The remaining work after this reduction is to write out the parity version, retain the harmless diagonal, choose an infinite characteristic-two field, and replace the source crossing-point support count by odd-pair support. These are compatible routine technical steps on the paid mechanism. I do not find a residual nonroutine construction or estimate in the unchanged author proof.

## 4. Actual primary operations and what they do not establish

The primary PDFs were reused read-only, independently hashed and independently re-extracted; all six text extractions match the retained round-1 texts. This is independent body engagement/authentication, not a claim of six new HTTP acquisitions. Exact extents and URLs are in reading-limits.md and private/primary-authentication.json.

**Pach–Toth 2000, Section 4, Lemma 4.1 and full proof** (retained text 590–735; author PDF https://math.nyu.edu/~pach/publications/whichcrossing.pdf). All realizable GF(2) odd-pair vectors are the reference convex vector plus vertex-pull vectors and rotation-inversion contributions. Pulling an edge around a vertex toggles its pairings with the incident edges; local rotation changes toggle adjacent inversion pairs. The proof realizes these changes and deforms a drawing back to the reference drawing. These are genuine classical parity and local-order operations. Its symbol Phi is a realizability subspace, distinct from the author's rank-detector map Phi; identifying the symbols would prove nothing. This lemma alone supplies no sharp d_m d_n rank bound, but it removes any basis for treating mod-2 local crossing/rotation accounting as a new theory. Theorem 1 removes crossings of wholly even edges, not arbitrary even crossings of adjacent pairs. Theorems 2–3 are comparison/crossing-lemma bounds, not the full frozen sharp evaluation.

**Szekely 2008, Theorem 1 and complete six-page proof** (https://amc-journal.eu/index.php/amc/article/view/43/30). For a reference drawing D, attach any set A_e of vertices excluding e's endpoints, and define par(e,f)=|e intersect A_f|+|f intersect A_e| mod2 for independent pairs. The criterion is, for every assignment,

    #{odd pairs of D with par=1} <= #{even pairs of D with par=1}. (R3)

Equations (6)–(13) express the effect through four Q-values and show how assignments encode the changes; (14)–(22) give the comparison of odd counts. Theorem 1 makes (R3) equivalent to independent-odd optimality. If D is nice, that implies ordinary optimality and equality of ordinary and independent-odd minima. The converse from ordinary optimality is not stated or justified. Knowing pinned cr(K_{m,n}) and that the axis drawing is nice therefore does not verify (R3). The paper suggests the axis drawing as a candidate, without the required verification. Its unrestricted iocr conclusion would in fact go beyond the frozen restricted-class claim. I do not use it as an automatic deduction. The 2003/2004 antecedent parity formula is read through its explicit restatement here; its original body was not separately acquired.

**FPSS 2012, Remark 4, Section 3 and Remark 12** (https://doi.org/10.7155/jgaa.00266). Remark 4 defines Rule ± by adjacent edges contributing zero in the relevant crossing sense; for ocr this is exactly even adjacency. Lemma 1 separates a self-crossing, then reconnects by a narrow tunnel with balancing crossings. Lemma 3 pairs even intersections along an even edge, reconnects on either side, and manages closed components without new odd pairs while preserving rotations. This is classical one-sided/parallel-track and closed-curve parity bookkeeping. It does not assert that every even-adjacent drawing can be made adjacent-free with every independent parity preserved. Remark 12 says the framework's translation fails for ocr+ and acr+, whereas it *can* work for ocr±; the particular monotone separation there does not separate ocr from ocr±. Round 1's claimed open ocr± translation question misstates this paragraph. This additional correction strengthens the need for precise operation-level comparison, though it is not itself a proof of the frozen theorem.

**BFK, arXiv:1312.3679 retained author version**, Theorem 1.1, Proposition 2.7 and its proof, Section 4 including Propositions 4.1–4.2 and Lemma 4.10/Corollary 4.11 (https://arxiv.org/abs/1312.3679). They prove mon-ocr±(K_n)=mon-ocr+(K_n)=mon-cr(K_n)=Z(n). Proposition 2.7 minimizes crossings among drawings preserving rotations, above/below relations and every pair parity; monotonicity and completeness force the relevant bigon to contain no vertex, allowing its elimination. The Section 4 extensions include x-bounded and shellable/s-shellable classes, using winding parity, local K_4 order types and weak Hanani–Tutte with preserved rotations. It is inaccurate to summarize the entire paper as only monotone. These operations are still not a theorem about arbitrary even-adjacent K_{m,n}. I do not drop their geometric hypotheses or complete-graph assumption.

**DS21 2017, odd entry and Levow reference** (retained version; https://www.combinatorics.org/files/Surveys/ds21/ds21v3-2017.pdf). The ambiguity is which parameter Levow defined—algebraic, odd, or an independent version. It is not a statement that binary-field crossing theory cannot decide numerical values. The survey credits binary-field development. Tutte and Levow bodies remain unobtained; therefore no incapacity or missing-operation claim is made about them. A new bounded search found bibliography/survey references for Levow but no body. Following an apparent Tutte access lead ended at ScienceDirect S0021980070800072 with HTTP 403. These are explicit coverage failures.

**Balogh et al., arXiv:2610.25204v1**, retained PDF dated 18 October 2026 (body title date October 20). I read the introduction, good-drawing/flag-algebra setup, the drawing-generation operations in Section 3, and the Lemma 9/Theorem 4 proof. Their setup assumes good drawings: adjacent edges do not cross and pairs cross at most once. Lemma 9 uses crossing K_{2,2} densities and a flag-algebra computation to obtain an asymptotic 0.96936 bound. It neither provides an all-size sharp parity result nor justifies normalizing arbitrary even-adjacent drawings into its good class. Its explicit pre-publication positioning is retained; its language about the pinned publication does not challenge the stipulated pin here. This was a relevant-body check, not a complete line-by-line reading or validation of its SDP computation.

Absence of a displayed full value is only bounded negative evidence. Even the stronger round-1 wording about absence in *any* class is untenable as a general novelty inference: zero-factor cases are elementary, K_{3,3} has the parity obstruction, and the small-value collapses recorded in FPSS already give small cases. None of this identifies a prior full all-m,n theorem. The verdict is TECHNICAL because of Sections 2–3, not REDISCOVERED because a prior identical theorem was found, and not SUBSTANTIAL because no identical displayed theorem was found.

## 5. Explicit resolution of O1–O7

**O1 — corrected; prior premise rejected.** Nonzero derivative-product division and x_p-x_q survive in characteristic two. Source eq:detector-definition and the product formula above are precise evidence. Only literal half-sign/averaging expressions lack a direct mod-2 image; that fact does not defeat the underlying operations.

**O2 — resolved in the technical-transfer direction.** Retain the already constructed eta_+, use the integral chord identity (R1), and carry fixed shared-spoke bits into the diagonal. Source lem:detector already annihilates that diagonal. Equation (R2) identifies the author's upper order input with the source's lower order input under Phi, and the source already supplies Q_s and A_Q D_Q A_Q^T. Infinite-field subspace transfer and the rank assembly remain compatible. No new nonroutine residual is identified after this combined construction. This is a method assessment of the unchanged proof, not a new proof repair offered to the author.

**O3 — corrected; incapacity inference withdrawn.** DS21 text 3219–3228 concerns ambiguity of Levow's definition. It supplies no theorem about numerical inability. Tutte/Levow unread bodies cannot serve as negative evidence. The actual classical operations used here were read in Pach–Toth, Szekely, FPSS and BFK.

**O4 — corrected and separated.** The exact full prior statement was not located within disclosed coverage; that does not establish substantiality. Source-plus-classical routine transport suffices for TECHNICAL under the campaign criterion. Szekely (R3) remains unverified here, and pinned ordinary optimality does not imply it. No historical impossibility or worldwide-priority claim is adopted.

**O5 — corrected; no grade calibration.** The actual R027 finding records later campaign acceptance for ordinary cr(K_n-e); the pending label in fresh-substantial-discovery-r2/candidate.md is historical. I read the archived candidate's missing-pair tests, split spaces, mixed orthogonality, twisted rectangular detector and localization/descent, and the manuscript's Sadhu comparison: that lineage concerns deleted edges and real signed counts, not this parity transfer. T184I134's frozen statement and author proof concern independent-set counts for clique-free graphs, with the mean-field optimizer F*_G, test weights and Jensen. They are not an ordinary crossing theorem. The O1–O4 operation comparison determines this verdict, irrespective of other candidates' grades. I have not reread their contribution verdicts for calibration or reopened Kang's body as a new dependency of this review.

**O6 — corrected; sufficient, no iff.** Even adjacency gives J_2^{ii}=T_i+Delta_i, sufficient for invertibility. No theorem here proves singularity for every nonzero adjacent parity perturbation. Indeed the detector's kernel includes 11^T+I, so nonzero off-diagonal algebraic perturbations can preserve its image; this is an algebraic observation, not a claim that an arbitrary block perturbation is realized by a drawing. No necessity/equivalence characterization is an extra conceptual contribution of the frozen proof.

**O7 — preserved with explicit separation of gates.** Full fixed scope, continuous-arc conventions, original rights and prefreeze disclosure remain. Author Lemma 1's round-disk/no-reentry normalization and Lemma 2's t(u1,.) explanatory typo remain correctness-attention items. The latter gives 1 rather than 0 under the stated cut, but the two terms cancel mod2; I do not edit the text. No correctness review is supplied, and no narrowing is authorized. Unread Tutte/Levow bodies, incomplete survey coverage, and the Ho/Yang acquisition/read limitations remain. Integrity authentication is not mathematical correctness or priority. This resolves O7's contribution-review handling, not the outstanding correctness questions themselves.

## 6. Positioning, history and contrary weighting

The author's transfer is a useful explicit parity formulation with full-scope quantitative consequences if correct. A short bridge can be substantial, and small ingredients alone do not force TECHNICAL. The strongest case for SUBSTANTIAL is that two literal source displays do not reduce modulo two, and that retaining a one-sided object must fit a later annihilator while the theorem targets a named drawing class. I considered that case. Here the fit is already supplied: the source constructs the one-sided object *before* averaging, its chord formula has the integral rewrite (R1), and its detector explicitly kills exactly the surviving ambiguity. Likewise the source already carries out the order-to-two-triangles reduction. The claimed three nonroutine replacements therefore collapse to routine use of operations already in the source. An absence of the parity theorem from either preprint's stated scope does not change that method comparison.

The complete-graphs companion's main.tex was read through its cycle proof, even-node rectangular detector, polynomial tests, collision-factor descent, isotropic image argument, deletion and upper construction. It also counts ordinary points. It does not display this bipartite parity result, but confirms a related operative interpolation/cycle framework rather than providing evidence of an unpaid parity obstruction. Its explicit lower-order/additive replacement at eq:M reinforces that order detection is based on polynomial evaluations, not an ordered-field sign test.

History searches used hidden/ignored files, JSON and large authored files with no size cutoff; commands and exclusions are retained privately. The initial file-hit pass also matched vendored software; the refined pass removes .venv/.lake/vendor and broad parent/review/recovery categories. Copied corpus/navigation hits are not treated as operative clearance. Crossing-specific operative hits led to the R027 archived candidate and manuscript passages actually discussed above. A r120 screen concerns endpoint-transport edges crossing at most once in a k-level complexity argument, not a graph-drawing parity rank transport. Other barycentric matches are geometrically unrelated. No identical prior project parity construction was located in this bounded scope. Entire arithmetic-discovery and analytic-discovery families, T088 roots including t088p133-proof-r2, recovery/review roots, the current nominee and current parent roots were excluded from history scanning. The mandated current inputs were read separately. This conservative exclusion is a limit, not project-wide exhaustion.

PQ1–PQ5 remain substantively important, with PQ4 corrected to avoid asserting nonroutine novelty: label the restricted class exactly; say only no full antecedent found in disclosed coverage; credit the pinned bipartite mechanism and ordinary value, the companion, classical barycentric interpolation, FPSS Rule ±, BFK's restricted geometric results, Pach–Toth's Tutte-style realizability operations, and Szekely's actual parity algebra/criterion; describe the proof as an explicit characteristic-two technical transport; retain the two correctness-attention items. Tutte/Levow attribution must disclose indirect access. Do not claim the even-adjacent hypothesis is necessary, that old methods could not have proved the statement, or that a worldwide search established priority.

The author records a scope freeze at 2026-10-20T18:22:29Z after substantial characteristic-two feasibility/strategy work and before proof drafting. I preserve that disclosure without independent timing certification. No author change, revised theorem or mathematical repair is part of this reassessment. Campaign 18/20 and all separate acceptance requirements remain untouched; no downstream stage is opened by this report.
