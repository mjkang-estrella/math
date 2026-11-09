# Fidelity and bounded prior-art investigation

No novelty clearance or comprehensive literature search is claimed. Searches were performed during this run; machine-readable query strings, head identities, exact values and access limits are in PRIOR-ART.json. Download receipts record actual UTC timestamps (which are November 2 UTC during November 1 local time).

## Literal statements and semantic split

The supplied arXiv v2 text was read at Definitions 4.1 and 4.5, Lemmas 4.2 and 4.6, (3.8), Theorem 3.11 and the paragraph preceding Conjecture 4.13. A live download of https://arxiv.org/html/2101.07103v2 was also saved with its receipt.

Equation (3.8) is L=diag(c)-K^alpha A K^-alpha with row conductances (d_i/d_j)^alpha. Theorem 3.11 supplies real spectrum, rank n-components and diagonalization by similarity to diag(c)-A. Similarity to a positive semidefinite symmetric matrix supports nonnegative eigenvalues; it does not imply nonnegativity of x^T L x for all real x. No use of that latter source inference is needed here.

Definition 4.1 is a potential drop divided by the imposed current. Its proof in Lemma 4.2 explicitly requires L V=I(e_v-e_w), (4.7). For nonzero alpha the left null vector is w_i=d_i^(-2 alpha). This follows term by term from w_i(d_i/d_j)^alpha=(d_i d_j)^(-alpha), symmetric in i,j. Hence compatibility requires w_v=w_w, equivalently d_v=d_w. Conversely our exact group inverse verifies a potential solution for every equal-degree pair in this graph. These are ten pairs among vertices 1..5 and six among vertices 6..9. Physical partial sums are 94/7 at alpha=1 and 410/31 at alpha=-1; they are not the all-pairs Kirchhoff indices. The literal source additionally imposes antisymmetric edge currents and Ohm's law with directional resistances, another compatibility issue that must not be silently repaired. The 16-pair sufficiency statement here concerns equation (4.7); it does not assert a general equivalence with every current axiom.

Lemma 4.2 (4.3) uses X_vv+X_ww-X_vw-X_wv for the named Moore–Penrose inverse. Definition 4.5 sums these over v<w. This is symmetric in the pair even if X is not symmetric. The assignment's -2 X_vw convention is separately reported, not identified with the literal source.

Lemma 4.2's proposed spectral similarity formula for the Moore–Penrose inverse fails for this nonsymmetric L. Exact controls show the group inverse fails a Penrose symmetry condition; the Moore–Penrose inverse fails commutation. Lemma 4.6's spectral formula instead agrees with the group-inverse trace and with the source's symmetric pair sum applied to that group inverse. It disagrees with the true Moore–Penrose value.

The independent construction uses P=1 w^T/(sum w), G=(L+P)^-1-P, U=11^(-1)11^T, W=ww^T/(w^T w), M=(I-U)G(I-W). Rational Gauss–Jordan inversion is implemented locally. All defining equations are checked exactly after construction. This establishes existence of certificate matrices by ordinary calculation. Formal uniqueness is not proved here; standard mathematical uniqueness is not a substitute for the required Lean theorem.

The computational paragraph reports all connected graphs with 5<=n<=8, more than 12,000 graphs. This 11-vertex candidate lies outside that experiment. No source code was supplied or recovered, so its implementation cannot be reconciled conclusively with either inverse convention. The predecessor's values and our independently reconstructed spectral values agree.

## Published source and later literature

The journal citation is Journal of Mathematical Analysis and Applications 507 (2022), article 125728, DOI 10.1016/j.jmaa.2021.125728. Estrada's live author publication page and Mugnolo's live CV were downloaded. They identify the work but do not clear later resolution. The journal body was not independently authenticated. ScienceDirect was already denied by the task and was not requested. A guessed author PDF URL returned 404 and was not retried. A search-indexed journal PDF excerpt corroborates the symmetric pair formula and conjecture numbering, but is not treated as independent complete journal-body verification.

A later closely related paper identified is Miranda–Estrada, Degree-biased advection–diffusion on undirected graphs/networks, DOI 10.1051/mmnp/2022034. Its primary MMNP PDF request returned 403 and was not retried. Search excerpts suggest a degree-biased adjoint and stationary vector proportional to degree powers, but no complete primary-body conclusion is claimed. A Mugnolo book, A Prolegomenon to Differential Equations and Variational Methods on Graphs, was identified as citing the target; its primary Cambridge fetch exceeded the web tool's size limit. A Chaos paper at DOI 10.1063/5.0142418 also appeared as a citing work. None of these citing bodies was fully screened, so they remain explicit gaps. OUCI advertised three citations but its fetch returned 502; this is neither an exhaustive citation count nor a clearance.

Multiple targeted web searches for refutation, correction, counterexample, the exact title, DOI and conjecture terms returned no verified prior refutation. One apparent June 2026 friendship-graph counterexample was inspected and rejected as unrelated: it concerns saturation number versus harmonic index. An open MathDB search label was not used as novelty evidence; the denied MathDB route was not requested.

## Registry screen

Only the two live GitHub /commits/HEAD endpoints were requested. Both returned 200; receipts and raw JSON are retained. openai/math HEAD is 4eaee87548250b2682affda7d05d947c05554bae; Omega HEAD is 2bd34aa7fd7676d9c4233eeec266df8aa1541d93, newer than the supplied 3e6639b6ed19cfda94e42db6814dd2623ec344a8. Neither HEAD response's changed filenames matches Kirchhoff, resistance, hubs-biased or 349441. This is not a full-tree conclusion.

Read-only cached D5 and Problems trees (13,408 and 1,642 entries, both untruncated) and an untruncated preprints tree (13,578 entries) were copied, hash-bound and path-screened. D5/Problems hits concern Fiedler resistance-invariant weights and quantum strong resistance; the preprints path screen has no hit. Their full paths, tree identities and hashes are in outputs/registry-cached-screen.json. The separate cached recursive openai root tree is explicitly truncated (55,173 entries) and was not mistaken for complete coverage.

The permitted live route does not provide complete D5/Problems/preprints contents. The current Omega head cannot be bound to those cached subtree identities solely from its commit response. The complete CURRENT registry requirement is therefore unmet; cached keyword path screens do not establish semantic nonduplication or exclude differently named proofs. No prohibited route was tried as a workaround.

## Gate decision

HOLD. The algebraic counterexample survives both correctly distinguished source algebraic readings. The demand for a refutation under every physical reading cannot be fulfilled from an undefined literal physical all-pairs index. We have not established that the authors intended a unique repaired physical object. No prior refutation has been verified, but later-literature and current-registry coverage are insufficient to pass the gate. Phase 2 and acceptance are not claimed.
