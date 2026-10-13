# I230 — reading, route failures, and limits

## Execution scope

Worked only in /home/mj-kang/Documents/Dev/math/openai-proof-research and wrote only the four authorized principal files and actually read page excerpts under frontier/sources/i230_p_harmonic_gradient/. An early analytic note recorded the exact epsilon/lambda obstruction before the restricted convexity route was found. It was developed in place, not preserved as a snapshot. Temporary PDFs were retrieved solely to extract the indicated pages and were removed; no unread PDF is retained.

No subordinate agent was used. No I231 file, live output of another agent, shared ledger, or live review was read. The completed I224 literature map and existing primary excerpts under I224 and I229 were reused to locate/read primary literature; those are not a new review round. The complete prior briefs and reviews supplied in the prompt were accepted as context. No research program, numerical experiment, parameter scan, test, staging, commit, seal or publication was performed. Python was used only for bounded catalogue lookup, provenance hashes, and the JSON manifest.

## Actual source reading

1. AGENTS.md and sources/upstream.json: complete. Revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb accepted, not audited.
2. sources/CONTENTS.md: family-377 passage and bounded case-insensitive lookup for p-harmonic, p-Laplace and infinity-Laplace terms. Only family 377 matched. sources/preprints-tree.json: complete-path-list query for that family and related names; not a semantic read of every manuscript.
3. Reused pinned corpus: all of 01-introduction.tex, 02-flatness.tex and 03-reduction.tex were read through bounded displays, with overlapping rereads of the selection/cylinder contracts to resolve initial output truncation. The actual inputs checked were thm:main; lem:linear-lift; prop:three-point; lem:family-flatness; lem:bad-scales; lem:cylinder-comparison; prop:nonaffine-limit; thm:liouville; and derivative extraction. They are stipulated true; no source proof audit. Sections 04–08 were not read or needed. No same-family p-viscosity companion was identified in the bounded catalogue/path check.
4. Bungert, arXiv:2302.08462v2: reused text, lines 1–310, particularly Definition 2.1, Theorem 1, Remarks 2.3–2.5 and the radial example. Read the exact H and global-gradient hypotheses; the rate is for values. No later proof section was relied upon.
5. Sobral–Teixeira–Urbano, arXiv:2610.13137v1: reused PDF-text excerpts pages 1–4 and 9–13, read completely. Theorem 1.1 constants depend on p; the shifted large-gradient matrix retains ellipticity ratio p-1. The planar infinity theorem is homogeneous. Pages 5–8 and 14 onward were not read.
6. Lindgren–Lindqvist, arXiv:2006.15328v1: new retained excerpts PDF pages 1–3, 7–12, 24–28, all read completely. Theorem 7 proves local uniform convergence of the gradient magnitude, and page 12 explicitly distinguishes full-gradient convergence as more demanding. Appendix pages 24–26 explains the adapted planar Sobolev/flatness estimates. The geometric-streamline development on omitted pages was not read or used.
7. Peng–Zhang–Zhou, arXiv:2310.08093v4: new retained excerpts PDF pages 1–8 and 14–23, all read completely. Read Theorem 1.1, Lemmas 3.1–3.5, 4.1–4.4 and 5.1–5.2, and the opening geometric inequalities in Section 6. Its actual theorem gives local uniform convergence of the full gradient in arbitrary convex rings. Smoothness/nonvanishing/quasiconcavity are stated in Lemma 3.1 citing Lewis; Lewis's 1977 original was not retrieved or independently read. We only use non-strict Delta u_p<=0, and derive it directly from quasiconcavity plus the p-equation. The excerpt's strict statement at p=2 is unnecessary here. Omitted pages 9–13 and 24–45 were not read. The 2025 published abstract was checked for bibliographic identification; the proof reading uses v4, not a claim to have read the published PDF.
8. Li–Zhang, arXiv:1901.06128v1: the entire three-page manuscript was extracted and read, including Theorem 1.1 with coefficients uniformly elliptic on Q6 and its scale-independent Harnack constant. Used only for the conditional finite-viscosity rigidity result with a globally bounded full gradient. Moser's 1961 original was located bibliographically but not retrieved/read.

## Failed or non-closing routes

* Copying I224's strengthened scale maximum does not remove epsilon/lambda, because r cancels from the exact p-equation. This is an algebraic obstruction, not a presumed defect in I224.
* An affine lift creates epsilon Delta u, and cannot give a homogeneous p-equation.
* In the infinite transverse-viscosity ratio, Delta_x V=0 plus source fits allows V=sin t. No homogeneous Liouville invocation is valid there.
* The wider sqrt(epsilon) scale produces the full harmonic limit only conditional on compactness; the old thin fit gives no such compactness.
* At finite nonzero ratio, the strictly convex exponential energy identifies a different equation. Bounded-global-gradient rigidity is proved, but that extra hypothesis is not inherited. No full fitted-class Liouville proof was found.
* The fixed eta² test removes the explicit p factor but leaves uncontrolled p-flux concentration. Linearized flux-angle coercivity cannot be bounded below uniformly in p.
* Planar Sobolev/magnitude convergence does not alone imply vector gradient convergence or a rate; the source itself warns of this distinction.
* The noncritical quasiconcave route does close, but is closely related to Peng–Zhang–Zhou's existing normal/slope proof. Combining it with the stipulated Hölder estimate and Bungert is a technical quantitative transfer, not an independent tenth contribution.

## Search and claim limitations

Broad primary-literature searches were used only as leads, followed by actual source reads. Search snippets from secondary hosts were not theorem inputs. Some combined tool displays exceeded the output budget; relevant manuscript ranges were then reread separately. No failed PDF download is represented as read. No exhaustive global priority search, no endpoint exponent claim, no boundary gradient rate, no critical-point theorem, and no general p-independent C¹ estimate. The final positive theorem explicitly retains the noncritical and convex-superlevel hypotheses on u_p. The parent owns contribution and proof gates.
