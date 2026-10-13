# I223 — primary-source comparison and exact reading limits

The independent verdict is **TECHNICAL/KNOWN ONLY**, explained in [the review](../../reviews/i223-coulomb-cost-complexity-contribution.md). This is a substantiality judgment conditional on correctness, not a finding that the exact full theorem has already appeared, and not a proof-gate decision. No I221 or other active review output was read.

## Accepted source

OpenAI, *A counterexample to the Monge ansatz for the three-marginal Coulomb cost*, September 25, 2026, pinned to `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

[Immutable PDF](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/paper.pdf). Read the existing `frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside/preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/paper.pdf.txt` completely: lines 1–749, all 14 pages, including references. Fresh pinned PDF retrieval through `pdftotext -layout` and SHA256 independently returned `0c82801c83218d368b0edf839a3f4c32f3c3998a53e4e0d1dba3c96465ca5efe`, matching the reused extraction. No new source-manuscript copy retained.

Most relevant dependencies: Lemma 2.1 (image-measure obstruction), Lemma 3.1 and its proof (convexity with the positive outer coordinate fixed), Proposition 4.1 (complete contact set/forbidden patterns), Lemma 4.2 (common smooth branch charts), Section 5 (smooth marginal/optimizer), Section 6 including Lemma 6.2 (separated approximation and conditional CDFs), and Theorem 7.1/proof (all d >= 2, s > 0). Their truth is stipulated, not audited.

## Carioni–Del Grande–Iglesias–Schönberger

*From plans to maps: Nonlocal regularization of optimal transport*, [arXiv:2609.05062v1](https://arxiv.org/abs/2609.05062v1), [versioned PDF](https://arxiv.org/pdf/2609.05062v1).

Fresh retained extraction: `carioni-et-al-2609.05062v1-pages1-25.txt`, **all lines 1–1633 read**, PDF pages 1–25. This covers the entire introduction and Sections 2, 3, and 4, including the full Example 4.6 and proof. Also read Section 5 through the statement of Proposition 5.3 on p. 25; its later proof is outside the extraction. Pages 26–36, including the remaining duality, numerical material and references, were not read. The older I217 Carioni excerpt was listed but not opened; its conclusions were not substituted for this longer source reading.

Exact comparison: Example 4.6 pp. 22–24 already proves the fractional penalty exponent and matching stripe upper bound/interpolation lower bound. Theorem 2.9 pp. 10–13 already uses finite-perimeter chart partitions, exact pushforwards, BV maps and fractional jump estimates. Propositions 2.1, 2.3, Corollary 2.5 provide general deterministic regularization/existence/compactness. Propositions 4.1 and 4.4 do not give the desired rate when no finite-energy optimal map exists; Remark 4.5 explicitly identifies this limit. Their q is I220's p; their fractional order alpha is I220's t. They use measure-weighted regularization with general Borel kernels; the unweighted identification under density comparison must not be applied silently at flat endpoints.

## Colombo–Di Marino

*Equality between Monge and Kantorovich multimarginal problems with Coulomb cost*, author version dated April 11, 2013, [primary PDF](https://cvgmt.sns.it/media/doc/paper/2127/MultiColDim.pdf), DOI [10.1007/s10231-013-0376-0](https://doi.org/10.1007/s10231-013-0376-0).

Read the older I217 excerpt completely (210 lines) first. Then retrieved and read `colombo-di-marino-full.txt` completely: **lines 1–719, all 14 pages and references**. Theorems 1.1 and 1.4 cover exact cyclic approximation. Lemma 2.2 supplies invertible equal-mass transports. Section 3.1 completes cycles by inverse maps and checks all pushforwards; Section 4 extends to Polish spaces and cyclic continuous costs. It gives no BV/fractional complexity rate. Consequently cyclicity is known, while I220's controlled special realization is an additional deduction.

## De Pascale–Louet–Santambrogio

*The Monge problem with vanishing gradient penalization: vortices and asymptotic profile*, [arXiv:1407.7022v3](https://arxiv.org/abs/1407.7022v3), [versioned PDF](https://arxiv.org/pdf/1407.7022v3), DOI [10.1016/j.matpur.2016.02.009](https://doi.org/10.1016/j.matpur.2016.02.009).

Read the older I217 excerpt completely (142 lines), then fresh `de-pascale-louet-santambrogio-pages1-14.txt`, **all lines 1–912**, and `de-pascale-louet-santambrogio-pages15-18.txt`, **all lines 1–279**. Thus PDF pages 1–18 were completely read, including the whole proof of Theorem 1.1 in Section 3.2, Theorem 1.2's complete statement and interpretation, Propositions 3.1/3.2, and Section 4.1 through Corollary 4.1/proof. Page 18 also starts Section 4.2's heuristics; that continuation and the later detailed vortex proof were not read or invoked.

Theorem 1.1 assumes polar Lipschitz domains and positive upper/lower density bounds. Section 3.2 uses regularization, exact-image transport, and a corrective composition; these hypotheses fail for the present global disconnected/flat support. Theorem 1.2 concerns an epsilon|log epsilon| vortex regime, not the stripe exponent, and provides finer asymptotic information than I220 claims. Its full later proof is unnecessary to the scope comparison and is not certified here.

## Transport/mixing interpolation

Cinti–Otto, *Interpolation inequalities in pattern formation*, [arXiv:1509.01189](https://arxiv.org/abs/1509.01189), [primary author PDF](https://cvgmt.sns.it/media/doc/paper/2778/interpola-paper-11.pdf). Reused I220 `cinti-otto-introduction-pages1-4.txt`, **all 189 lines**, plus fresh `cinti-otto-pages5-8.txt`, **all 214 lines**. Exact total scope: PDF pages 1–8, including Propositions 1.1–1.4 with their hypotheses and discussion, and the start of the physical applications. Later proofs were not read. Cited for scope/context of interface/negative-norm/Wasserstein estimates, not as an exact theorem containing I220's nonconstant dominated-measure setting.

Seis, *Maximal mixing by incompressible fluid flows*, [arXiv:1309.0556v1](https://arxiv.org/abs/1309.0556v1), [versioned PDF](https://arxiv.org/pdf/1309.0556v1). Reused I220 `seis-pages1-3.txt`, **all 137 lines**, whose header identifies v1 and document date September 17, 2018; fresh `seis-pages4-8.txt`, **all 250 lines**, and `seis-pages9-11.txt`, **all 196 lines**. Exact total scope: PDF pages 1–11. This includes all main theorem statements/proof of Theorem 1, both Lemmas 1 and 2 of Section 3.2 and their complete proofs, including the mollified-indicator transport pairing on pp. 9–10. Page 11 starts the appendix and Lemma 3's proof; its continuation and the remainder of the appendix/references were not read. I do not independently certify that auxiliary proof. The relevant complete comparison is the mollification/transport argument of Lemma 2, not an attribution of I220's exact statement to Seis.

## Inputs, boundaries and retrieval record

Read `AGENTS.md` and `sources/upstream.json` completely. Read both assigned I217/I220 briefs, the final I220 report, its complete analytic attempt and source note, and its authentication JSON completely. Reading metadata in that JSON does not count as reading any referenced historical source or report. No I33–I35, I189, I214, I221 or other review was opened.

For `sources/CONTENTS.md`, the auditable rereads are lines 1–220 and 8990–9016 (the latter includes the target family and adjacent entry). An initial full-output request was truncated and incidentally exposed further unrelated catalogue text; no full-catalogue reading is claimed or relied on. Source paths were resolved from the supplied I220 metadata and bounded directory listings. No repository-wide research scan was performed.

Only ordinary retrieval, text extraction, document writing and administrative SHA256 hashing were used. An initial Colombo PDF pipeline had an extra `pdftotext` argument and produced no retained file; the corrected retrieval succeeded. No downloaded PDF binaries were retained. New source files are page-limited/full text extractions, each entirely read and hashed in `input-authentication.json`; extraction completeness is distinct from a claim to have read the entire original article. No broad novelty search was used to infer worldwide priority.
