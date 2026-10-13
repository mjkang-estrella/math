# I261 literature and source-contract ledger

Reviewed target is I262, not the unlaunched I259 scope. Verdict is TECHNICAL. Search absence does not establish novelty or significance. Exact mathematical reasons appear in the review and analysis.md.

## Pinned primary sources

All repository URLs below use immutable revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Catalogue family 262 was a locator, not the source contract.

- [Equality companion](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build): sections/introduction.tex `thm:main`; sections/action.tex `act:quantitative-action`, `act:constraint`, `act:trace-deficit`; sections/spectral-bound.tex `bound:sharp`; sections/compactness.tex `comp:relations`, `comp:vanishing-errors`, `comp:tail-bounds`; sections/rigidity.tex `rig:fixed-right-spaces`, `rig:fixed-left-spaces`, `rig:factorization`, `rig:partner`. These five sections were fully read. They establish classification, retained auxiliary defects and factorization; the read text has no D-versus-J corollary. Bibliography fully read.
- [Matrix inequality companion](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build): sections/introduction.tex `thm:main`; sections/spectral.tex `lem:form-compactness` and full main-theorem proof; sections/action-framework.tex `thm:action`; sections/action-limit.tex full action proof; sections/field.tex full field construction and comparison. Those five sections were fully read. sections/trace.tex was read from its beginning to before the first proof, including `thm:trace` and `lem:trace-half-lines`; sections/paths.tex was read from its beginning to before the first proof, including `prop:paths`. Their remaining proofs were not read or used. Bibliography fully read; notes/history.tex was not read. The main bound already applies directly to B_w w ff^T at the same gamma and supplies the alternative full-tail estimate in this review.
- [Scalar companion](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/build/sections/introduction.tex): fully read, including `thm:main`. This gives a scalar full-moment theorem, not an orientation estimate. Remaining scalar proof sections were not read or relied on.

Raw primary-file SHA256 and git-blob hashes are in input-authentication.json. Retained theorem excerpts come only from fully read passages and contain their exact pinned URLs. No source result is being audited for truth.

## External primary comparisons

- [HLW](https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf), Theorem 3.1: all of PDF pages 3–6 visually read, including its complete presented proof. It is a classical operator-valued endpoint input. Full PDF identity matches I259's authentication record. Original paraphrases and a short formula transcription are retained in classical-primary-excerpts.md; whole-page inspection images were removed after reading.
- [Carlen–Frank–Lieb v2](https://arxiv.org/html/1301.5032v2): Sections 1–2 and the relevant remainder statement in 3.1 were read, and Section 5 was fully read using intact MathML alttext extraction. Scalar stability is prior art; no matrix extension is assumed.
- [Leng v1](https://arxiv.org/html/2606.03749): introduction and the spectral theorem/proof through the end of Theorem 1.2 were read. Convex-geometric material afterwards was not used. Its scalar density formulation cannot see the orientations of a fixed w.
- [Frank–Gontier–Lewin](https://arxiv.org/pdf/2109.05984): PDF pages 5–10 fully extracted and read. Section 2's primary statements concern scalar finite-rank optimization; the remainder of the paper was not used. The journal-hosted PDF was located, but a direct retrieval returned 403; the separately hashed arXiv PDF was used for the read statements. Do not conflate the two byte identities.

No directly applicable published vector/matrix quantitative stability theorem was established in this bounded screen. This does not certify its absence. The verdict instead rests on the explicit same-exponent deduction from a stipulated primary theorem.

## Search extent

Queries on 2026-10-12: `Carlen Frank Lieb stability lowest eigenvalue 1301.5032`; `Lieb Thirring stability matrix vector potentials quantitative stability`; `2606.03749 Lieb Thirring stability Leng`; `"quantitative" "matrix" "Lieb-Thirring" stability`; `"stability" "vector-valued" "Gagliardo" inequality soliton`; `"Lieb-Thirring" "stability" "matrix-valued"`; `"Schrödinger" "stability estimates" "operator-valued"`; `"Gagliardo-Nirenberg" "stability" "Hilbert"`; `"Lieb-Thirring" "quantitative stability"`; `"matrix" "stability" "Keller" inequality`; `"Optimizers for the finite-rank Lieb-Thirring inequality" stability`.

Most vector search hits concerned evolution/orbital stability or stability of matter, not a static matrix deficit. Those snippets were treated as leads and are not mathematical premises. No score is taken from MathDB. Its Lieb–Thirring entries mentioned in I250 are relevance leads only and were not read as primary evidence here.

## Contribution distinction

The existing sources do not directly state the exact target. Its specified constants and orientation metric can be useful. However, after elementary global compression the stipulated matrix theorem already provides a dimension-independent support-free tail with a positive amplitude exponent. The endpoint interpolation gives a sharper rate, not an indispensable mechanism for the proposed comparability conclusion. This supports TECHNICAL rather than KNOWN or SUBSTANTIAL, with the exact proof gate explicitly separate.
