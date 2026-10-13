# I225 primary-source reading index

This is a scoped contribution check, not an exhaustive literature search or a worldwide novelty claim. Existing local pinned source copies were reused. Every newly retained copy below is a PDF text excerpt whose complete stated page range was read. Full downloaded PDFs were processed in memory and not retained.

## Pinned OpenAI premises

All at repository `https://github.com/openai/math`, revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; file-level raw URLs and Git blob identities are in `../../experiments/i225_new_curvature_bridge/input-authentication.json`. These are accepted premises, not audited.

- `Giglis-distributional-curvature-characterization-of-Alexandrov-spaces-September-24-2026/build/sections/introduction.tex`: complete introduction; `main:equivalence`, exact Hausdorff measure, unreduced RCD and original test fields/functions.
- `Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/build/sections/introduction.tex`: complete introduction; `weight:every-geodesic`, including bounded Lipschitz `F`, bounded continuous `G`, global full-support finite-dimensional RCD hypotheses and all minimizing-geodesic quantifier.
- `Bi-Lipschitz-Coordinates-at-Regular-Points-of-Noncollapsed-RCD-Spaces-September-25-2026/build/source/introduction.tex`: complete introduction; theorem and already claimed defect construction. Selected actual lower interfaces in `coordinates.tex`, `pinching.tex`, `renormalization.tex` were also read; exact line ranges are authenticated. Dimension-only distortion is distinct from the unquantified chart radius.
- `Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/build/sections/introduction.tex`: complete introduction; `thm:foundation`. `sections/geometry.tex`, proposition `geo:intermediate` and its full proof, was read for the specific time/radius dependencies.
- `Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/build/sections/introduction.tex` and `geometry.tex`: complete. `scales.tex` was read through line 135 (scalar definition, power reduction, logarithmic selection); `conclusion.tex` complete. The proof's exponent/threshold is nonexplicit and fixed-geometry only. Lower proof operations are accepted; their long proofs were not audited or claimed to have been read in full.

## Primary prior art actually read

1. **Gallouet–Merigot–Thibert, Strong c-concavity and stability in optimal transport**, [arXiv:2207.11042v1](https://arxiv.org/abs/2207.11042v1). Retained `gmt-v1-pages1-11.txt` and `gmt-v1-pages17-19.txt`, exactly PDF pages 1–11 and 17–19. Theorem 5 and Propositions 8/10 provide the abstract modulus/duality and marginal gluing mechanism. Theorem 28 is read with its `C^1` map, `C^2` potential and smooth twisted cost assumptions. These do not pay the rough-density conjugate-pair estimate IC. No reliance on unviewed versions: the arXiv record inspected lists v1 only. The proof fragment on page 17 is not described as the whole proof of Theorem 22.

2. **Kitagawa–Letrouit–Merigot, Stability of optimal transport maps on Riemannian manifolds**, [arXiv:2504.05412v2](https://arxiv.org/abs/2504.05412v2). Retained `klm-v2-pages1-5.txt` and `klm-v2-pages18-20.txt`, exactly PDF pages 1–5 and 18–20. Theorem 1.2 and Corollary 1.3 cover fixed sources bounded above/below on closed manifolds, arbitrary targets. Equation (1.5) is an exponent `1/6` on the **squared** map distance. Section 4 exhibits the gradient-interpolation loss. The last excerpt stops during Proposition 4.3; no complete reproof of KLM is claimed.

3. **Gigli–Violo, Notes on the Cheeger and Colding version of the Reifenberg theorem for metric spaces**, [arXiv:2406.13771v1](https://arxiv.org/abs/2406.13771v1). Retained `gv-v1-pages1-7.txt`, exactly PDF pages 1–7. Theorem 2.2 gives the global version; **Theorem 2.6** is the local dyadic-summability theorem in this v1. The published version is [Bollettino UMI 18 (2025), 217–271](https://doi.org/10.1007/s40574-025-00458-7), with different local theorem numbering. Neither an explicit distortion formula nor a new chart theorem is imported from search summaries.

The report's own theorems are proved directly in `analytic-attempt.md`; the prior-art statements are used to limit the contribution claim. Source-specific dependencies are not silently strengthened.

## Search leads not imported as theorems

Searches also returned Warren's smooth-density near-identity theorem, older Ambrosio–Gigli stability, and an October 2026 regularization preprint for Euclidean quadratic transport. They were not retained or relied upon as mathematical inputs. No negative novelty conclusion is based on their absence or on a search-result summary. The failed GMT HTML v2/v3 fetches were superseded by the verified v1 PDF reading.

## Remote PDF provenance

- GMT v1 PDF SHA-256: `90caefecca3be940b2b18249b19b3c7b0e51d302b2d251080fbd4a1cd2e5aaa9`.
- KLM v2 PDF SHA-256: `2e24ceb87da6614b32f6ada1704f550968e94322ac9405e96cefb1c5e5b6456c`.
- GV v1 PDF SHA-256: `f8129762b114449fc088c533e1791a31e15d357e036d58d50ff5a5def4721b54`.

These identify retrieval inputs, not stored PDFs. Hashes of the retained text excerpts are in the input-authentication file.
