# I301 — sources, read scope, and attribution

2026-10-13. Proof review of U300, not an exhaustive literature or contribution assessment. Raw and semantic hashes, precise local ranges, and retrieval failures are recorded in [input-authentication.json](../../experiments/i301_gaussian_translation_proof/input-authentication.json). No external full source or full section is retained.

## Core stipulated source

[OpenAI, Sharp binary-information contraction on the discrete cube, pinned main TeX](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/main.tex). Actual lines 1–167 read, including `main:soft` and definitions. Whole-file raw SHA256 `ad04285e5eaa23a9b7a897f4501176e13f139bb04811c91576d5cc717cb5f8ca`, 14,721 bytes, fresh retrieval identical to the existing local corpus. The stipulated theorem covers arbitrary soft cube kernels at their actual information, all finite dimensions and all noise correlations. Gaussian limiting strictness is a downstream deduction, not contained in that stipulation.

[OpenAI, Hellinger companion, pinned main TeX](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026/build/main.tex). Actual lines 1–160 read for adjacent scope, including `thm:main`. Raw SHA256 `b286e05e0e9321c4a0cb925734a078b127e9d8694e8fccc5d4f6a484bfb0347b`, 10,094 bytes, fresh retrieval identical to local. Its theorem is Boolean and concerns the square-root profile; it is not substituted for soft Gaussian strictness. This limited companion read certifies no novelty claim.

## Classical scalar identity independently inspected

[NIST DLMF §4.36](https://dlmf.nist.gov/4.36), equations [4.36.1](https://dlmf.nist.gov/4.36#E1) and [4.36.3](https://dlmf.nist.gov/4.36#E3). Entire successful 89-line rendering read, including both displays and the pole qualification. The short operative transcription is:

    sinh(z)=z product_{n>=1}(1+z^2/(n^2 pi^2)).
    coth(z)=1/z+2z sum_{n>=1}1/(z^2+n^2 pi^2), z not in pi i Z.

This is the sole additional classical external identity in the core parent mechanism. Local uniform convergence on the positive real axis is checked directly by comparison with sum n^{-2}. Three independent urllib raw attempts returned 403; raw-response hashes are null. The short-transcription hash in authentication authenticates exactly that transcription, not an unreceived raw body. The power-series quotient and Jensen steps are proved directly in the review, not imported from named theorems.

## Existing rearrangement source rechecked for the consequence

[Mossel–Neeman, Robust Optimality of Gaussian Noise Stability, `1210.4126v3`](https://arxiv.org/html/1210.4126v3). Fresh in-memory HTML raw SHA256 `8b4e91d50c87e89d4531c9507bab8ec367c4a0705927d07d09e197dd16f08235`, 1,391,640 bytes. Actual semantic read: `S1.SS2` to before `S1.SS3`, and complete `S2` to before `S3`. This supports the positive-correlation two-set comparison used by I295. Its semigroup calculation is checked from the J Hessian. The original Borell article and this paper's equality/robustness sections were not newly read. This source is needed only for the dimension-free gap consequence, not for scalar U300.

## Internal deductions and scope

[I300 parent analysis](../../experiments/i300_gaussian_translation_strictness/analysis.md), [iteration](../../iterations/i300-gaussian-translation-strictness.md), and [authentication](../../experiments/i300_gaussian_translation_strictness/source-authentication.json) were fully read. Analysis SHA256 `a00cd592d623d7b9b1cc5be06a3fd3c96f09de8cc0fc933295e68238fa75af1e`.

[I290 analysis](../../experiments/i290_global_soft_summary_stability/analysis.md), SHA256 `2057261d4defe12b348fc97625130cf909e345c99d83a26ead7947171d794cf5`, was fully read. The conditional block-sum Gaussian interface was independently proved; the rest of its cube chain was read for scope, not passed wholesale.

[I295 analysis](../../experiments/i295_gaussian_rearrangement_stability/analysis.md), SHA256 `70992530f4413ff1a7ce8149dc5643cfd2215ca2bb85f2a5861ee70e405ef813`, was fully read. Its law-preserving rearrangement and scalar compactness implication were checked. Its EPI/analyticity sources were not newly fetched or imported. U300 fills the old scalar strictness obligation; it does not itself certify I131's local/compression deductions or the complete global S128 chain.

No named LSI source, unexamined search hit, analyticity theorem, numerical experiment, independent contribution claim, or acceptance recommendation is used.
