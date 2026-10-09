# Parent preliminary review — Gaussian polynomial candidate

Date: 2026-10-08. Candidate only; independent proof and novelty review pending.

The parent read the complete discovery report. Its strongest statement is almost-everywhere convergence, along all positive integers, of polynomial multiple averages for a common commuting Gaussian action and inputs in L^{2k}. Equal-degree polynomial maps are allowed. The proof supplies a finite Gaussian-degree L² r-variation bound, then uses polynomial density and a multilinear maximal estimate.

The conditional-expectation identity produces Wick products, not ordinary products. The report separately handles every ordinary-product contraction through finite complex spectral measures. This distinction makes the proposal more concrete than an invalid restriction of a product-space conull set to the diagonal. The proposed construction has been sent for independent analytic review, including all normalization, measure, and approximation steps.

The parent checked the actual [Mirek–Trojan Theorem B, page 2](https://arxiv.org/pdf/1405.5566v1): its variation condition is r > max(p,p/(p−1)), hence r > 2 at p=2, and the constant is uniform over coefficients of polynomial maps of fixed degree. The circle-rotation construction for a real polynomial phase must be checked as an application of this single-function theorem; no multiple-function theorem is assumed. A broad additional primary-literature search did not establish an exact duplicate, which is not novelty clearance.

Reproduction: the complete `experiments/i05_crossfield/check.py` output matches `check.json` byte-for-byte. It checks the conditioning and Wick identities through degree eight, a cyclic nonmixing example, and 300 finite variation arrays. All 107 upstream files match SHA-256, Git blob hashes and the complete pinned tree; all eight successful literature downloads and eight recorded artifacts match their hashes. Only the two shared README inputs have changed during intervening integrations. See `parent-verification.json`. These are integrity and finite-algebra checks, not proof certification.

The final convergence proof does **not require the OpenAI corpus**. The accepted all-orders mixing result is used only for an optional limit identification, and that identification is not the proposed advance. This dependency limitation is material to the user's objective. The fresh review must separately assess mathematical correctness, prior art, nonroutine substantiality, and relevance; it must reject promotion if this is a known or routine Gaussian consequence. No MathDB importance ranking or new accepted-finding number is assigned.

The full audit brief and task ID are in `../../iterations/iteration5-crossfield-r2-task.json`. The two rejected routes—known spectral thin-tree consequences and a false entropy-to-subgaussian upgrade—remain research records only.
