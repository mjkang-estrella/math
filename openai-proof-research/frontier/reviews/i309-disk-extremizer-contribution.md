# I309 — independent contribution review of disk-extremizer rigidity

2026-10-13. **Verdict: TECHNICAL/KNOWN ONLY for the entire exact-plus-quantitative package.** This is a contribution decision, not a replacement proof gate. I308 was not read; neither a qualitative proof pass nor a Q310 proof pass is presumed. Thirteen accepted findings remain thirteen.

The three frozen candidate hashes match the instruction: I307 `597263620687b02e8f98a9558b9816cfe539af34b24d95aa1dee7b21394f7e1b`, I306 `14fe4d62f111e08ba3f8b4b8a26b168d08c45a1ec5739bfa8f2c6281efaa1c89`, and I310 `502d91e44fefdc9a0e396c7cad9a52e0cbd946873bad4cef2468eebc6e8fe7ef`. Their authentication records and all declared local whole-file and passage hashes were checked. The pinned OpenAI theorem truth is stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Decisive exact-scope antecedent

[Gau–Wu, *Inner functions of numerical contractions*, LAA 430 (2009), 2182–2191](https://ir.lib.nycu.edu.tw/server/api/core/bitstreams/761cc49b-4b82-4fd4-8748-960e6473e874/content), Theorems 2 and 8, covers **all scalar H∞ functions**, not only polynomials or disk-algebra functions. A norm-two attained scalar function yields a reducing summand similar to the model operator with minimal inner function `φ=zf`. The whole substantive article, including Theorem 8's proof, was read. This supplies a stronger earlier equality classification than E307.

Here is the same-scope reduction, rather than a search-miss argument. Interior finite spectrum excludes unitary parts and makes the old calculus agree with Taylor evaluation. The model summand is finite-dimensional, so f is a finite Blaschke product. If its zero orders are r at zero and kλ elsewhere, the summand's minimal polynomial is

    z^(r+1) product_(λ≠0) (z-λ)^kλ.

It divides the original matrix's minimal polynomial. Thus every nonzero zero is an eigenvalue, `kλ≤νλ`, and `1≤r≤ν0−1`; in particular `ν0≥2`. Blaschke factorization gives the asserted poles. For a nilpotent matrix this forces a monomial. Compactness of its finitely many Schur jets gives the exact scalar-SUPREMUM criterion. These steps are detailed in the [analysis](../experiments/i309_disk_extremizer_contribution/analysis.md).

I306's strict scalar/complete separation is indeed stronger than R019's coefficient-compression obstruction. Nevertheless, its scalar side follows from this old equality theorem and the already checked power norms; its complete side is R019. Neither the old LSS matrix nor the accepted entangled witness is counted again.

## Quantitative contribution assessed separately

No inspected publication is claimed to state Q310's particular power-gap modulus or constants. ACV v3's approximate reducing-block and representing-measure estimates concern different quantities; they do not automatically imply Q310.

The negative judgment on Q310 instead uses a concrete routine reduction: retain the deficit in the pinned scalar disk ordered-test/positive-block argument; use Cauchy–Schwarz and Parseval to obtain a degree-at-most-L−1 polynomial q with

    ||f−q||₂≤sqrt(ε),   |||q|²−1||₁≤(17/4)sqrt(ε),
    ε=4−||f(A)||².

Its highest autocorrelation bounds the product of its endpoint coefficients. Repeatedly delete the smaller endpoint, with recurrence `C_d=1+6C_(d−1)`, and then use `||Σ c_k A^k||≤2sqrt(L)||c||₂`. This yields exactly `D_L=1+2sqrt(L)(1+17·6^(L−1))` and the proposed Q310 bound. The [analysis](../experiments/i309_disk_extremizer_contribution/analysis.md) displays the intervening estimates and constant propagation. This is an explicit, useful quantitative deduction, but under the unchanged I246/I292 standard it is deficit bookkeeping and elementary finite-coefficient stability, rather than a new structural bridge. A separate Q310 proof audit remains necessary if the parent pursues acceptance; this review does not certify it.

The ACV, Crouzeix, Berger–Stampfli/Drury and KMR comparisons are bounded to the actual passages read. In particular KMR's positive partial fractions were tested at equality; they are not falsely cited as stating E307. Source versions, hashes, extents and retrieval limits are in [literature.md](../sources/i309_disk_extremizer_contribution/literature.md), [reading-and-failures.md](../experiments/i309_disk_extremizer_contribution/reading-and-failures.md), and [input-authentication.json](../experiments/i309_disk_extremizer_contribution/input-authentication.json). No acceptance/count edit, worldwide-priority assertion or separate I306/I310 slot follows.
