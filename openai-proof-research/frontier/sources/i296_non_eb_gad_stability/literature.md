# I296 — primary sources and contribution limits

2026-10-13. Exact versioned sources; no worldwide priority or acceptance claim. No full external bodies or whole-section verbatim excerpts are retained.

## King: the old balanced inequality being strengthened

[Christopher King, Additivity for unital qubit channels, quant-ph/0103156v2](https://arxiv.org/html/quant-ph/0103156v2). Raw SHA256 6f9fc5b396e07054b8f63460cbe6ca5abd6348fb73d468a63a4a33700d74f731; 303853 bytes; matches parent authentication.

Read served lines 24–375: statements, complete Section 2, complete Section 3/Lemma 4 and complete Section 4. Theorem 2 bounds phase-damping output norms; Lemma 4 supplies marginal-balanced phase-damping decompositions; Theorem 3 combines convexity and that bound; (49) follows by differentiation at p=1. These are old results. I296 refutes a proposed positive impurity remainder for their SAME balanced measurement ensemble, not King’s actual theorem.

The elementary exact counterexample and the cat-block rate analysis are independently derived calculations. No quantitative Epstein remainder is imported. Epstein's original paper was not read.

## Amosov: reconstruct the loss before using it

[G. G. Amosov, On estimating the output entropy of a tensor product of the quantum phase-damping channel with an arbitrary channel, 1301.2886v1](https://arxiv.org/html/1301.2886v1). Raw SHA256 67dc32cef1fb79ec72a1914f3edcb8d31380e53f968e96d2572557e1ef0462a2; 217735 bytes; matches parent record.

Read served lines 22–311, including Proposition 5 and its complete proof at 127–195. For a balanced pure qubit input, direct reconstruction uses the normalized support projection sigma=P_support/2, and gives the phase-damping entropy remainder as a relative-entropy data-processing loss. This avoids apparent normalization errors in the served formulas. The counterexample has zero loss. Applying this pure-input proposition to a mixed intermediate dephasing output is still unproved.

## Pinned GAD inputs

Repository [openai/math](https://github.com/openai/math), stipulated revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Exact URL prefix:

    https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/

Read complete sections/output.tex, thermal.tex, partners.tex and special.tex; paper.tex only lines 1–105 and 115–190. Fresh raw bytes match retained files. Relevant labels: eq:channel, lem:partner-branch, eq:recursion, eq:minimum-output-value, eq:thermal-table and cor:unital. These pay minimum output entropy, the thermal/computational branch recursion and the already-established amplitude estimate. They do not assert I296's missing tensor-tail exact-drift estimate. All exact file hashes and URLs are in authentication.

## Credited older stability and test inputs

- [Shor, quant-ph/0201149v1](https://arxiv.org/html/quant-ph/0201149v1): the EB entropy argument used in frozen I289; not a non-EB bridge.
- [Harrow–Montanaro, 1001.0017v6](https://arxiv.org/html/1001.0017v6): mixed-state product-test marginal-purity formula. I293 derives the stronger arbitrary-ensemble drift directly from it.
- [Soleimanifar–Wright, 2201.01824v1](https://arxiv.org/html/2201.01824v1): Theorem 15 global product-test soundness. It would close productness after a new entropy payment, which is not proved here.
- [Bae et al., 1510.07815v1](https://arxiv.org/html/1510.07815v1): depolarizing output-entropy stability precedent. I284's failed CP transfer remains excluded.

These four works are credited through the complete frozen I289/I293 source-reading records; no fresh independent full-proof reads of them are claimed in I296. Their authenticated hashes and read extents remain in those frozen manifests. No new result is attributed to an abstract or search preview.

## New diagnostic and unpaid mechanism

The equatorial Schmidt-label construction gives zero balanced King residual for every admissible ensemble, with positive root impurity and positive exact two-copy drift. Equatorial cats show that even actual GAD tensor tails cannot pay root impurity. Their residual's two analytic rates show why they do not refute actual-tensor-tail exact-drift payment. These are route diagnostics, not a completed non-EB stability theorem or a nominated minor conditional result.

The remaining operation is same-ensemble entropy payment of exact drift for A_s tensor-power tails, or a genuinely amortized/block estimate with global soundness. No inspected primary source pays it here. The bounded two-query search establishes neither literature absence nor novelty. Current count stays 13/20; independent review and contribution assessment remain separate.
