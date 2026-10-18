# Source and operation comparison

Pinned revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Theorems are stipulated; this is application/hypothesis comparison, not an upstream truth audit. Exact paths, URLs, sizes and hashes of all 26 non-PDF source blobs are in receipts.json. The complete family inventory has 37 entries, 28 blobs including two PDFs; PDFs were not retrieved.

For Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026:

- build/paper.tex, thm:fourier and cor:dichotomy: outside Tao's cubic class, all first charges α vanish. This is already paid, not T266's new part.
- 02-pair-moments.tex, prop:pair-certificate: exact positive pair identity at total order 10; its contraction/normal-form machinery is credited.
- 03-cubic.tex, prop:cubic-classification: H and H entrywise squared Hadamard imply the cubic class. No third-charge orientation classification follows from this assertion alone.
- 03-complete-family.tex, lem:basic: row orthogonality, same-matrix contraction and different-matrix cross identities survive for triplets. The order-two sum uses seven bases. prop:cubic-exclusion there is a seven-basis argument; its introductory citation to the stronger primary triplet exclusion must not be confused with that proposition's own scope.
- 04-mixed.tex, lem:gram and lem:mixed-reductions: the shared-column Gram entry has 1/5 and 4/5 weights, and singleton elimination uses the complete-family sum. These exact operations fail unchanged for triplets. prop:mixed-certificate excludes seven bases under first-charge vanishing; it is not an orientation-product identity for triplets.
- 05-verification.tex, finite selection of pair and mixed relations: the actual selected table has total order at most 11. It is not a theorem bounding every possible certificate degree.

For The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026, build/sections/introduction.tex: the main theorem excludes four bases under its stated binary64/compiler/complete-execution contract. The lower-bound construction gives the tensor-product triplet used here. Nonexistence of four bases supplies no converse classification of the surviving triplets. No new assertion here removes the source's execution contract.

The exact unpaid target is already proposed in Matolcsi–Matszangosz–Varga–Weiner, [Triplets of Mutually Unbiased Bases](https://arxiv.org/html/2503.14752v2), Conjecture 2 and (4.9). Their cube representation and binary-vector criteria are credited. Neither numerical triplet searches nor the stronger conjectural family classification constitute its proof. The present 10×10 reduction uses elementary complementary products and Newton's identity; it is technical support, with no independent novelty claim.

[Brierley–Weigert](https://arxiv.org/html/0901.4051v2), §3.4, §4.1 and Table 1, gives the cubic-pair triplet exclusion. Its method enumerates unbiased vectors by polynomial equations and controls numerical root errors. That antecedent supplies the already-known first-charge input together with the pinned Fourier theorem. Its computation was not independently rerun here.

A complete T266 proof could be substantial, but none is delivered. No parameter-family result, dimensional change, normal-form reformulation or source-certificate adaptation is nominated instead.
