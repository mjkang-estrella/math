# C*-algebraic Novak counterexample

**One complete source-conjecture refutation.** The campaign ledger and external proof-packet receipt record final acceptance after extracted replay. Independent source/math/formal/bounded-novelty/manuscript review passes; the unchanged report and parent wording corrections are in reviews/.

MathDB351633; Krishna, published Conjecture4.2 (2022), preprint Conjecture4.3 (2021). In M2(C), take n4,d2, first coordinates0,U,U+V,V and second coordinates0, where U=2πZ and V=π(−7Z+sqrt15 S)/4 for the standard real symmetric Pauli matrices. The literal source matrix is Hermitian, has central entries and has quadratic form cos(πsqrt15)−3≤−2. The scalar and commutative Novak theorems are unaffected. See main.tex/paper.pdf and PROOF.md.

All36declarations in3modules pass an isolated fresh strict replay using Lean4.34.1 and the complete pinned dependency set in verification/pins.json. Every declaration type is recorded in build/verified/Checks.log; only propext, Classical.choice and Quot.sound occur. No assumed spectral identity or residual source hypothesis remains. The endpoint is Novak.source_counterexample_351633. Matrix exponentials, all cosine evaluations, actual inputs, literal two-coordinate source blocks, flattened8x8matrix, Hermitian property and negative quadratic form are proved in Lean.

Reproduce in the existing environment from this directory:

```sh
python3 verification/verify_candidate.py . --lean-bin /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean --packages /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

For another environment, supply a Lean4.34.1 binary and compiled, clean dependency checkouts with the exact revisions in pins.json. The verifier checks revisions and cleanliness, copies the source modules to an isolated build directory, compiles with warningsAsError, inspects all declaration types and checks all reported axioms. It does not update discovery acceptance.

The2-page paper builds cleanly with Tectonic and all final pages were visually inspected. frozen-review-hashes.json pins the exact bytes to be reviewed; the previous larger intermediate layouts are not deliverables. No external publication, posting, upload, author contact or push has occurred.

Local primary-source evidence is preserved under ../../lanes/parent-novak/sources/: actual publisher PDF, arXiv PDF, live complete MathDB snapshot and rendered publishedp799. Published Conjecture4.2 and Definition6 were read directly and visually checked. The independent bounded novelty assessment compares the scalar Novak theorem, later C*-algebraic citations, the distinct Hinrichs–Vybíral conjecture and Krishna2026 Sendov paper. No earlier source-conjecture refutation was found. Semantic Scholar is an incomplete citation index; subscription indexes and a systematic non-English search were unavailable. No absolute worldwide priority is asserted. The independent numerical code uses double precision; exact identities and Lean provide the proof. See reviews/parent-addendum.md.

The proof archive contains the manuscript source/PDF, all three Lean sources, strict verifier and exact dependency pins, all declaration types/axioms, parent and independent audit receipts, both numerical checks, source provenance, complete live MathDB snapshot and unchanged independent review. MANIFEST.json hashes every included file except itself. Run the verifier from this directory with the explicit compiler/package paths above; no generated oleans are trusted or required from the archive.
