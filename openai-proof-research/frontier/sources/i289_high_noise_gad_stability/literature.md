# I289 — primary literature, dependencies and collision boundary

2026-10-13. Bounded source screen only; no worldwide novelty/priority claim. Immutable versioned URLs and raw hashes below authenticate what was fetched. Semantic read extents are independently listed in input-authentication.json and reading-and-failures.md. Full external bodies and complete verbatim sections are not retained.

## Pinned family 276

Repository: https://github.com/openai/math, stipulated revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Prefix:

    https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/

Read complete paper.tex and sections/output.tex, thermal.tex, partners.tex, special.tex. Labels used: eq:channel, eq:v-main, lem:partner-branch, eq:recursion, thm:thermal, eq:thermal-table, cor:partner-additivity, eq:minimum-output-value, cor:unital. Actual minimum-output and partner statements cover arbitrary finite-dimensional partners; the branch states are pure but need not be orthogonal. The completed-square formula sets nu=1/2, gamma=1-s^2 here. Fresh raw bytes match retained files and their exact tree Git blobs. The catalogue lists a single family-276 manuscript, with the companion consequences in these sections.

## Entanglement-breaking additivity

[Peter W. Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v1](https://arxiv.org/html/quant-ph/0201149v1). Raw SHA256: 555bcb6ca31a1818464b94ac93e70834e5560eddd8d637c0b6c71a26d89f14cd.

Theorem 1 and equations (5), (7)–(14) are the closest direct predecessor. The proof keeps the EB marginal entropy and the average partner-output entropies through SSA. Read its representation and full proof. I289 specializes this argument to an explicit rank-one POVM; the prepared replacement states are mixed, with their entropies canceling in the classical extension. Shor's theorem itself is an additivity statement and is credited accordingly.

## Global product-test soundness

[Aram Harrow and Ashley Montanaro, Testing product states, quantum Merlin-Arthur games and tensor optimisation, arXiv:1001.0017v6](https://arxiv.org/html/1001.0017v6). Raw SHA256: ae7e1d2e4016a1586948e5f3b3416b183a19ef0427dfe3ed5b59edc4852c5daa.

Read Theorem 1 and complete Appendices A–B. This provides the original dimension-independent product-test stability comparator. I289 does not claim that stability is new. The final proof uses the simpler verified theorem below, so no reconstruction of literal typographical or continuity concerns in the served older proof is a premise.

[Mehdi Soleimanifar and John Wright, Testing matrix product states, arXiv:2201.01824v1](https://arxiv.org/html/2201.01824v1). Raw SHA256: ef9b18ae0a3714d124a755233d20409b16abb5c1d20d94f06c4f399c9e95a998.

Theorem 15 states product-test acceptance at most 2/3 + omega^2/3 for closest-product squared overlap omega, for every number of parties and all finite local dimensions. Read its full §2.1 induction, not just the statement. This implies product infidelity <= 3 times test failure and is the exact older global soundness premise. Theorem 8's sharper curve and later 2026 improvements are unnecessary.

## Output-entropy stability comparator

[Eunok Bae, Gilad Gour, Soojoon Lee, Jeonghoon Park and Barry C. Sanders, Stability theorem of depolarizing channels for the minimal output quantum Rényi entropies, arXiv:1510.07815v1](https://arxiv.org/html/1510.07815v1). Raw SHA256: b846df10ea9221db81fbdd01dfc67cc9ff07217e319e2e00d1080914cc4ee85a.

Read §§II–III, particularly Lemma 5, its proof, the von Neumann remark (44)–(45), and Theorem 6. Its channel is isotropic depolarizing; its closest-product Taylor method is a comparator, not an automatic GAD result. I284's non-CP same-s postmap remains excluded. No Taylor remainder or n-uniform radius from this paper is used by I289.

## Exact contribution boundary

The older sources pay EB entropy additivity and global test soundness. The shared author/parent connecting deduction bounds product-test failure by the same conditional impurity budget that Shor's recursion pays, for any rank-one measurement tree. Full-law latitude rounding uses I280's already paid amplitude KL estimate. Neither inspected older theorem literally states the displayed GAD equatorial-distance bound; this is a deduction, not an attributed quotation. Its short modular proof may be judged technical by independent contribution review. No independent substantiality or acceptance verdict is issued.

I288's fixed-parity-rank finite-core reduction is a spent comparator with complexity-dependent constants. I289 replaces its finite-core mechanism and has no phase-rank parameter. Full non-EB GAD U remains outside the claim. The authorized parent supplement is shared input, authenticated separately; it is not an external publication or an independent final proof review.

Searches covered EB minimum-output strong additivity, quantitative output-entropy stability, product-test soundness and combinations of Shor/product tests/GAD. Search hits and abstract previews outside the stated extents are leads only. An exact prior GAD theorem was not established in this screen; that absence supports no worldwide priority conclusion. No full-paper snapshots or verbatim excerpts were added to deliverables.
