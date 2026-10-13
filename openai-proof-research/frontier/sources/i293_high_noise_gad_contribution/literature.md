# I293 — primary-source contribution comparison

2026-10-13. Bounded screen; no worldwide priority claim. No external full bodies, full sections or verbatim excerpts retained. Exact semantic extents and byte authentication are in the experiment manifest.

## Pinned family 276

Repository https://github.com/openai/math; stipulated revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

Complete actual files read, with fresh immutable raw bytes matching the retained copies and exact-path Git blobs:

- [paper.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/paper.tex), SHA256 c25bd71e406cca4f77e1424f33c23aa1e1e56ecbdafedf2ad2c4dac0f0a1c24b.
- [output.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/output.tex), SHA256 d78c9e8b7d4a9623db2e23241fc20f047f6ad976f6d9ab4bc8fbd9ba98d2c542.
- [thermal.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/thermal.tex), SHA256 52a3470b411125ba69e7f39cc78c611695c895059288e212e3c5407a69882d14.
- [partners.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/partners.tex), SHA256 32360b66c1d91858469873fc16e89112ea428c9386114f57ff6f654bde72102f.
- [special.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/special.tex), SHA256 ef9e0122760b79dc2f7dfb120d1ab6914ecc9760cbbdae03089e7709c987b0c1.

Relevant labels: eq:channel, eq:v-main, lem:partner-branch, eq:partner-branch, eq:recursion, thm:thermal, eq:thermal-table, cor:partner-additivity, eq:minimum-output-value, cor:unital. Actual statements admit arbitrary finite-dimensional partners and nonorthogonal pure branches. The pinned companion consequences do not literally state the I289 stability estimate. Their truth is stipulated.

## Closest older primary results

[Peter W. Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, quant-ph/0201149v1](https://arxiv.org/html/quant-ph/0201149v1).

Raw SHA256 555bcb6ca31a1818464b94ac93e70834e5560eddd8d637c0b6c71a26d89f14cd. Read the representation (5) and complete Theorem 1 proof (7)–(14), not only its additivity statement. The proof retains marginal output entropy and average partner-output entropy. Refining the POVM and preserving that local gap supplies the target recursion. Mixed preparations are handled by classical-block cancellation. This source supplies additivity/SSA structure, not a literal global stability theorem.

[Aram W. Harrow and Ashley Montanaro, Testing product states, quantum Merlin-Arthur games and tensor optimisation, 1001.0017v6](https://arxiv.org/html/1001.0017v6).

Raw SHA256 ae7e1d2e4016a1586948e5f3b3416b183a19ef0427dfe3ed5b59edc4852c5daa. Read Theorem 1 and complete Appendices A–B. The decisive comparator is Lemma 2 with its proof: product-test acceptance on mixed states equals the average of marginal purities. The review derives arbitrary-ensemble drift from this old identity via complementary purities, quadratic variance and trace-norm contractivity. Its global theorem already removes dependence on tensor length and local dimension. Literal display concerns in the old soundness proof are not repaired or needed as premises.

[Mehdi Soleimanifar and John Wright, Testing matrix product states, 2201.01824v1](https://arxiv.org/html/2201.01824v1).

Raw SHA256 ef9b18ae0a3714d124a755233d20409b16abb5c1d20d94f06c4f399c9e95a998. Read definitions and the complete §2.1 Theorem 15 induction, equations (1)–(3). The overlap is squared product overlap omega; acceptance <=2/3+omega²/3 implies infidelity <=3 failure globally. This is the verified soundness premise. The sharper Theorem 8 proof is unnecessary.

[Eunok Bae, Gilad Gour, Soojoon Lee, Jeonghoon Park and Barry C. Sanders, Stability theorem of depolarizing channels for the minimal output quantum Rényi entropies, 1510.07815v1](https://arxiv.org/html/1510.07815v1).

Raw SHA256 b846df10ea9221db81fbdd01dfc67cc9ff07217e319e2e00d1080914cc4ee85a. Read complete §§II–III, including the Taylor calculation, Lemma 5 full proof, von Neumann remark (44)–(45), Theorem 6 full proof and Theorem 7. This is the closest output-entropy stability precedent inspected. It uses isotropic depolarizing channels and expansion at a closest product; its displayed remainder is not a dimension-uniform GAD transfer theorem. The review does not assume or adjudicate such a transfer. The served compilation date is not used to date submission priority.

## Project overlap and verdict limits

I280's completed amplitude KL estimate is paid. I284 rules out the same-s CP depolarizing postmap. I288's bounded-k result is a separate finite-complexity comparator and cannot be promoted to rank-unrestricted stability by letting k grow.

The exact shared author/parent contribution is same-tree quadratic drift plus full-law latitude rounding. The review independently reduces the drift to Harrow–Montanaro's older mixed-state formula with ordinary norm inequalities, then uses Shor, global soundness and paid KL to recover the entire target. The old sources are credited for what they actually prove; the connecting inference is explicitly a reviewer deduction, not an attributed quotation or demonstrated earlier publication.

This supports TECHNICAL, while acknowledging genuine unrestricted progress in the claimed EB region. No non-EB theorem, second nomination for s<=sqrt(2)-1, acceptance or count change follows.

Bounded searches used the queries "entanglement breaking" "stability" "minimum output entropy"; "product test" "Shor" entropy stability; and "amplitude damping" "stability" "product states" entropy. Search previews were leads only; no additional theorem was imported from them. Search absence provides no novelty or priority evidence. Literature priority remains UNRESOLVED.
