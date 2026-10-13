# I293 — contribution review of rank-unrestricted high-noise GAD stability

2026-10-13. **TECHNICAL. No analytic flaw found in the frozen theorem; literature priority UNRESOLVED. No acceptance claim.** Current total: 13/20, reflecting the user's metadata update only. This review changes no count and does not read R019.

The complete I289 analysis was read and authenticated at SHA256 063466c7963eb9696af1d6fe4e07a3bbb328842a55b4ecfa09b6759004be9e02; report SHA256 4e68aa6bcfd55732a9dc2f08240e56928beacae44fd6deb7a4a744a6f4eb9fbe also matches. All pinned OpenAI results at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The author and parent's shared bridge is credited input, not independent validation.

The target is genuinely unrestricted: for every n, every pure input and 0<s<=1/3, the squared unhalved trace distance to equatorial pure products is at most [240+32/(1-s²)]D_s/s²<=276D_s/s². It does not impose bounded phase rank, support, closeness or complexity. I288's fixed-k theorem cannot supply this by taking k unbounded.

The decisive comparison is constructive. [Harrow–Montanaro Lemma 2](https://arxiv.org/html/1001.0017v6) expresses mixed-state product-test acceptance as the average of marginal purities. For a pure first-party/tail input and any pure ensemble of its tail marginal, complementary purities and the quadratic variance identity give

    F_n(psi)<=sum_i p_i F_(n-1)(chi_i)+1-Tr(rho_first²).

The proof uses only traceless-Hermitian ||Y||_2²<=||Y||_1²/2, partial-trace contractivity and the pure-projector distance formula. It is derived explicitly in the [review analysis](../experiments/i293_high_noise_gad_contribution/analysis.md), without assuming the proposed author/parent lemma. [Shor's full Theorem 1 proof](https://arxiv.org/html/quant-ph/0201149v1), especially (5) and (7)–(14), retains the same marginal entropy and pure conditional tails. The explicit EB representation and one-site Bloch gap then give F_n<=D_s/s² by induction. [Soleimanifar–Wright Theorem 15](https://arxiv.org/html/2201.01824v1), with its complete §2.1 proof, gives closest-product infidelity epsilon<=3F_n for every n and arbitrary defects.

I280's paid full-law KL estimate and Hellinger rounding give equatorial distance squared <=40epsilon+16D_s/c_s, c_s=(1-s²)s²/2. Thus the reduction recovers the requested bound, even with 120 in place of 240. The smaller coefficient is a containment certificate, not a separate nomination. No unproved entropy tensorization, selected rare branch, growing induction coefficient, or finite-core loss is hidden.

The exact new assembly is useful: a quadratic test aligns Shor's conditional impurity budget with global productness, and full-law rounding selects the equator without n separate latitude errors. Nevertheless, both connections follow from the older mixed-state purity formula and elementary metric inequalities with the paid amplitude estimate. This explicit unrestricted reduction supports TECHNICAL under the unchanged standard; scope and proof brevity alone would not justify that classification.

[Bae et al.](https://arxiv.org/html/1510.07815v1), read through the actual §§II–III proofs and von Neumann remark, credits depolarizing output-entropy stability as prior work. It does not give a GAD transfer; I284's non-CP same-s postmap remains excluded. The actual pinned family-276 source and all four specified companion sections were read and authenticated. The author's weaker drift and constants are valid on analytic checking.

No exact earlier published GAD theorem or worldwide priority conclusion is established. The old-result reduction is a reviewer deduction, not a quotation or claim that the displayed theorem was previously published. The same unsimplified theorem extends to s<=sqrt(2)-1, with no second nomination and no non-EB claim. This contribution review does not certify a separate formal proof gate or an acceptance.

[Literature and exact URLs](../sources/i293_high_noise_gad_contribution/literature.md), [read boundaries and failed shortcuts](../experiments/i293_high_noise_gad_contribution/reading-and-failures.md), and [authentication](../experiments/i293_high_noise_gad_contribution/input-authentication.json) provide the audit record. Only assigned I293 deliverables were written; detached SHA256s accompany the handoff.
