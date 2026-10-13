# I294 — independent PROOF review of frozen I289

2026-10-13. **Verdict: PASS for the unchanged original theorem and PASS for its stated same-proof interval extension. No mathematical repair is required.** This is an independent proof review, conditional only on the requested stipulation of the pinned OpenAI results. It is not a contribution, priority, or acceptance verdict. The current project total is **13/20**, per the user's metadata update; I294 makes no count change.

The reviewed analysis SHA256 is `063466c7963eb9696af1d6fe4e07a3bbb328842a55b4ecfa09b6759004be9e02`; the report SHA256 is `4e68aa6bcfd55732a9dc2f08240e56928beacae44fd6deb7a4a744a6f4eb9fbe`. Both were checked directly and remained unchanged. All five authored deliverables and the explicitly authorized parent bridge were read. Author and parent proof assurances were not used as independent evidence.

For every integer n >= 1, every pure n-qubit input psi, and 0 < s <= 1/3, the proof establishes, in nats and with unhalved trace norm,

    inf_(equatorial pure product phi) ||Ppsi-Pphi||_1^2
       <= [240+32/(1-s^2)] D_s(psi)/s^2
       <= 276 D_s(psi)/s^2.

There is no phase-rank, support, Schmidt-rank, complexity, or closeness restriction. The same first inequality holds for 0 < s <= sqrt(2)-1, including its endpoint. The 276 simplification is asserted only on the original interval: the numerator at the extension endpoint is 256+16 sqrt(2), which exceeds 276.

The independent recomputation in [analysis](../experiments/i294_high_noise_gad_proof/analysis.md) verifies every requested link:

- The exact channel decomposition has nonnegative weights summing to one and rank-one nonzero effects. Its conditioned tail inputs are pure even for the mixed replacement preparations.
- SSA has the required lower-bound direction. Shannon and preparation entropy terms cancel exactly. The qubit impurity cost is 2 s^2 det(rho_first).
- The pure-input swap identity is exact. Expanding the quadratic ensemble drift gives an upper bound of 4 det(rho_first), without assuming its sign. Using the same EB ensembles yields F <= 2 D_s/s^2 with coefficient-one induction.
- [Soleimanifar–Wright v1, Theorem 15](https://arxiv.org/html/2201.01824v1) uses squared closest-product overlap and the same test projector. Its full induction was recomputed, giving epsilon <= 3F. [Shor v1, Theorem 1](https://arxiv.org/html/quant-ph/0201149v1) was read in full through its proof; the mixed-preparation specialization was derived directly.
- The actual pinned family-276 pure branch statement yields D_s >= (1-s^2)s^2 KL(q||uniform)/2. This uses its own computational tree; the two resulting bounds are combined only after each induction is complete.
- Full-law Hellinger rounding gives squared unhalved trace distance <= 40 epsilon+16 D_s/c_s. Substitution yields the displayed constants.

Zero-probability and deterministic branches, empty tails, poles, n=1, D_s=0, s=1/3, and s=sqrt(2)-1 cause no gap. No numerical evidence is used. The endpoint with zero replacement weight is handled by omitting zero effects. No non-EB statement is inferred.

[Reading boundaries](../experiments/i294_high_noise_gad_proof/reading-and-failures.md), [source authentication](../experiments/i294_high_noise_gad_proof/input-authentication.json), and [literature](../sources/i294_high_noise_gad_proof/literature.md) record exact identities and semantic extents. No live contribution sibling, R019, or other live sibling was read. Only the five assigned I294 files were written; no subagents, shared-index edits, staging, commits, or publication occurred.
