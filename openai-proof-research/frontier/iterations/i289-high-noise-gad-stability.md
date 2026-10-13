# I289 — global unital GAD stability in the EB regime

2026-10-13. **Verdict: the assigned rank-unrestricted all-n theorem is proved. No independent acceptance or substantiality claim; priority remains unresolved.** Twelve accepted findings toward twenty are unchanged. All OpenAI results at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

For every 0 < s <= 1/3, every n >= 1, and every normalized pure n-qubit input psi, with entropy in nats and unhalved trace norm,

    inf_(phi in M_n) ||Ppsi - Pphi||_1^2
      <= [(240 + 32/(1-s^2))/s^2] D_s(psi)
      <= (276/s^2) D_s(psi).

Here A_s has Bloch multipliers (s,s,s^2), D_s is its output entropy minus n h((1+s)/2), and M_n consists of products of equatorial pure qubits. There is no phase-rank, Schmidt-rank, support, complexity, or closeness restriction. The constant 276/a^2 is uniform on any [a,b] contained in (0,1/3]. It is not uniform as s tends to zero.

The [complete proof](../experiments/i289_high_noise_gad_stability/analysis.md) separates arbitrary productness from latitude selection. Its chain is:

1. The exact measure-and-prepare decomposition is A_s = s Dephase_X + s Dephase_Y + s^2 Dephase_Z + (1-2s-s^2) Depolarize_0. Its nonzero POVM effects are rank one, so measuring the first qubit leaves pure conditional tail inputs.
2. Shor's strong-subadditivity argument retains S(A_s(rho_first)) in the entropy recursion. The direct one-copy gap is at least 2s^2 det(rho_first), so D_s pays the sum of conditional marginal determinants along this measurement tree.
3. The two-copy product-test failure F obeys F_n <= E F_tail + 4 det(rho_first) for any pure tail ensemble. It telescopes on the same tree to F_n <= 2D_s/s^2. This is the shared author/parent bridge, proved in two forms in the analysis and credited to the authorized parent supplement.
4. The older [Soleimanifar–Wright Theorem 15](https://arxiv.org/html/2201.01824v1) gives closest-product infidelity epsilon <= 3F_n, hence epsilon <= 6D_s/s^2. Its full induction proof was read and checked. This is global soundness, without a Taylor radius.
5. I280's paid computational-amplitude KL estimate is rederived from the actual pinned thermal branch inequality: D_s >= (1-s^2)s^2 KL(q||uniform)/2. Hellinger rounding of the closest product's full amplitude law then gives equatorial distance squared <= 40 epsilon + 32D_s/((1-s^2)s^2).

The [Shor primary proof](https://arxiv.org/html/quant-ph/0201149v1), Theorem 1 and equations (5), (7)–(14), is credited for the entropy recursion. The connecting estimate uses a quadratic two-copy observable, rather than an inverse channel or the refuted sum of original marginal determinants. It replaces I288's complexity-dependent finite core completely.

The initial depolarizing/transpose mixture approach was investigated and left an unpaid heterogeneous-branch stability estimate; selecting its all-depolarizing branch has exponentially small weight. The successful EB measurement approach closes that missing productness mechanism directly. Partial transpose was never assigned entropy invariance. Zero outcomes, mixed preparation states, empty tails, poles, input zeros, n=1, D_s=0 and s=1/3 are covered explicitly.

The same unsimplified constant works up to s = sqrt(2)-1, where the replacement weight can vanish; this is a checked extension of the same unital theorem, not a second finding. Full non-EB U is not settled. The parent's general interior EB GAD suggestion is recorded as shared context and is not nominated as an additional result here.

Closest contribution collisions are Shor EB additivity, Harrow–Montanaro product-test stability, Soleimanifar–Wright product-test soundness, and Bae et al.'s depolarizing output-entropy stability. These older results pay substantial parts of the proof. The exact additional connection is the arbitrary-ensemble product-test drift and its same-tree entropy payment, shared with the parent, plus latitude rounding using the paid amplitude theorem. The short assembly may warrant a technical classification on independent contribution review; no exact external duplicate was established by the bounded screen, and search absence makes no priority claim.

[Literature and immutable URLs](../sources/i289_high_noise_gad_stability/literature.md), [reading and failures](../experiments/i289_high_noise_gad_stability/reading-and-failures.md), and [authentication](../experiments/i289_high_noise_gad_stability/input-authentication.json) specify exact read extents and hashes. No subagents, I287 or other live sibling reads, shared-index edits, staging, commits, publishing, numerical scans or giant history replay were used. Only assigned I289 deliverables were written; full external bodies were read in memory and not retained. Detached hashes accompany the handoff.
