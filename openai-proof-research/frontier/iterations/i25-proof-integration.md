# I25 rooted matching entropy — accepted as R011

**Final acceptance, 2026-10-09:** [R011](../findings/R011-rooted-matching-entropy.md) is the fifth substantial finding. Independent full-proof PASS and separate SUBSTANTIAL significance verdict both pass parent verification. [Acceptance evidence](../experiments/i25-novelty-r3-parent-verification.json). The following integration details preserve the proof-stage history; current acceptance is governed by R011.

The [completed resumed report](i25-matching-entropy-improvement-resumed.md) proposes a full proof that, for every finite loopless labelled multigraph with a perfect matching, every prescribed feasible mean and every root vertex v,

\[
F-H\le\tfrac32(B-b_v).
\]

Here H is maximum matching-law entropy, F is the sum of edge-choice entropies, B is the sum of complementary edge entropies, and b_v is that complementary sum on the root star. Reserving the root star makes the defect exactly additive across tight odd cuts. Induction can then exclude those cuts at a positive global maximum, where the source covariance method uses only the degree constraints. The strict-coefficient argument and endpoint limit address the six-vertex equality case. This would improve the source's unrestricted coefficient from 2−2/m to (3/2)(1−1/m) on 2m vertices.

The parent read the full report and decisive original source proofs, then reproduced both documented commands. The [parent verification](../experiments/i25-resumed-parent-verification.json) passes: 70 sealed artifacts, 18 pinned sources, 62 source contracts, 10 proof passages, seven primary passages, 20 primary artifacts and all 1,226 unchanged original files. Diagnostics reproduce 33 high-precision retained laws, 75 rational-activity laws with 564 certified rooted inequalities, nine Klee orders, three exact gluing cases and 291 rational trace checks. Only expected shared-ledger/index drift is reported.

The [independent full-proof review](../reviews/i25-rooted-entropy-proof-r2.md) gives **full-theorem PASS, no repairs required**. The parent read the full review and reproduced its independent diagnostics and verifier: 78 review artifacts, 68 frozen inputs, 1,297 preserved files and 20 review read contracts, with no errors. Exact checks cover asymmetric labelled gluing, repeated contracted-root propagation, parallel collapse and boundary reductions; the ancillary Klee and counting claims also pass. [Parent R2 verification](../experiments/i25-proof-r2-parent-verification.json). The [separate significance review](../reviews/i25-rooted-entropy-novelty-r3.md) is complete and judges the combined mechanism substantial. R011 records acceptance; worldwide priority remains unverified. The source comparison must assess the new rooted induction against the strongest existing proof, including its gluing and covariance machinery.

The precision audit confirms that the old apparent rooted ratio 1.3677 was numerical error; it recomputes to about 1.0017. That value plays no role in the proof. The optimal coefficient remains unresolved; the candidate only gives an upper bound of 3/2, with the known lower obstruction approximately 1.35476.

The public record contains the report, proof contracts, diagnostics, manifests and review launch. Ignored source caches and the original local dependency installation remain outside publication; the full local provenance verifier depends on those manifest-described files. The final reviewed result advances the accepted count to **5/10**; historical candidate files retain their original status.
