# I25 rooted matching entropy — candidate under independent review

The [completed resumed report](i25-matching-entropy-improvement-resumed.md) proposes a full proof that, for every finite loopless labelled multigraph with a perfect matching, every prescribed feasible mean and every root vertex v,

\[
F-H\le\tfrac32(B-b_v).
\]

Here H is maximum matching-law entropy, F is the sum of edge-choice entropies, B is the sum of complementary edge entropies, and b_v is that complementary sum on the root star. Reserving the root star makes the defect exactly additive across tight odd cuts. Induction can then exclude those cuts at a positive global maximum, where the source covariance method uses only the degree constraints. The strict-coefficient argument and endpoint limit address the six-vertex equality case. This would improve the source's unrestricted coefficient from 2−2/m to (3/2)(1−1/m) on 2m vertices.

The parent read the full report and decisive original source proofs, then reproduced both documented commands. The [parent verification](../experiments/i25-resumed-parent-verification.json) passes: 70 sealed artifacts, 18 pinned sources, 62 source contracts, 10 proof passages, seven primary passages, 20 primary artifacts and all 1,226 unchanged original files. Diagnostics reproduce 33 high-precision retained laws, 75 rational-activity laws with 564 certified rooted inequalities, nine Klee orders, three exact gluing cases and 291 rational trace checks. Only expected shared-ledger/index drift is reported.

A [fresh independent full-proof review](iteration25-rooted-entropy-proof-r2-task.json) is running. A [separate significance review](iteration25-rooted-entropy-novelty-r3-task.json) is also running, independently of the proof review. No acceptance, finding number, priority claim or count increment is assigned. The source comparison must assess the new rooted induction against the strongest existing proof, including its gluing and covariance machinery.

The precision audit confirms that the old apparent rooted ratio 1.3677 was numerical error; it recomputes to about 1.0017. That value plays no role in the proof. The optimal coefficient remains unresolved; the candidate only gives an upper bound of 3/2, with the known lower obstruction approximately 1.35476.

The public record contains the report, proof contracts, diagnostics, manifests and review launch. Ignored source caches and the original local dependency installation remain outside publication; the full local provenance verifier depends on those manifest-described files. None of this candidate's artifacts changes the accepted count of **4/10**.
