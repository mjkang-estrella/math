# I347 — reading, validation, and failed closure attempts

Date: 2026-10-13. Target: predictable quadratic variation for the exact SAT hitting time. Status: unresolved, with the finite two-root partial in analysis.md proved.

## Inputs actually read and authenticated

Read the assigned brief in full, AGENTS.md, sources/upstream.json, the relevant SAT entries of sources/CONTENTS.md, and the corresponding paths in sources/preprints-tree.json. Read all five finalized I343 artifacts, including their source manifest. Large concatenated outputs were truncated; the omitted scopes were subsequently re-emitted in smaller chunks. All five supplied detached hashes match exactly. This round independently validates only the partials needed for this continuation; the older manifest's unrelated source-reading claims are not silently adopted as fresh reads.

Freshly retrieved from the pinned raw OpenAI/math revision, held only in memory, and authenticated against the I343 manifest:

- Linear-Variance-of-the-Random-3-SAT-Hitting-Time-October-5-2026/build/source/main.tex: actual main theorem, lines 61–70; potential setup and proof, 155–264; root exposure, product law, filtrations and flip tests, 306–418; occupation and duration, 428–488; limit-law disclaimer, 706–709.
- Variance-of-the-Random-k-SAT-Hitting-Time-September-27-2026/build/source/sections/deletion.tex: all 298 lines, especially lem:conditional-product and lem:root-flip-tests.
- The same manuscript's occupation.tex, lines 220–331: lem:weighted-root-counts, joint factorial incidence identity and averaging proof.
- introduction.tex, lines 1–105: exact model, thm:variance, cap lower bound B > U_k, source scope and finite-size centering.
- conventions.tex, lines 1–145: prop:cap-bridge, floor correction, and exponentially late cap.

All five fresh upstream hashes match the I343 records. These are precise partial reading scopes, not claims of rereading every companion manuscript. No computability or pressure theorem is needed for this continuation.

Primary external reading was narrowly targeted to the unpaid bridge: Major's authored martingale CLT notes, PDF pp. 1–4, actual conditions (1.2)–(1.3); Chatterjee's A new method of normal approximation, arXiv:math/0611213v4, PDF pp. 1–4, definition (1) and Theorem 2.2. Both PDF byte hashes were freshly computed in memory. No full external body was saved. An incorrectly recalled arXiv identifier 0801.2445 led to an unrelated bilaplacian paper; it was recognized and excluded, and a targeted search located the correct primary paper. A query for the exact SAT quadratic-variation target did not supply the missing estimate. This was not a comprehensive novelty survey or a proof of absence.

## Independent I343 checks

The analysis rederives the needed (k−1)-deletion moment, rather than treating it as stipulated. In particular:

1. One-clause killing probabilities use falling factorials for proper clauses. Exactly k−1 frozen coordinates contribute an O(u^(−k)) error even though one proper k-clause cannot kill that set.
2. The root exposure leaves both ordinary contents and the test parts conditionally independent. S_m is measurable in the smaller filtration; the deletion event is measurable only in the larger one. Future ordinary contents remain fresh there.
3. Occupation telescoping starts after the deleted index. Every future nonordinary step is charged, and the cap error retains its dependence on B.
4. Higher-duration moments follow by conditional induction at every future history. No inequality reversing Jensen is used.
5. Every collision count 0,…,k−1 is paid before averaging. The one-surviving-root case bounds the summand directly; dividing its weight by p^β would fail near zero. Only V ≥ k uses the raw cap.
6. Incidence and collision counts are averaged jointly through factorial expansion. Their independence is not assumed. The intermediate exponent is v/β−v = −v/k.
7. The natural Doob filtration is distinct from the static root exposure. Only already averaged moments are transferred. They establish conditional Lindeberg in L¹ for k ≥ 4.
8. The 3/2-moment argument covers realized/predictable variation at k = 4. The fourth-moment argument applies only at k ≥ 5. Late-cap transfer uses the exact mean and variance.

The folded-normal example was also checked as an abstract logical countermodel: bounded omissions and vanishing first projections can coexist with a nonnormal standardized limit. It is not a SAT counterexample. Variable/sign symmetry does force first-order clause degeneracy; arbitrary permutation of clause positions does not preserve hitting time.

## New two-root validation

The redundant-killing moment uses disjoint fixed clauses and their joint falsifying assignment. Redundant killing forces every background solution into that single joint slice, so the product of 2k necessary root tests is legitimate under the specified lower filtration. Ordinary clauses still have size k; hence β remains k/(k−1). The moment balances at 2(k−1), not at 2k−1. Every collision count v < 2k is kept, including v = 2k−1 separately; cap-only events cost n^(−2). Small n and cap endpoints have no missing cases.

The cooperative estimate uses a different argument. Fixing the other root-disjoint clause inserts one deterministic monotone constraint into the one-root proof. Charge its occupation step rather than claiming a fresh random drift. This preserves the endpoint (k−1)-moment. An explicit equality-gadget formula verifies that cooperative killing can have an empty joint falsifying slice and no background union-root collisions. The gadget is proved symbolically using all padding sign patterns; no SAT computation or scan was performed.

## Routes attacked and their stopping points

**Double deletion.** The exact signed decomposition distinguishes redundant and cooperative killing. The first branch admits the stronger two-root estimate; the second does not force the solution set into the joint slice. Applying the first proof to both branches would be a conditioning error.

**Root sparsity as interaction locality.** Marked-root intersections and background union-root collisions are rare, and can be charged for bounded kernels. The equality gadget disproves the assertion that all mixed interactions require such collisions. Long logical relations in the common ordinary environment remain possible. Its finite positive probability says nothing about their typical asymptotic size.

**Ghost resampling.** A resampling mixed difference is an alternating sum of four double-omission mixed differences. The paid occupation moments bound those terms but do not show their decay or collective decorrelation. There is no signed cancellation estimate in hand.

**Posterior variance.** The Doob martingale of Q has increment W_j−E[W_j|past], where W_j = Var(T|ℱ_j). This yields an exact squared future-covariance sum. For k ≥ 5 the delay-variance remainder is paid; covariance of the signed ghost delay with the omitted hitting time is not. Fourth moments give O(n²) for the sum, precisely missing little-o.

**The k = 4 fourth-moment shortage.** Truncating ghost differences before the conditional square produces bounded v_i^[K] and an L¹ bracket approximation with error Cn/K. Its off-diagonal covariance still needs a four-future-replica estimate. Truncation removes integrability difficulties, not the underlying SAT correlations.

**Changing to Stein's kernel.** Its cubic error is paid by the validated third delay moment. Its conditional kernel variance is another joint estimate, and was not inferred from the correctness of its expectation.

**Bystanders, fresh input blocks, and first projections.** No conditional core-width estimate or regenerative residual-state theorem is available from the validated inputs. First projections vanish by symmetry, and fresh blocks retain the previous solution set. None supplies an independent-sum representation of the centered hitting time.

## Operational endpoint

Only the five assigned files were written. No child agents, git commands, acceptance/count edits, shared indexes, publication, numerical scans, live-sibling reads, or full external body retention occurred. The initial read-only inventory and brief retrieval started in the parent workspace before the project-cwd instruction was applied; it read no other project bodies. Every subsequent command used openai-proof-research. There was no external second-agent review or formalization.

Final mathematical status: validated I343 Lindeberg; paid redundant/cooperative two-root moment separation; exact posterior covariance and bounded-kernel concentration targets; no predictable-variation concentration and no SAT CLT. Stop at this finite endpoint rather than promoting a conditional implication or a finite deterministic gadget into the requested theorem.
