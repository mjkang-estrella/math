# MathDB frontier research

This phase responds to the user's correction: the objective is a genuinely new idea toward a significant named open problem, not another routine consequence of an accepted OpenAI theorem. The earlier F001–F010 remain archived deductions; they do not meet this phase's research target.

## Acceptance standard

1. Identify the exact MathDB problem and its remaining scope after accepting **all** the pinned OpenAI results.
2. Explain why the proposed result would matter for that problem. Cite an observed ranking or featured designation; never invent a score.
3. Identify a substantive new bridge: a construction, estimate, or structural lemma not already contained in a source or obtained by a standard transfer.
4. Try to prove the bridge and attack its vulnerable step with independent review, counterexamples, and appropriate exact or numerical checks.
5. Keep proved statements, conjectures, conditional reductions, and failed approaches visibly distinct. A reduced problem is not a solved problem. A computation is not a general proof.
6. Give each substantive validated finding its own commit. Do not inflate the finding count with equivalent formulations or routine corollaries.

## MathDB interpretation

The [database](https://mathdb.com/database) exposes Trending, Newest, Featured, and Likes. The [news archive](https://mathdb.com/news) exposes a Significance ordering. Indexed snapshots describe significance as a 0–100 estimate of **the impact of a reported development**, not proof certainty. These are not verified numerical rankings of every open problem.

For example, the indexed [Schubert-varieties homepage snapshot](https://mathdb.com/?tag=schubert-varieties) reports 97/100 for a forced Navier–Stokes announcement, 84/100 for a cscK Yau–Tian–Donaldson counterexample claim, 79/100 for a Pierce–Birkhoff counterexample claim, 76/100 for a bicentralizer/classification claim, and 75/100 for an Arnold–Givental claim. The snapshot was indexed three weeks before retrieval on 2026-10-08; these are historical news scores, not current scores for our proposed work.

The current homepage features Hodge, BSD, Riemann, Yang–Mills, P versus NP, Navier–Stokes, and the solved Poincaré conjecture. Featuring and numerical news significance must not be conflated. Browser access hit a Cloudflare verification page; readable search-index copies remain available. No submissions or claims have been posted to MathDB.

## Current work

**Research resumed at the user’s explicit request to iterate until the desired output is obtained.** [Iteration 02](iterations/README.md) is active. The [first-pass outcome](OUTCOME.md) records the previous unsuccessful search and remains historical. No high-significance named problem has been solved in this phase. The working reports belong in `scouts/`; their claims are provisional until reviewed and integrated. The immutable source revision is recorded in [../sources/upstream.json](../sources/upstream.json).

- **Arithmetic:** the [second round](reviews/arithmetic-bridge-r2.md) proves that one proposed four-cycle is harmless and that the naive global unweighted operator norm fails. The full high-trace and cubic-centering estimates remain missing. This route is parked pending a genuinely new joint estimate; it is not being counted as a Chowla result.
- **Discrete:** the [scout](scouts/discrete.md) found obstructions to union-preserving coding and graph balancing. The [direct-noise round](reviews/frankl-direct-r2.md) produced no Frankl advance and is parked. Parent review corrected its overclaim of general falsification and its vacuous endpoint-supremum candidate. Both finite experiment outputs were reproduced exactly; floating-point evidence is not proof.
- **Analysis:** the [simple-eigenvalue hot-spots extension](scouts/analysis.md) survived [mathematical review](reviews/hotspots-review-r2.md) after repairs, but was **demoted for lack of a novel mechanism**. The subsequent [polygon candidate](reviews/hotspots-multiplicity-r2.md), covering repeated eigenvalues, has also been **demoted on significance and novelty grounds** by the [round-3 review](reviews/hotspots-polygon-novelty-r3.md): the smooth mechanism and polarization are already published, leaving only a short corner extension of unconfirmed priority. Both that reviewer and the [dedicated proof reviewer](reviews/hotspots-polygon-proof-r3.md) accepted the mathematics after analytic clarifications. The parent reproduced the exact checks and recorded the result as [technical finding R003](findings/R003-polygon-eigenline-selection.md). General Lipschitz eigenline selection remains open. Neither result fulfills the user's research objective.
- **Algebraic geometry:** the [K3 audit](reviews/geometry-k3-review-r2.md) accepts the corrected arithmetic comparison but gives a CM counterexample to its interpretation as the full known Hodge region; Lemma C is Varesco 2023. The [Mumford audit](reviews/geometry-mumford-review-r2.md) validates a repaired reduction but finds exact prior art. Neither establishes new substantive Hodge progress. The parent reproduced both independent audits and source hashes. The [construction round](reviews/geometry-mumford-bridge-r2.md) found no cycles. It proposes a split-sixfold partner and a conditional linking-class reduction; the [final audit](reviews/geometry-partner-review-r3.md) accepts a repaired classical construction and conditional reduction, with novelty unverified. The algebraic link remains unconstructed. No major new theorem is claimed.

## Technical findings within the incomplete arithmetic approach

These are project-level proof-method findings, **not substitutes for the requested novel resolution or substantial new case of an important conjecture**. No literature-priority claim is made.

| Record | What was established | Separate commit |
|---|---|---|
| [R001](findings/R001-divisor-parallelogram-bound.md) | A restricted normalized four-cycle family has negligible total absolute weight, even with arbitrary bounded midpoint factors. | `ed50d45` |
| [R002](findings/R002-unweighted-kernel-obstruction.md) | Rare large entries defeat the proposed norm bound for the explicitly undeleted, unweighted kernel. | `609a94c` |

The parent checked both proofs against the actual source kernel and reran the exact-arithmetic diagnostics. They do not provide the missing longer-walk or centering bounds.

## Verified polygon technical note

[R003 — Polygonal Neumann eigenline selection](findings/R003-polygon-eigenline-selection.md) records the corner exclusion and its selection consequence, with conditional strict hot spots under family 369. Two independent reviews accepted the mathematics; the novelty review judged it a modest extension of a known mechanism. It is preserved as one separate finding, not counted as fulfillment of the requested high-significance advance.

## Validated bounded-index arithmetic consequence

[R004 — Simultaneous bounded residual index](findings/R004-simultaneous-bounded-index.md) combines two accepted corpus inputs to put every base in a fixed finite set at bounded index for a positive proportion of primes. The corrected theorem and prime-average corollary pass independent proof review; parent finite checks and source hashes reproduce. The literature screen found no exact duplicate, but a nonroutine new mechanism and priority remain unproved. The frontier objective stays open. The [progression round](iterations/i03-arithmetic-progressions.md) has returned a candidate proof of that reservoir and positive-lower-density primitive roots. Independent analytic review is running; those stronger claims are not yet accepted.

## Closed operator candidate

[R005 — Explicit reflection half-spaces](findings/R005-operator-reflection-obstruction.md) rules out every operator T_a=S+M_aV in the proposed commuting family as an ordinary-ISP counterexample. Independent audit and parent reproduction pass; the two explicit invariant half-spaces have dense nonclosed sum. This is a candidate obstruction, not a significant new ISP theorem. The next round investigates a specified asymmetric coupling, whose ordinary invariant subspaces remain unresolved.
