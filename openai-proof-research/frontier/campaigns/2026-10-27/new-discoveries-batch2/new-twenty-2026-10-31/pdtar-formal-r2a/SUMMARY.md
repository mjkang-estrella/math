# MathDB 353203 — partial round 2a

No acceptance or credit is claimed. Root decides. The entire Core remainder is proved; the full MathDB endpoint is still conditional because three small-case obligations remain open.

`PDTAR.coreRemaining : CoreRemaining` is unconditional. Its proof covers arbitrary finite ordered partitions A and B, all sizes at least 3 except (3,3), and requires only SamePD; no reduction or no-isolation hypothesis is assumed. The new modules prove no isolated vertices, cross nonemptiness, no cross leaf, all three steps of the single-cross-neighbour hub argument, the exceptional-size conclusion, two cross neighbours outside (3,3), completeness with the larger side second, the swapped case, and independence of both parts. This closes every Core item in the binding brief.

`PDTAR.edgeRemaining_of_reduction (hR : ReductionRemaining) : EdgeRemaining` is proved. The proof transports no-isolation through the graph isomorphism supplied by hR, and proves directly that any simple graph without isolated vertices on Fin 1 ⊕ Fin 1 is the edge. No nonempty assumption on the arbitrary comparison vertex type is introduced.

Also proved: equal labelled PD families induce a TAR isomorphism by the identity on finsets, the sum partition and no-isolation bridges, and the full positive-integer endpoint conditional on exactly the three residual Props and hR.

The final module `PDTAR/CoreSmallProof.lean` has six declarations. Two have the requested completed names and signatures. The other four use explicit `_conditional` suffixes and additional Prop hypotheses under the brief's incomplete-round fallback. It does NOT declare unconditional `twoRemaining`, `starsRemaining_of_reduction`, `threeThreeRemaining_of_reduction`, or `mathdb_353203_of_reduction`. No placeholder theorem with one of these names is asserted.

The exact residual definitions are in `PDTAR/SmallObligations.lean`:

* `StarRigidityRemaining`: on each of the two sum-type orientations of a star with at least 3 leaves, a graph without isolated vertices with the same labelled PD family is isomorphic to the star.
* `ThreeThreeRigidityRemaining`: the analogous labelled-family rigidity assertion on Fin 3 ⊕ Fin 3.
* `TwoWitnessRemaining`: at positive s,t with a part of size 2, construct a graph on the same vertex type without isolated vertices, with the same labelled PD family, and no base-graph isomorphism to K(s,t).

These are definitions of Props, not axioms or proved assertions. Their exact quantifiers and conclusions are in Lean. The small cases have not been closed by a finite scan or by importing published statements. ReductionRemaining is never discharged in this lane and appears only as an explicit theorem hypothesis.

All six frozen files were extracted from the archive with the required SHA256, and their before/after hashes agree byte for byte. No new Reduction module is created. All new mathematical modules have names CoreProof*, Small*, or the required CoreSmallProof. No sibling lane is imported or modified.

Validation results are recorded in `results.json`. The source-only archive contains all six frozen modules, ten new modules, validation scripts and its manifest. The replay uses a fresh extraction, strict serial Lean 4.34.1 compilation with asynchronous elaboration disabled, leanchecker on every module, and a full local-declaration audit including generated declarations. Only propext, Classical.choice and Quot.sound may occur in transitive axioms. The negative controls test empty fort, empty PD set for K(2,3), and dropping the (3,3) exclusion from the cross-degree theorem. The last is an interface rejection, not a formal counterexample construction.

All replay logs are retained in full. Process limitation: the initial development helper reused per-module log names, so failed development logs were overwritten by corrected successful passes. Those failed diagnostics were visible in the session but are not preserved as full artifact logs. Replay logs are complete and immutable under the resumable driver's hash checks; the development helper now gives each run a unique name. This historical logging gap is reported rather than reconstructed.

No git operations, shared ledger edits, child agents, network requests, uploads, external messages or browser tabs were used. One heavy process ran at a time. Resource receipts record the enforced 2 CPU affinity, 120 s CPU and 140 s wall caps, 6 GiB sampled process RSS cap, MALLOC_ARENA_MAX=2, and lane-local temporary/cache paths.

Next-round plan:

1. Prove a PD-family characterization for K(2,t) and K(2,t) plus its internal 2-side edge: a set meets the 2-side, or contains at least t−1 vertices of the other side. Prove the positive direction by at most two propagation steps and the negative direction with a fort comprising two unchosen opposite-side vertices. At t=2 check the singleton cases directly. Construct the witnesses of TwoWitnessRemaining, prove edge-count non-isomorphism, transport the swapped orientation, and handle P3 versus K3 for (1,2) and (2,1). The identity-induced TAR isomorphism is already proved.
2. For stars, prove the source's connected upper-PD characterization with an explicit minimal set of size n−2 on the transported graph. Alternatively derive the same rigidity directly from the labelled star family, whose centre singleton is PD and whose leaf-only PD sets have size at least t−1. Keep both orientations in StarRigidityRemaining until the swap transport is formalized.
3. For K(3,3), split on a cross neighbourhood of size 1. The completed hub steps already give the internal two-star structure; use cross_nonempty and the hub lemma again at a leaf to force all four cross edges between the remaining pairs, then explicitly relabel the bipartition. For the all-cross-degree-at-least-2 branch, formalize the source's structural six-vertex degree and triangle argument without enumeration of all graphs.
4. Replace only the four conditional declarations after their Props have proofs. Combine with sibling r2b's reductionRemaining in root's assembly module; keep that proof outside this lane. Repeat the strict fresh extraction and declaration audit before independent review. No acceptance is requested from this lane itself.

Replay history: `replay-attempt1/extracted` preserves the first full compile/check/audit run. Its final negative control was correctly rejected by Lean with “Application type mismatch”, which the driver's narrower expected-error parser did not recognize. The negative fixture was changed to supply the incomplete theorem as a whole, producing “Type mismatch”; a new source archive and fresh complete replay were then used. No mathematical module changed between these two replays.

Final validation: fresh replay completed all 36 of 36 steps: 16 strict builds, 16 leanchecker runs, declaration audit of 177 local declarations with zero violations, and all three expected-failure controls. Peak sampled process RSS was 3518951424 bytes; maximum step wall time was 4.075 seconds. No resource cap was hit.
