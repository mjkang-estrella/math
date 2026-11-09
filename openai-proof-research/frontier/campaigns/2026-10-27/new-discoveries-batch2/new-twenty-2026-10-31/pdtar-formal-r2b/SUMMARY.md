# PD-TAR reduction — r2b handback

The reduction is closed, with no additional hypotheses:

```lean
PDTAR.reductionRemaining : PDTAR.ReductionRemaining
```

This is only the published reduction needed by MathDB 353203. It does not prove the Core remainder or the small-case obligations assigned to r2a, and it does not close the full MathDB endpoint. No acceptance or discovery credit is claimed. Root decides.

The six round-1 modules are byte-identical to the supplied source archive with SHA-256 `39ebb60a1e30c558cc2a978dc423a27d3969006bbf21904a788f97a17b4b9b69`. All new mathematical work is in seven `PDTAR/Reduction*.lean` modules; importing `PDTAR.ReductionProof` supplies the theorem. There are no dependencies on the sibling lane.

## Complete replacement proof

The survey chain was read, including the full proofs of `interval`, `lem:ord_pres`, `t:irrel-isom`, `isomorph-isometry-u` and `isomorph-same-zfs`, their degree and cube preliminaries, and the review's gate B. The formal proof uses the brief's permitted self-contained replacement route, avoiding induced-cube interval classification.

1. Every TAR neighbour of S is uniquely S symmetric-difference {v}. `reduction_neighbor_equiv` identifies neighbours with coordinates whose toggle is PD. Consequently their number is at most the base order. At the full set all toggles are PD by the frozen `erase_isPD`. A TAR isomorphism gives bijections of neighbour subtypes, so the two base orders agree. The empty vertex type is included.
2. The co-singletons are distinct neighbours of the full set. Their images are obtained from the image A of the full set by toggling distinct coordinates. Equal base orders make these coordinates a bijection e of vertex types. This is `reduction_basis`.
3. Any two PD sets S,T have a TAR walk of Hamming length: add vertices to reach their union, then reverse a monotone walk from T to the union. The monotone walk is proved by strong induction on the number of missing vertices; PD up-closure guarantees every intermediate vertex. The symmetric-difference triangle inequality bounds every TAR walk below by its endpoint Hamming distance. Map the constructed walks along the isomorphism and its inverse to obtain equality of all endpoint Hamming distances. Thus `ReductionHammingRemaining`, introduced as a specification in ReductionMetric, is fully discharged by `reductionHammingRemaining` in ReductionPaths. It is not a remaining assumption.
4. The Hamming distances to the full set and each co-singleton determine membership of each coordinate. Toggling a coordinate decreases Hamming weight exactly when the coordinate is present. Applying this test before and after the TAR isomorphism gives its full affine description: phi(S) = e(S) symmetric-difference R, where R = A symmetric-difference univ. This proves `reduction_affine_of_hamming`. Surjectivity yields the corresponding iff on all finite subsets, not merely the forward implication on PD sets.
5. A flip mapping one up-closed family onto another can be removed from the family equivalence. If P(S) iff Q(S symmetric-difference R), then P(S) implies P(S union R), hence Q(S minus R), hence Q(S). The converse uses the same argument starting in Q. `reduction_flip_normalize` proves this for arbitrary upward families. Applying it after the coordinate bijection yields equality of the relabelled PD families.
6. Pull H's adjacency back along the inverse coordinate bijection. `reduction_closed_transport`, `reduction_step_transport`, `reduction_propagate_transport`, and `reduction_obs_transport` prove exact transport of the literal simultaneous rounds. Hence PD transports in both directions. The pullback graph has an explicit graph isomorphism from H and has exactly G's PD family. `reductionRemaining` assembles these proved bridges.

`reduction_common_neighbors` separately proves the direct two-common-neighbour calculation for a cube face using symmetric differences. It is not needed by the replacement proof. No induced-interval, minimal-set, rank-preservation, or irrelevant-set theorem is assumed.

## Correction to the task wording

The claim that degree equals the base order **exactly at** the full set is false. For K3, whose PD sets are all nonempty subsets, every 2-set also has degree 3 in its TAR graph. The valid statement, proved here, is that every degree is at most the base order and the full set attains the bound. The frozen definitions require no change.

## Validation and limits

See results.json for the completed extracted serial rebuild, leanchecker results, every-declaration audit, hashes, line counts, and resource receipts. The audit includes generated declarations, unsafe/partial flags, `_unsafe_rec`, `implemented_by`, `extern`, and transitive axiom sets; only propext, Classical.choice and Quot.sound are allowed. Expected-failure controls test an excessive degree claim and a false cube-toggle equality. Full development failure logs are preserved separately from successful extracted replay logs.

The process RSS cap is sampled every 50 ms; unsampled transients are not ruled out. Each expensive child has affinity to at most two available CPUs, CPU 120 seconds, wall 140 seconds, sampled RSS 6 GiB, and MALLOC_ARENA_MAX=2. Lean uses -j1 -M3500, warnings as errors, and asynchronous elaboration disabled. The mathlib cache is read-only. No child agents, git operations, ledger edits, uploads, messages, browser tabs, downloads, or background jobs are part of this handback.

Next step for root: independently review the replacement proof and statement fidelity, combine the module import with r2a's work, then perform the full endpoint replay. No further reduction sub-lemma remains open in this lane.
