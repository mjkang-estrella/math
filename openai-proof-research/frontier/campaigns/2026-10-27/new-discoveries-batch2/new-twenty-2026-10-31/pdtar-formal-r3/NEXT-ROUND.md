# Exact residual work

Only the following two unchanged Props remain as hypotheses of the partial endpoint. Their definitions are in PDTAR/SmallObligations.lean; they are neither axioms nor assertions of truth.

```lean
def StarRigidityRemaining : Prop := ∀ t : ℕ, 3 ≤ t →
  (∀ H : SimpleGraph (Fin 1 ⊕ Fin t), NoIsolated H →
    SamePD (completeBipartiteGraph (Fin 1) (Fin t)) H →
    Nonempty (H ≃g completeBipartiteGraph (Fin 1) (Fin t))) ∧
  (∀ H : SimpleGraph (Fin t ⊕ Fin 1), NoIsolated H →
    SamePD (completeBipartiteGraph (Fin t) (Fin 1)) H →
    Nonempty (H ≃g completeBipartiteGraph (Fin t) (Fin 1)))

def ThreeThreeRigidityRemaining : Prop :=
  ∀ H : SimpleGraph (Fin 3 ⊕ Fin 3), NoIsolated H →
    SamePD (completeBipartiteGraph (Fin 3) (Fin 3)) H →
    Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3))
```

The immediate star obstacle is that the existing pair_fort lemma assumes both parts have size at least 2. Its proof can be specialized in a new module to the leaf side with a nonempty singleton opposite part: fort_meets_side_twice already needs only nonemptiness of that opposite part. This gives a fort whose closed neighbourhood is the centre plus any chosen leaf pair. It remains to show that such a fort cannot contain the unique PD singleton (the centre), and then deduce that the fort is the entire leaf pair. One possible route splits a fort supported on three vertices into a pair and a triple. A pair fort has identical neighbours outside the pair; its transposition is a graph automorphism, so inclusion of the centre would yield a second PD singleton. If the fort contains all three supported vertices, its closed neighbourhood is itself, a proper component; a centre singleton cannot power dominate outside it. These observations still require Lean proofs, including construction of the transposition automorphism and transport of PD. Once the pair forts are identified, their closed neighbourhoods force all star edges and exclude internal leaf edges. Both orientations still need transport. No claim that these proposed lemmas have been formalized is made.

For (3,3), the existing hub lemmas resolve much of the single-cross-neighbour structure but do not yet construct the relabelled complete bipartition. Complete that branch using cross_nonempty at the four non-hub vertices and the second hub application. For the other branch, the source's six-vertex argument remains to be formalized. First show every 2-set PD and every singleton non-PD from SamePD and the existing KstFamily lemmas. Then derive degree exactly 3: degree at least 4 leaves at most one unobserved vertex, handled by small_step_of_one_missing; degree at most 2 at a neighbour makes the observed closed neighbourhood of that pair reachable from a singleton. Finally exclude triangles via the cubic six-vertex structure and build the bipartition. No decide over all six-vertex graphs is allowed or needed.

After these two proofs, import them into a NEW revision of Final (Final is new in r3, unlike inherited packet modules), replace the conditional assembly by the requested unconditional theorem, print its axioms, and repeat a fresh extracted build, checker and full closure audit. Root independently reviews and decides acceptance. The witness construction no longer needs work: twoWitnessRemaining is proved for the full positive-integer scope, including t=1 and swapped orientation.
