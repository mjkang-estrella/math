# Proof

For any finite simple graph, private neighbours lie in the selected vertex's closed neighbourhood and outside the closed neighbourhood of every other selected vertex. Passing to a subset preserves private neighbours, so irredundance is hereditary. `IR` is the supremum of cardinalities over the finite family of irredundant subsets. The empty set makes the family nonempty. The supremum is attained, and bounds every irredundant cardinality. `IRSet` requires irredundance and equality with this maximum.

A source swap replaces u by adjacent v. Equal cardinalities force v to be absent from the erased set, and reversing the swap recovers the original set. A self-swap would either keep the erased vertex or require a loop in the source graph, both impossible. These proofs supply the simple graph structure directly on the literal swap relation.

The source `G9` has edges
03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58.

`Four.lean` lists all 126 four-subsets, proves this list equals `univ.powersetCard 4`, and proves via kernel reduction that each is non-irredundant. Heredity and existence of a four-element subset exclude every larger irredundant set.

`Three.lean` lists all 84 three-subsets, proves completeness, and checks irredundance iff membership in the nine-set walk. Each walk set has cardinality 3. Thus `ir_G9` gives IR(G9) = 3, and `isIRSet_iff` characterizes every IR-set.

The walk is
012 – 027 – 047 – 467 – 678 – 168 – 138 – 358 – 345.

`swap_walk_iff` checks all 81 ordered pairs, including the diagonal, using the literal source relation. Swaps occur exactly when indices differ by one. `toIR_bijective` gives the vertex equivalence, and `pathIso` gives the graph isomorphism. Applying the path half of Conjecture at n = 9 contradicts this witness.

The independent non-vacuity control uses K2 = pathGraph 2. Its maximum irredundant sets are precisely the two singletons; their source swap relation is exactly the unique edge, giving `controlIso` and `nonvacuity`.

Finite decisions use ordinary `decide`; their equality certificates are checked by Lean's kernel and replayed by leanchecker. No computational trust extension is used.
