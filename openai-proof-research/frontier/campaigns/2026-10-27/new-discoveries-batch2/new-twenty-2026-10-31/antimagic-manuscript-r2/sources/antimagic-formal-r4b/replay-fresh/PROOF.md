# Round 4B proof

Fix two inherited FullTree certificates S on G and T on H with the same natural parameters t,n. The proof uses their existing depth, child and unique_parent fields. It does not substitute a weaker structural predicate or require an extra graph-distance lemma. Their isTree fields remain part of the hypotheses, although the other fields already suffice for the uniqueness argument.

Let Layer S h be the subtype of vertices at depth h. If h < n, the child_count field gives cardinality t for each vertex's child subtype. Fintype.equivFin followed by finCongr chooses its t child slots. This choice need not be canonical.

The map descend from the dependent sum of depth-h parents and their children to Layer S (h+1) forgets the parent. It is injective: the child's positive depth makes it nonroot, so unique_parent identifies any two proposed parents. It is surjective: every depth-(h+1) vertex is nonroot and has its unique parent; child_depth places that parent at h. Composing the inverse descend equivalence with the chosen child slots gives step S h : Layer S (h+1) ≃ Layer S h × Fin t.

There is exactly one depth-zero vertex, the root. Hence the zero layers of S and T are equivalent. Recursively define the next layer equivalence as step S, the product of the previous layer equivalence and the identity on Fin t, and inverse step T. The lemma layers_parent records that this construction carries the parent coordinate to the previous layer equivalence.

Map a vertex v at depth h by the h-th layer equivalence. vertexMap_depth proves its image is still at h. Equal images therefore have equal depths, and injectivity of that layer equivalence proves equality of vertices. Conversely, the inverse layer equivalence at the depth of any target vertex supplies a preimage. This proves a bijection on the full vertex types.

step_parent_iff characterizes the child relation between successive layers as equality of the parent coordinate. layers_parent and injectivity of the previous layer equivalence therefore show vertexMap_child in BOTH directions. In the reverse direction child_depth on the target, together with vertexMap_depth, first proves that the source vertices are in successive layers. Finally adj_iff on both certificates turns preservation and reflection of child into preservation and reflection of adjacency. fullTreeIso packages the vertex equivalence and this relation equivalence into G ≃g H.

For the exact ModelBridge, obtain the model certificate from the frozen theorem modelStructure and apply fullTreeIso to S and that certificate. All typeclass binders, t >= 2 and n >= 1 hypotheses, and the Nonempty (G ≃g tree t n) conclusion are exactly the inherited ModelBridge definition. No parity assumption is needed for this structural theorem.

The final mathdb_354228 supplies this proven bridge to Round3.mathdb_354228. Its only remaining proof arguments are the three exact frozen construction Props. The inherited isomorphism-invariance theorems then transport the spectrum, leaf count and chiLA. This lane proves none of those construction Props.

Validation uses strict Lean compilation, leanchecker with an explicit module name for all 23 modules, and a full generated-declaration import-closure audit with allowOpaque=true. The audited set is computed to closure from every local declaration; missing dependencies cause failure. The report checks unique names, hashes, allowed axioms and local executable metadata. All checks run serially under the specified resource wrapper.
