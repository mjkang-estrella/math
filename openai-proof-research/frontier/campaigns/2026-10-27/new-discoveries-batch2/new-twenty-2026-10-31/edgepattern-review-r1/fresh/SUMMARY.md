# MathDB 342414: r5 classification and refutation

The new endpoint is `EdgePattern.TreeModelsR5.refutation : ¬ EdgePattern.Conjecture2.{0}`. It applies `TreeModelsR3.neg_conjecture_of_classification` to the proved theorem `EdgePattern.TreeModelsR5.classification : EdgePattern.TreeModelsR3.ClassifiedCubicTrees`. This packet is submitted for root review, not self-accepted. No campaign counts have been changed.

The 268 inherited Lean source modules remain byte-identical. Six new modules complete the proof and replace audit tooling. All writes are confined to this lane. No git, child agents, shared ledger edits, publication, external messages, or prior-art gate repetition were used.

## Proof

Fix a rooted finite acyclic graph in `TreeFamily T 3 2`. Its roots each have two other neighbours. Choose and label these four branches, and let each branch's leaves be its neighbours other than its parent root. Each leaf set has cardinality at most two. The four cardinalities define the canonical `Counts`.

Acyclicity excludes all collisions among roots, branches and leaves. Sibling branches cannot share a leaf, by uniqueness of the intermediate vertex of a two-edge path. Cross branches cannot share a leaf, since their two roots and the root edge would give an alternative walk avoiding a bridge. Depth coverage shows every vertex occurs in one of these ten blocks.

`Slots` is the disjoint sum of the two roots, four branches and four leaf subtypes. `slotValue_bijective` proves this sum enumerates the original graph exactly. Enumerate each leaf set by `Fin card`. Nested `finSumFinEquiv` equivalences give `number : Slots T B ≃ Fin (order k)`. Thus `vertexEquiv` is an actual bijection from the canonical model to the original vertex type. The six clauses of `forward` preserve adjacency under this bijection.

For reverse adjacency, r5 replaces edge counting with a shorter general lemma, `reflects_adjacency`. If a connected graph maps injectively into an acyclic graph, any target edge between images belongs to the image of every source walk joining its endpoints, because every edge of an acyclic graph is a bridge. Injectivity of `Sym2.map` then identifies a source edge between the original endpoints. Hence the homomorphism reflects adjacency. This argument requires neither surjectivity nor finiteness. The canonical model is connected by `distance_eq`; the root edge joins the two possible finite-distance roots.

The resulting graph isomorphism preserves the two chosen root labels. Its inverse is exactly the `RootedIso T (pattern k)` required by r3's classification. Applying the inherited, fully proved classification-to-refutation bridge gives the unconditional endpoint.

## Module roles

- `StructureR5`: bridge-based cycle exclusion, adjacency reflection, connectivity, coverage and separation.
- `CoordinatesR5`: four branches, disjoint leaf sets and exhaustive coverage.
- `NumberingR5`: disjoint-sum coordinates, bijection, bounded counts and canonical numbering.
- `HomR5`: explicit number values and preservation of all six forward adjacency clauses.
- `EndpointR5`: connected canonical models, rooted graph isomorphisms, classification and refutation.
- `AuditR5`: fuel-bounded expression inventory and axiom/safety policy checks.

The proof import closure contains no `Audit*` module. `AuditR5` imports the endpoint and inventories local declarations, including generated helpers, with their module, complete expression DAGs for types and available opaque bodies, safety flags and transitive axioms. Its encoder is an explicit Nat.rec fold on natural-number fuel; fuel exhaustion is a hard failure. Inherited `Audit`, `AuditR2`, `AuditR3` and `AuditR4` are preserved as historical source tooling outside the proof import closure.

Both endpoint axiom reports list only `propext`, `Classical.choice` and `Quot.sound`. See replay receipts, audit findings and negative-control receipts for final validation status. Source fidelity and novelty evidence remain the inherited input records; r5 makes no new literature claim and does not repeat their gate.

The final auditor also passes a separate generated-declaration check: six declarations, all non-partial and non-unsafe. After this tooling-only adjustment, the final auditor is rebuilt and kernel-checked from a new empty extraction using the hash-identical proof modules from the full fresh replay. The endpoint proof closure itself did not change. The combined replay receipt records both stages.
