| Source obligation | Formal statement | r5 status |
|---|---|---|
| Cubic edge-rooted acyclic patterns with exact depth 2 | `TreeFamily T 3 2` | Inherited source-literal definition |
| Every such finite tree has a canonical rooted model | `TreeModelsR3.ClassifiedCubicTrees` | Proved by `TreeModelsR5.classification`, with precisely r3's quantification over `W : Type` and `[Fintype W]` |
| Root branches and their children exhaust the vertex set | `Branches.coverage` | Proved for arbitrary universe |
| Distinct blocks enumerate the graph bijectively | `slotValue_bijective`, `vertexEquiv` | Proved, with leaf counts at most 2 |
| Canonical adjacency, including no extra target edges | `forward_slots`, `reflects_adjacency`, `modelIso` | Proved; the bridge argument replaces edge counting |
| Two distinguished roots preserve their order | `vertexEquiv_left`, `vertexEquiv_right` | Proved |
| Canonical weighted bound for all 81 count tuples | `TreeModelsR3.all_81` | Inherited proved theorem |
| Uniform maximum-independent-set expectations transport under rooted isomorphism | `TreeModelsR3.bound_of_iso` and its inherited dependencies | Inherited proved bridge, now applied to every finite tree |
| Negation of the convex-combination conjecture | `TreeModelsR5.refutation : ¬ EdgePattern.Conjecture2.{0}` | Unconditional theorem, via `neg_conjecture_of_classification classification` |

`Conjecture2` universally quantifies the permitted degrees and depths, arbitrary finite pattern vertex types, and proposed finite real convex combinations of tree constraints. The inherited counterexample fixes d = 3 and r = 2, which suffices to negate that universal proposition. The positive-weight implication and uniform averaging over maximum (not maximal) independent sets are unchanged from the inherited definitions and bridge.

The precise requested endpoint is universe zero. It quantifies over all finite vertex types in `Type`, with no fixed vertex bound imposed by its statement. Every ordinary finite graph is representable there. Structural helpers, coordinates and the model isomorphism are universe-generic; the r3 classification predicate and inherited refutation bridge are stated at universe zero. No all-universe refutation or transport along ULift is claimed.

The primary-source reference, bounded prior-art evidence and its access limitations are the immutable inherited `PRIOR-ART.md` and `EDGE-PROOF.md`. Those historical records describe gaps at their respective dates; the r5 declarations and replay receipts supersede their formal-completion status only. Root remains responsible for independent source-fidelity, novelty, significance and acceptance assessment.

The manuscript source paper/manuscript.md, Section 6, adds the full definition-level correspondence table, and Section 7 gives the canonical-to-tree homomorphism / bridge reflection / numbering architecture. The shallower-tree robustness is ordinary mathematics only.
