# Unconditional source refutation — checked implementation

Solo lane; credit 0, campaign accepted7/total37 unchanged. No paper, novelty
assessment, independent review, acceptance or shared index/ledger changes.

Starting packet SHA256 74e2c9ead42007930c623531d4ee290865cf41d245f520ca7bff8270a9fd2f74.
All inherited manifest entries checked. Source, Boundary, Gadget, Edges and Degrees
remain byte-identical. Five new modules extend them:

- Local: degree_b, degree_c, degree_d, degree_x, degree_y identify genuine retained
  degrees with db,dc,dd,dx,dy of mask S i for arbitrary deletion S. Uses the inherited
  retained-neighbor theorem; no original-degree substitution.
- Lower: valid_diamond and valid_xy follow from arbitrary Valid(graph t) S.
  block_cost equates index deletion count with diamondCost+pathCost; deleted_card_sum
  uses injective/surjective actual edge indexing to sum exactly. The kernel certifies
  the finite cost identity. deletion_card_lower holds for all t, including zero.
- Charges: chargedEdges are actual unordered edges in S. actual_diamond_cost and
  actual_path_cost identify their cardinalities with the two costs. charged_subset,
  charged_blocks_disjoint, charged_parts_disjoint and actual_deleted_sum certify
  disjoint block/part charges and the exact global sum.
- Transport: moveSet preserves deletion cardinality. retainedIso preserves the actual
  retained graph and hence actual degree; valid_move transports Valid in either
  direction using the inverse isomorphism; minimum_iso preserves attained minimum.
  finIso takes graph t to Fin(Fintype.card(Vertex t)); fin_connected, fin_edge_card
  and fin_minimum_lower supply the literal source graph model.
- Refutation: choose natural t>3c using the real Archimedean property. The inequality
  3t≤minimum and edge count8t contradict minimum≤8t/3+c. No upper witness is used.

Actual checked declarations (namespace EdgeIrregulator):

```lean
deletion_card_lower (t : ℕ) (S : Finset (Sym2 (Vertex t)))
  (h : Valid (graph t) S) : 3*t ≤ S.card
minimum_lower (t : ℕ) : 3*t ≤ minimum (graph t)
minimum_iso {V W : Type} [Fintype V] [Fintype W]
  {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) : minimum G = minimum H
minimum_source_refutation : ¬ MinimumSourceClaim
source_refutation : ¬ SourceClaim
```

These endpoints have no hidden local-certificate, gadget, transport or arbitrary-subset
premise. SourceClaim is the inherited literal ∃c:ℝ,1≤c∧∀ n G:SimpleGraph(Fin n),
G.Connected→∃S,Valid G S∧(S.card:ℝ)≤(G.edgeFinset.card:ℝ)/3+c.

The exact equality minimum(graph t)=3t for t≥2 is intentionally left to root's
combination with the separate upper-witness lane. It is not needed by either negation.
There are no residual proof obligations for the assigned source-negation endpoints.

OriginAudit enumerates all136 declarations from the actual ten module origins,
including private/generated, crosschecks moduleData membership, prints full types,
transitive axioms and safety flags. AuditPrint also checks and prints axioms for every
name. All flags unsafe/partial/axiom are false; axiom union is exactly propext,
Classical.choice, Quot.sound. No proof holes, added axioms, unsafe or native_decide.
Pinned Lean4.34.1 and all9 package pins retained; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

The deterministic packet contains sources, pins, dependency hashes, audit/replay code,
frozen inputs and failure evidence, no prebuilt own oleans. Fresh extracted replay
checks all pins and1132 imported package olean hashes, rebuilds all ten proof modules
and both audits serially, and records all136 types and axiom closures. See
verification-fresh/replay-receipt.json for authoritative replay status and resources.
See FAILURES.md for failures and the early receipt-overwrite limitation.
