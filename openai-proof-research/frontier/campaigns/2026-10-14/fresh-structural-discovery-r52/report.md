# r52: full directed-cycle target unresolved

**No nominee; no campaign count change.** The unchanged full r33 question asks for an absolute linear bound on the number of directed simple cycles partitioning every finite simple balanced digraph, with antiparallel arcs allowed. No restriction or weakened substitute is adopted.

The new positive interface is an integral bounded-load correction for small imbalance. If a simple n-vertex directed h-expander has zero-sum integer demand b with |b(v)|<=k<=h, a fractional flow of arc capacity k/h can be rounded using vertex splitting to an actual arc subset F with divergence b, out-degree at most ceil(kn/h), and in-degree at most ceil(kn/h)+k. Deleting F loses at most that latter quantity in cut expansion. This is elementary max-flow and integrality support, not an independent contribution claim.

Applied to the actual source181 polynomial scale, it gives balanced edge-expander splitting and small sampled Eulerian reservoirs with balanced global complements. The sampled-reservoir argument must use tau=D^.77: the source's printed .74 is insufficient for this correction estimate, but the source proof's strict exponent inequalities permit .77. The complete derivation and dependency distinction are in balanced-reserves.md.

The global proof is still missing. The source box split needs a small undirected boundary, whereas directed two-sided vertex expansion only yields a small one-sided boundary after long-cycle removal. Equality of cut arc counts does not bound the opposite boundary's support. Even after balanced reservoirs are available, the source's linear undirected simple-path partition does not supply a linear directed path partition. These debts are explicit in directed-box-interface.md; they are not hidden inside a transfer assertion.

The initial source118 quantitative-tree investigation produced two scoped route obstructions, preserved in tree-route-obstructions.md: contiguous spider phases with a singleton survival guarantee have exponential cost in their incoming-root count, and the actual packing's unequal-label bins can recycle globally using one extra bin. Neither statement disproves efficient competing trees, a stronger additive packing gap, or a different isolation construction. No tree target was frozen.

Finite checks inspect 4,096 four-vertex digraphs, validate 574 admissible self-imbalance repairs including456 nonzero cases, test32 seeded dense repairs and825 exact spider schedules, and check the exponent arithmetic exactly. They are diagnostics, not proof of the full target. The packet verifier binds exact files/directories and source identities to a caller-supplied anchor; it does not certify mathematical validity or novelty.

Parent assistance checked the flow algebra and the .77 sampling substitutions and supplied an overlapping bounded Patel–Yıldız comparison. It is author assistance, not independent review. No acceptance gate was requested or passed for this unresolved packet.
