# Statement correspondence

Sources are cached read-only inputs from expanded-corpus-r133 and stacksort-review-r1. No new novelty investigation or live prior-art clearance was performed in this implementation lane.

Defant–Propp, arXiv:2002.07144v4, §2.3: “Then s(π) = s(L)s(R)m.” `s_split` proves this literally, for m greater than the left entries and at least the right entries. On permutation words all entries are distinct. `s [] = []` holds definitionally. The source example 416352 ↦ 143256 is kernel checked. Zero-based labelling is transported by `s_map_orderEmbedding`.

Definition 1.1 defines the degree as the average of |f⁻¹(f(x))| over the full domain. `deg` is P/n!; `deg_eq_average`, `words_card`, and `fibre_square_identity` give exactly that average and the sum of squared fibres. `P` is the literal filtered cardinality of the Cartesian square of ALL permutation words. `s_mem_words` supplies the self-map bridge.

Conjecture 4.4 says the limiting nth root lies in (1.68,1.73). `Conj` is the literal existential assertion of convergence to an L in that open interval. `mathdb_345545` negates it, conditional on the two explicitly displayed open propositions. `limit_ge` states every such limit is at least 1.73. `nonvacuity` states the roots exceed 1.73 frequently; `subsequence_companion` supplies the explicit index 131·2^k−1. The real expression at n=0 uses Lean's totalized division; it has no effect on atTop limits.

Version correction: the numbered conjecture occurs in v3/v4 and as Conjecture 23 in EJC 27(3), P3.51. v1/v2 instead contain an unnumbered (1.6,1.8) remark. No claim about a numbered conjecture in v1/v2 is made here.

The cached MathDB 345545 record says “maximum fiber size”, while the primary source uses average multiplicity. `maxFib` is the maximum fibre over outputs actually achieved by the map. This equals the maximum over the whole finite codomain: an unachieved output has fibre zero, and every positive fibre is achieved. `ConjMax` uses this maximum. Its negation `mathdb_345545_max` and companion `max_companion` are unconditional; the latter holds for EVERY n≥5. Credit cannot rest on this paraphrase reading.

The source-reading limit is not proved to exist in this packet. The non-vacuity companion is included precisely to prevent an inference based solely on possible nonexistence. No heuristic estimate of 1.95 is used in a Lean proof.
