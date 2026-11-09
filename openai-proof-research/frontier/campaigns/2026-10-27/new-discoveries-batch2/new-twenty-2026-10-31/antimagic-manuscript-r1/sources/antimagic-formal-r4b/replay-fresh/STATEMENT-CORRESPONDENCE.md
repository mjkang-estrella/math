# Round 4B statement correspondence

Source: Bača, Semaničová-Feňovčíková, Lai and Wang, arXiv:2204.04479v2, published Fundamenta Informaticae 185(2) (2022), Definitions 1.1–1.4 and Conjecture 6.1. The HTML calls the conjecture 6.0; the published numbering governs attribution.

- A finite complete full t-ary rooted tree, with common terminal depth n, is supplied as the unchanged `FullTree G t n`. Its fields explicitly give the root, depth-zero characterization, child relation, adjacency decomposition, increasing depth, unique parent, depth bound, exact child counts and tree property.
- `Round4B.modelBridge : ModelBridge` has every binder and hypothesis of the frozen bridge. Its conclusion is a literal SimpleGraph isomorphism from the arbitrary G to the unchanged `tree t n`, on the unchanged sigma row-index vertex type.
- No evenness hypothesis enters the bridge. The restrictions t >= 2 and n >= 1 are exactly inherited. The stronger fullTreeIso helper works for any t,n whenever both structural certificates exist.
- The final `Round4B.mathdb_354228` quantifies over every finite G with that certificate, t >= 2 even and n >= 1. Its conclusion is both IsLeast (spectrum G) (numLeaves G + 1) and chiLA G = numLeaves G + 1. The label definition uses edge equivalences into Fin |E| with +1 in weights, and leaves have graph degree one, exactly as inherited.
- The endpoint is conditional only on the three construction Props in namespace Round3. They are explicit theorem arguments, not axioms. No weakening of formula fidelity, parameter range or graph scope occurs.

This is a formalization progress packet. It does not establish novelty, close the construction lane, or assert acceptance.
