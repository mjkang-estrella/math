# A five-vertex obstruction to the sink-edge conjecture

2026-11-14. Target: MathDB 382130, bound by inherited independently passed target review to Conjecture 1 of Petter Restadh, *Diameters of the Characteristic Imset Polytopes*, arXiv:2302.03647v2 (6 March 2023), page 11. This paper addresses that owned version only. Independent scope/registry acceptance and extracted replay are separate.

## Statement and definitions

For an arbitrary finite vertex set [n], let G be a simple skeleton and H an acyclic orientation. For every subset S of size at least two, c_H(S) is one if some v in S satisfies S⊆pa_H(v)∪{v}, and zero otherwise. CIM_G is the real convex hull of the imsets of **all** acyclic orientations of G. Making i a sink directs every incident edge towards i and preserves all other arrows. The source conjecture says that, whenever H and its sink modification are not Markov equivalent, their imset segment is an edge of CIM_G. An edge means a face of affine dimension one.

The Lean predicate `UniversalSinkEdge` quantifies over arbitrary n, simple G, arbitrary Boolean arrows H with no nonempty directed cycle, and i. Its hull `SourceCIM` uses all relationally acyclic arrows with that skeleton. Its theorem `source_negation` proves the negation. `explicit_five_counterexample` gives the witness.

## Certificate

Take E={12,13,14,15,24,25,34,35}. Source labels 1,...,5 correspond to Fin 5 by k↦k−1, with checked inverse k↦k+1. In vertex order 1,...,5 the four parent lists and topological orders are:

| DAG | Parents, in vertex order | Topological order |
|---|---|---|
| C | (2345,∅,4,2,23) | 2,4,3,5,1 |
| D | (235,∅,∅,123,23) | 2,3,5,1,4 |
| A | (234,4,4,∅,123) | 4,2,3,1,5 |
| B | (2345,∅,∅,23,23) | 2,3,4,5,1 |

Every arrow points forward in its listed order; all skeletons are E. Making vertex 4 a sink in C reverses 4→1 and 4→3 and retains 2→4, giving D exactly. Kernel-checked source-label arrow lists, parents and ranks are in the appendix.

C and D encode different conditional independences. C has the unconditioned open path 2→4→3. In D, both 2 and 3 have no incoming arrows. A collider-free path starting at 2 must start forward; induction over its consecutive edges forces every edge forward, since a forward edge followed by a backward edge makes a collider. It cannot finish at source 3. Thus 2 and 3 are d-separated given the empty set in D and are not so separated in C. The Lean definitions include simple paths, collider activation by a conditioned descendant (including the collider itself), noncollider blocking, and disjoint-set separation. The singleton reduction is proved. No equivalence between imset equality and Markov equivalence is assumed.

The 26 coordinates partition as follows:

R={12,13,14,15,24,25,34,35,123,124,125,134,135,235,1234,1235};
F={145,1245,1345,12345}; Q={234}; Z={23,45,245,345,2345}.

The supports of (c_C,c_D,c_A,c_B) are respectively (R∪F,R∪Q,R,R∪F∪Q). The parent-set formula, partition, and table, including all zero coordinates, are proved by kernel reduction. Consequently c_C+c_D=c_A+c_B. In any expression a c_C+b c_D=c_A with a,b≥0 and a+b=1, coordinate 234 forces b=0 while coordinate 145 forces a=0. Hence c_A is outside the segment.

## Convex obstruction and conclusion

If a,b belong to a real convex set P, a+b=c+d, and a lies outside [c,d], then [c,d] cannot be a face of P. Its midpoint is also (a+b)/2. The defining face property, applied with strict coefficient 1/2, would force a into the segment. This proves nonface directly; no assumption that faces are exposed is needed. An edge is a face whose vector span of differences has real dimension one, so nonface implies nonedge.

All four imsets are generators of the actual SourceCIM_E. Apply this lemma with a=c_A,b=c_B,c=c_C,d=c_D. The resulting nonedge, exact sink identity, and d-separation difference refute the universally quantified source conjecture. Nothing here refutes the proposed linear diameter bound, or establishes vertex-number minimality.

## Formal and source limits

The appendix is literal and deterministically extractable; its six modules and production oleans have recorded hashes. Specific pinned mathlib imports support real convex hulls, segments, finite sets and affine dimension. No source theorem is an assumed Lean axiom. Only propext, Classical.choice and Quot.sound occur in endpoint dependencies. The inherited source and target reviews are not this implementation's new independent reviews. Journal-final fidelity, novelty, scope/registry acceptance, independent statement review and independent extracted replay are not established here. Credit is zero.
