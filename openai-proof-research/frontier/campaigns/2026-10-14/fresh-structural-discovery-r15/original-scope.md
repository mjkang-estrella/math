# Frozen target LR: a linear intersecting partite covering obstruction

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

There exist an integer r>=2, pairwise disjoint finite sets V_1,...,V_r,
and a nonempty SET E of subsets of V=union_i V_i, such that:

1. For EVERY e in E and EVERY i in {1,...,r}, |e intersect V_i|=1.
2. For EVERY two DISTINCT e,f in E, |e intersect f|=1.
3. For EVERY C subset V with |C|<=r-1, there exists e in E with
   e intersect C empty.

Thus H=(V,E) is finite, r-partite, r-uniform, linear and intersecting,
and tau(H)=r. The upper bound follows because any edge covers E.
No bound on r, side sizes, degrees, edge count, coordinates, or construction
method is imposed. An existence proof must provide one such finite object
or rigorously establish its existence. A refutation must prove tau<=r-1
for EVERY finite linear intersecting r-partite r-uniform hypergraph.
No small-r exclusion or failure of one construction refutes LR.

Source family 162 at openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The balanced prime-order manuscript thm:main supplies tau=r at r=q+1,
with r vertices in every part; the extension-field companion thm:main
supplies other ranks. Neither asserts linearity. Their cor:tree-cover
statements already perform the standard monochromatic-component transfer.

Concrete operation chosen before sustained work: remove duplicate pair
agreements while retaining exactly one agreement for EVERY pair and
retaining the cover obstruction. In the source's partition presentation,
refinement cannot decrease tau; but splitting blocks must still leave
some shared block for every pair. The proposed additional mechanism is
simultaneous partition refinement (and, if it is obstructed, a genuinely
new partition trade) paying transitivity and unique pair coverage together.
It is not assumed that such a refinement or trade exists. The frozen
assertion allows any other construction, and will not be narrowed to the
refinement method if it fails.

Primary screen before freeze: Francetic--Herke--McKay--Wanless,
arXiv:1508.00951v3, actual Lemmas2.1-2.2, Theorem2.3, Corollary2.4
and their proofs impose delta>=2, Delta<=r-2 and Delta>=7 on an LR
witness; their r<=9 result is not a universal answer. Their Introduction
and Section3 describe equality and structured-cover examples, not LR.
The source explicitly credits these results and explains its merge/split
operation, which creates multiple agreements. A numerical scan or arbitrary
choice of one color per pair does not enforce the equivalence relations
needed by the refinement mechanism.

This is a research target, not a theorem or an assertion of worldwide
novelty. No independent proof/contribution PASS, nomination, count increase,
manuscript or Lean package is claimed or authorized by this freeze.
