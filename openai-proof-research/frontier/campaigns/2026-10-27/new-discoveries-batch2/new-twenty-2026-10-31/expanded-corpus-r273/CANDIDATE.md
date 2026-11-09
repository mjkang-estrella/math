# 378416: ordinary counterexample, qualification HOLD

No acceptance, no Lean endpoint, no permission to start Pi. The campaign remains 52/60. This is a complete ordinary argument for the intended primary-source Conjecture 4.9(i), with a conditional implementation plan. Journal, prior-art and literal-definition issues below must be adjudicated by root.

## Exact target and conventions

Deza–Dutour, arXiv:math/0405279v1, Conjecture 4.9(i), printed p13: a type-{3,4} simplicial complex of rank d is not z-uniform iff its characteristic partition has sizes (d/2,d/2), or all even, except simplex. Here z-uniform means all zigzags have the same length; a zigzag is the orbit of T = sigma_d ... sigma_1 on flags, with opposite orientations identified. Identifying the reverse does not halve its length. Definitions 2.3 and duality Theorem 2.6 were read.

There is a real fidelity issue: the source's sentence defining type {3,4} immediately before this conjecture, and the MathDB paraphrase, use (d-2)-faces of a (d-1)-complex. A thin simplicial sphere has exactly TWO facets through a codimension-one face. The classification cited there is instead about codimension-TWO links of lengths 3 and 4. Its actual primary definition is Deza–Dutour–Shtogrin, math/0310165, Definition 1.1; Definition 1.2 and Section 2 give K(P). This argument uses that intended, classified family. It does not assert a counterexample to the internally inconsistent literal codimension-one paraphrase. Root must require an explicit fidelity ruling before formalizing or counting anything. The counterexample concerns the substantive uniformity assertion, not the dimension correction.

## Finite complex

Let A={a0,a1,a2,a3}, B={b0,...,b6}, disjoint. Define K to consist of all subsets X of A union B such that A is not contained in X and B is not contained in X. Thus K is the join of the boundaries of a 3-simplex and a 6-simplex. Its 28 facets are (A minus {ai}) union (B minus {bj}), each of size 9. It is a thin connected simplicial 8-sphere, rank d=9.

For completeness, every face of size 7 omits four vertices in total, at least one in each block. Omission counts are (3,1), (2,2), or (1,3). Its link is respectively the boundary of a triangle, the join of two 0-spheres (a square), or the boundary of a triangle. These have 3,4,3 edges/facets respectively. So K has the intended type {3,4}. On any facet, the characteristic partition groups its three A vertices and six B vertices: deleting two vertices in the same group gives link length 3; in different groups length 4. Its partition is (3,6). This is neither two equal parts nor all even, and K is not a simplex. The conjecture therefore predicts z-uniformity.

## Actual flag transition, including semantic bridge

A flag of K is uniquely an ordered list v=(v0,...,v8) of the vertices of a facet, interpreted as the chain of prefix sets of lengths 1,...,9. Its missing vertices are one alpha in A and one beta in B. For j<9, sigma_j swaps entries at positions j-1 and j of this ordered list: it changes exactly the prefix of length j. Applying sigma_1 through sigma_8 consequently shifts v0 successively to the last position. The last involution sigma_9 changes the facet across the ridge {v1,...,v8}. The unique other completion is alpha if v0 is in A, and beta if v0 is in B. Therefore

    T(v0,...,v8) = (v1,...,v8, missing vertex in the block of v0).

After the step, the new omitted vertex of that block is v0. This establishes the transition from the actual face-poset involutions, rather than defining a convenient unrelated recurrence.

Encode a flag by its binary block word w (three A letters and six B letters), and its two ordered cyclic queues: the A vertices in their order in v followed by the omitted A vertex; similarly for B. This encoding is injective. T rotates w left once. In the queue corresponding to the departing letter it rotates the queue left once, leaving the other queue fixed. All entries of each queue are distinct. After t steps a flag returns iff (1) the block word returns, (2) the number of departing A letters is divisible by 4, and (3) the number of departing B letters is divisible by 7.

## Two exact periods, no enumeration

Take F with ordered facet

    (a0,b0,b1,a1,b2,b3,a2,b4,b5), omitted a3,b6.

Its word is ABBABBABB, of least rotation period 3. A return must have t=3j. The departing counts are j and 2j. The return conditions are 4|j and 7|2j, equivalently 28|j. Its least T-period is therefore 84.

Take G with ordered facet

    (a0,a1,a2,b0,b1,b2,b3,b4,b5), omitted a3,b6.

Its word AAABBBBBB has least rotation period 9: a nontrivial period dividing 9 would be 1 or 3, neither of which works (each length-three block would have to agree). A return has t=9j, with departing counts 3j and 6j. The return conditions are 4|3j and 7|6j, equivalently 28|j. Its least T-period is 252.

Thus K has two zigzag lengths 84 and 252. It is not z-uniform, contradicting the predicted uniformity for partition (3,6). Clause (i)'s divisibility addendum is not refuted: gcd(84,252)=84. Clauses (ii)–(iv) are not separately claimed. A counterexample to the first equivalence refutes the conjunction in the record's intended interpretation.

## Source-object and prior-art comparison; limits

The 2004 source reports checking this conjecture only through d=8. The example is rank 9. Its entire printed family K(P) is a standard join/product-of-simplices family, not claimed as a new construction. The source prints no rank-nine (3,6) witness or the orbit calculation above in the target passage. The new mathematical content proposed here is the failure of its uniformity criterion, through unequal exact periods, not merely constructing another member of its family. That distinction still needs independent significance review: being outside a table's range alone is NOT clearance from routine-source modification.

Deza–Pankov 1509.03754v3, Sections 2.1, 3.1–3.2, gives join examples and the general vertex-shift description of T; that standard bridge agrees with the direct proof above. It is not claimed new. Its later Coxeter-complex result concerns flag complexes of polytopes, not automatically all joins of simplex boundaries. Selected definitions and the vertex-shift proof passage were read; the entire paper's theorem/proof corpus was NOT exhausted. The journal HTML is cached, but not fully read. The 2015 chemistry book, all citations to the 2004 paper, and the 2005 printed source body remain unread. The author-listed source journal URL returned 403; no retry/bypass. Deza's author site failed TLS validation; no disabling validation. No assertion of worldwide novelty or latest-journal clearance.

Historical r720 concerned 378414 (products of polygons), and r265 concerned 378417 (Lins triality), both parked. Those are the same source family, not this claimed witness; they do not supply acceptance precedent. Searches for exact source/title and (84,252)/(3,6) found no inspected matching theorem, but absence of search hits is not novelty evidence. Current OpenAI catalogue fetched with commit-history first displayed head 4eaee87548250b2682affda7d05d947c05554bae; no zigzag/Petrie routing match. Current LeanPool projects.yml fetched; bounded routing screen only, not complete theorem-body audit or head pin. See receipts and SOURCE-READ-INVENTORY.md.

## Conditional Pi implementation plan, only after root qualification

Use Pi spark/GLM-5.3-Flash-EXL3, high thinking, only if root authorizes after the source-fidelity and significance/prior-art gates. No process has been started.

1. Define literal finite simplicial complex on Fin 11 by forbidding the two full blocks. Prove downward closure; characterize facets and ridges, and all codimension-two link facet counts. Prove partition (3,6) from those counts. Use actual flags as maximal face chains, not a primitive bespoke machine.
2. Prove the bijection between flags and ordered facets, and derive each sigma_j from the unique alternate intermediate face. Prove T's shift/replacement formula. This is a necessary semantic bridge and is given an ordinary proof above.
3. Either prove the queue-return criterion, or provide two directly checked lists of ordered facets of lengths 84 and 252, proving transition, closure and pairwise distinctness through actual flags. At most 336 states of nine vertex labels, roughly 3024 labels; no enumeration of all 28*9! flags or solver is required. Kernel reduction is sufficient for finite local checks; no native_decide or added axioms.
4. Define zigzag length as least positive return time (or equivalent orbit cardinality). From each closed distinct transition list prove its exact orbit length. Prove 84 != 252 and refute the exact primary equivalence in its intended type definition. Explicitly state why the MathDB codimension wording is not silently substituted.
5. Independent fidelity, mathematics, significance and prior-art reviews are required. A paper and fresh extracted strict replay, pinned dependencies, and transitive axiom audit remain required before any acceptance. No Lean files or manuscript have been written here.
