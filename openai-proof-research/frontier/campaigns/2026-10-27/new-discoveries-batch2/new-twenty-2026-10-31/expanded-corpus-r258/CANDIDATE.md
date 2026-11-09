# MathDB 359209: exact finite certificate tasks, not a claimed counterexample

Zero credit. No solver, Lean build, or large search was run. Root must close the remaining literature and registry gates before execution. The source-eligible mathematical mechanism is a coloring of a **complete multipartite** graph, not of a bipartite graph.

## Literal source and printed construction inventory

Anuwiksa–Simanjuntak–Baskoro, arXiv:2307.09736v1, Definition 1 and Conjecture 2, pp. 2 and 11: m_c is the least part size s forcing a monochromatic K_{2,n} in K_{c×s}. Conjecture 2 is m_n(K_{2,n},K_{2,n})=5 for every n≥2. The record's title can easily cause the wrong encoding. Vertices on the two-vertex side of the forbidden copy may lie in the same host part or in different host parts. Both cases must be checked.

The sole listed arXiv version was obtained, together with its metadata. The 15-page source's explicit families are: Example 1 using conference-parameter strongly regular graphs and symmetric Hadamard matrices; Examples 2 and 3 applying the general bounds to other strongly regular parameter sets; Examples 4 and 5 using prime powers congruent to 1 mod 4 and symmetric Hadamard orders 4k and 4r^4. The r=1 application requires p^t≥7, and does not settle n=5. Section 2's matrices, Examples 1–5, Theorems 3–5 and the proof constructions must be compared with any returned witness. No source n=5 coloring is proposed here. The older Perondi–Monte Carmelo paper (Matemática Contemporânea 46, pp.103–111), actual body obtained, has Proposition 9 and Corollaries 10–11 with prime-power assumptions; these do not give m_5(K_{2,5},K_{2,5})=5 by substitution. Its multicolor C4 results have different target graphs.

Unclosed gate: the author's 2025 dissertation was located through an author publication page but its body was not read; the complete forward citation inventory is not established. The current registry path screen is bounded, with no complete current Omega subtree retrieved. Do not interpret these gaps as permission or novelty clearance.

## An ordinary exact reduction for the upper-bound direction

Suppose a coloring of K_{n×5} contains no monochromatic K_{2,n}. For a fixed part A, count monochromatic two-edge wedges with both ends in A. Each outside vertex has r red neighbors in A and contributes

C(r,2)+C(5-r,2) ≥ 4,

with equality precisely at r=2 or 3. There are 5(n−1) outside vertices, so the wedge count is at least 20(n−1). Each of the ten pairs in A has at most n−1 common neighbors in either color, giving the reverse bound 20(n−1). Thus equality holds everywhere. Each external vertex has two or three red neighbors in A, and each pair in A has exactly n−1 common neighbors of each color.

For u,v in A write d_u,d_v for their total red degrees. Their common blue neighbors number 5(n−1)−d_u−d_v+(n−1). Equality with n−1 forces d_u+d_v=5(n−1). Since |A|=5, all vertices have red degree 5(n−1)/2. This rules out even n. If n≡3 mod 4, the sum of red degrees is 25n(n−1)/2, which is odd, also impossible.

A global wedge count handles n≥7, regardless of congruence. Each vertex has degree d=5(n−1). Its monochromatic wedges are at least d(d−2)/4. Counting by end pairs gives

(5n) d(d−2)/4 ≤ C(5n,2)·2(n−1).

After division by positive factors this implies 5n−31≤0, impossible for n≥7. Together these arguments prove the upper bound m_n≤5 for every n≥2 except possibly n=5. This is a short range result, probably routine, **not a full literal solution and not a credit proposal**. It motivates focusing the upper-bound counterexample task on n=5.

For n=5, any avoiding coloring of K_{5×5} must have red and blue degree 10 at every vertex; every vertex has 2 red neighbors in two other parts and 3 in the other two; and pairs in the same part have exactly 4 common neighbors in each color. This sharply restricts a witness search without asserting existence.

## Exact next task for Pi

First finish the source gate above. If cleared, use at most 2 CPUs, CPU 120 s, wall 140 s, sampled RSS at most 6 GiB per finite process; stop all processes before handback.

1. Cheapest decisive diagnostic: n=3, s=4. Use vertices (a,i) with a∈Fin 3 and i∈Fin 4. There are 48 independent edge bits. For each unordered pair u,v, let W be the vertices outside both endpoint host parts (outside their one shared part if applicable). For every 3-subset T⊂W, forbid all six incident edges being red and forbid all six being blue. Exactly 2400 clauses of length 6 before symmetry clauses: 18 same-part pairs each give 2 C(8,3), and 48 different-part pairs give 2 C(4,3). Start without symmetry breaking. UNSAT would prove m_3≤4, refuting the exact conjecture; return LRAT/RUP and a verified encoding bridge. SAT is only an uncredited lower-bound witness, so stop that direction rather than calling it a solution.

2. Main upper-bound diagnostic: n=5, s=5. Use 25 vertices and 250 independent edge bits. For each of 300 unordered vertex pairs, require at most 4 red and at most 4 blue common neighbors among eligible vertices. There are 20 eligible vertices for 50 same-part pairs and 15 for 250 cross-part pairs. A direct CNF has 3,051,900 clauses of length 10; avoid this unnecessary expansion by introducing conjunction bits and a sequential cardinality encoding. There are 4750 eligible pair–neighbor triples per color. Add the proved exact-balance constraints above if their encoding bridges are proved. No unproved automorphism restriction is allowed.

A SAT witness is only 250 bits. Export lexicographically ordered edge bits plus the 300 pairs' two exact common-neighbor counts, block row sums, and file hashes. An independent checker must recompute counts from the edge bits, not trust supplied counts. Each count must be at most 4. This proves that no monochromatic K_{2,5} exists: any injective copy has a two-vertex side u,v and five distinct eligible common neighbors, contradicting the count. Host monotonicity then contradicts m_5=5. The endpoint is the exact negation, without needing the true value of m_5.

UNSAT in task 2 establishes only the n=5 upper bound, and must not be promoted to a new full solution: all lower bounds would remain. Do not broaden automatically into unbounded searches. The n=4,s=4 lower-direction diagnostic (96 edge bits) is a possible later task only after root reassessment, not an instruction to run it now.

Lean implementation if a decisive certificate exists: finite vertices, symmetric Boolean edge coloring on distinct host parts, Finset count computation, injective graph-copy definition, and a proved common-neighbor bridge. For a SAT witness, kernel-reduced finite counts suffice. For UNSAT, use a proved RUP/LRAT checker and encoding soundness; never native_decide, sorry, new axioms, or an external solver verdict as proof. Root independently reviews fidelity, novelty, substantive significance and strict replay. No Lean success is claimed here.
