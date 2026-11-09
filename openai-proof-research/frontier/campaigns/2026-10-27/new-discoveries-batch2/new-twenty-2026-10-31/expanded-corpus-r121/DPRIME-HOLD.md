# MathDB 349435: source-version HOLD, a 24-cycle in D-prime(21,3)

No root acceptance or credit is claimed. The mathematical witness below refutes Conjecture 2.9 in arXiv:2101.06743v1. The latest served arXiv version removes this entire construction and conjecture. Root must adjudicate whether this is an eligible surviving MathDB target, a retracted conjecture, or an uncredited historical resolution. There is no claim that absence from the new version means a prior published refutation. The database calls D-prime a hypergraph; source Definition 2.7 defines an ordinary bipartite graph, which governs here.

For q=3 the two parts A and B are copies of F_3^k. The coordinate order is

    1,11,12,21,22,22',23,32,33,33',34,43,44,44',45,54,55,55',56,65,66,...

All coordinates below are residues 0,1,2. Write a_j,b_j for the zero-indexed coordinates of adjacent A,B vertices. Their first relation is

    a_1-a_0+b_1-b_0+a_0*b_0 = 0 (mod 3).

For j>=2 put t=1 if j<4 and t=j-2 otherwise. The j-th relation is

    a_j+a_t+b_j+b_t + a_t*b_0 = 0 (mod 3) if j mod 4 is 0 or 3,
    a_j+a_t+b_j+b_t + a_0*b_t = 0 (mod 3) otherwise.

These are exactly the first k-1 equations (2.8), not a new graph model. The author's pinned public exportAdjLists.cpp independently confirms the first ten equations, and the remaining periodic rule follows directly from the four displayed i>=2 equations in Definition 2.7.

Take k=21. The following cyclic list has 24 distinct vertices. Every consecutive pair, including the last and first, satisfies all 20 equations. Thus it is an ordinary simple 24-cycle in D-prime(21,3), while the conjectured lower bound for odd k is k+5=26. This refutes the universal girth assertion already at the admissible prime power 3. It does not compute the exact girth or assert smallest k.

| Index | Part | Coordinates |
|---|---|---|
| 0 | B | 210201111211221112121 |
| 1 | A | 221002211010012011121 |
| 2 | B | 000121122211121022110 |
| 3 | A | 000212211122212011220 |
| 4 | B | 221210220202111210211 |
| 5 | A | 211211011022200010020 |
| 6 | B | 101220200202011210211 |
| 7 | A | 011212122211121222111 |
| 8 | B | 022121211122212111222 |
| 9 | A | 201012020010120200101 |
| 10 | B | 112211221122112211221 |
| 11 | A | 000000000000000000000 |
| 12 | B | 000000000000000000000 |
| 13 | A | 221122112211221122112 |
| 14 | B | 210110021002100210021 |
| 15 | A | 011121012001200120012 |
| 16 | B | 101011021002100210021 |
| 17 | A | 211121110200201102002 |
| 18 | B | 221001010000100200001 |
| 19 | A | 000121110100200100002 |
| 20 | B | 112120100100100200001 |
| 21 | A | 201102221022112221110 |
| 22 | B | 022000122100000020012 |
| 23 | A | 011000211200000010021 |

The graph search used a structured breadth-first search from zero and 99 reproducibly seeded roots at each k=12 through 20. No forbidden cycle was found at those sampled roots. At k=21 the zero root yielded this certificate; k=22,23 also yielded 24-cycles and k=24 a 26-cycle. A k=32 run was CPU-capped after 12 completed roots: no full coverage is claimed. The searches do not exhaust all components and cannot establish minimality. The 21-coordinate witness is larger than the source's verified k<=10 isomorphism range and its k=11 comparison.

The independent script check-dprime.py evaluates each original bilinear relation directly, without invoking the neighbor generator. outputs/dprime-cycle.json records every residue, all zero, together with the vertex list and distinctness check. The complete Lean source DPrime.lean defines the equations, tagged vertices, every cyclic edge and distinctness in its IsCycle predicate. DPrime.cycle_certificate is a kernel-decided certificate; DPrime.source_refutation refutes the full all-k conjecture restricted to F_3. This restriction is a logically sufficient counterexample to the source's all-prime-power conjecture; no field-of-order-9 model or general girth algorithm is asserted. The formal concrete F_3 model is residues Fin 3 with integer polynomial equalities modulo 3. Its source equivalence is direct coordinate substitution as explained above; independent statement-fidelity review is outstanding.

Prior-art limits: live OpenAI/math HEAD and complete current Omega D5/Problems trees were path-screened, not semantically certified. Targeted title and notation searches located no exact counterexample, which is only a bounded non-finding. The source author's repository at its fetched HEAD still documents only k=11,q=3; its code is explicitly limited to k<=11. README and the original equation evaluator were read; the printed cycle list was screened for its parameter scope. No global novelty claim is made. Current arXiv removal is a material qualification blocker. The author-hosted preprint indexed by web search still prints the conjecture, but no authenticated journal final version has been body-compared.

The Lean endpoint has transitive axioms propext and Quot.sound only. The module-origin audit covers all 43 declarations, including generated ones; safe, nonpartial, body-present and allowed transitive axioms. Fresh extracted strict build, leanchecker and audit receipts are recorded in outputs/dprime-replay.json and logs/dprime-fresh-*. Cached dependency oleans are trusted, not rebuilt from upstream. This packet has not had independent review and is not self-accepted.
