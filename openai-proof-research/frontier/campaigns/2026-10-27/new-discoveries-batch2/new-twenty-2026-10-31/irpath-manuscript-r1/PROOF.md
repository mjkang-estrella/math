# Proof: the IR-graph of a 9-vertex graph is the path P_9 (MathDB 350452)

DRAFT, lane irpath-manuscript-r1 (Claude). Zero credit; root alone accepts. Part (ii) (cycles) is not claimed.

## Statement refuted

MathDB 350452 (raw line `mathdb-350452.jsonl`, sha256 `a37401f2cdfd8208b8da153b0e4747ef577175ccc520392ac23ee67a455b3ac3`):
"The path P_n is not an IR-graph for each n ≥ 3, and the cycle C_n is not an IR-graph for each n ≥ 5."
This is Conjectures 1 and 2 of Mynhardt–Roux, *Irredundance Graphs* (arXiv:1812.03382v3), restated as one conjecture with parts (i) and (ii) in arXiv:2104.09004v2 and in the survey arXiv:2003.05956.

Definitions (arXiv:1812.03382v3, §1.1–1.2): PN(v,D) = N[v] − N[D − {v}] with closed neighbourhoods. D is irredundant if PN(v,D) ≠ ∅ for every v ∈ D. IR(G) is the maximum size of an irredundant set, and IR(G)-sets are the irredundant sets of that size. G(IR) has the IR(G)-sets as vertices, with D ~ D′ iff some u ∈ D, v ∈ D′ have uv ∈ E(G) and D′ = (D − {u}) ∪ {v}. H is an IR-graph if H ≅ G(IR) for some graph G.

## The graph

V = {0,…,8}, with parts A = {0,1,2}, B = {3,4,5}, C = {6,7,8}. G is K_{3,3,3} minus 05, 08, 14, 23, 26, 37, 56. The deleted edges form the path 8–0–5–6–2–3–7 plus the edge 14. G has 20 edges:
`03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58`.

Write U(S) = V − N[S] for the vertices not dominated by S. U(v) is the complement neighbourhood:

| v | N[v] | U(v) |
|---|---|---|
| 0 | 0,3,4,6,7 | 1,2,5,8 |
| 1 | 1,3,5,6,7,8 | 0,2,4 |
| 2 | 2,4,5,7,8 | 0,1,3,6 |
| 3 | 0,1,3,6,8 | 2,4,5,7 |
| 4 | 0,2,4,6,7,8 | 1,3,5 |
| 5 | 1,2,5,7,8 | 0,3,4,6 |
| 6 | 0,1,3,4,6 | 2,5,7,8 |
| 7 | 0,1,2,4,5,7 | 3,6,8 |
| 8 | 1,2,3,4,5,8 | 0,6,7 |

W_0..W_8 = 012, 027, 047, 467, 678, 168, 138, 358, 345.

**Theorem.** IR(G) = 3. The IR(G)-sets are exactly W_0, …, W_8. W_i ~ W_j iff |i − j| = 1. Hence G(IR) ≅ P_9.

## Proof

**Lemma 1 (heredity).** If D′ ⊆ D and v ∈ D′, then N[D′ − v] ⊆ N[D − v], so PN(v,D) ⊆ PN(v,D′). Hence subsets of irredundant sets are irredundant.

**Lemma 2.** For any graph and any v ∈ D, PN(v,D) = U(D − v) − U(D), because N[D] = N[v] ∪ N[D − v]. Consequences:
- (a) If D − v dominates G, then PN(v,D) = ∅.
- (b) If D dominates G, then PN(v,D) = U(D − v).

**Step 1.** Intersect the U(v) to get U(xy) for all 36 pairs (Table 2 of the paper; `pair_common_complement_nbhd` in `outputs/graph-facts.json`). Exactly nine pairs dominate G: 05, 08, 14, 17, 23, 26, 37, 48, 56.

**Step 2.** The 84 triples T fall into three classes:
- **(a)** T contains a dominating pair. The third vertex fails by Lemma 2(a). There are 54 such triples.
- **(b)** T contains no dominating pair and U(T) ≠ ∅. There are 21 such triples, and for each a vertex v has U(T − v) = U(T), so PN(v,T) = ∅. In the list below, U(T) is in braces and v follows the colon.

  013{2}:3, 016{2}:0, 024{1}:4, 034{5}:0, 036{2,5}:6, 046{5}:0, 067{8}:0, 125{0}:5, 128{0}:2, 135{4}:1, 136{2}:3, 158{0}:5, 245{3}:2, 247{3}:2, 257{3,6}:2, 258{0,6}:2, 278{6}:2, 346{5}:3, 368{7}:3, 457{3}:5, 578{6}:5.
- **(c)** T dominates G and contains no dominating pair. By Lemma 2(b), PN(v,T) = U(T − v) ≠ ∅ for every v, so T is irredundant. Exactly W_0..W_8 are in this class.

The private neighbourhoods of the W_i are:
- W_0: 0:{0} 1:{1} 2:{2}
- W_1: 0:{3,6} 2:{8} 7:{1}
- W_2: 0:{3} 4:{8} 7:{1,5}
- W_3: 4:{8} 6:{3} 7:{5}
- W_4: 6:{6} 7:{7} 8:{8}
- W_5: 1:{7} 6:{0} 8:{2}
- W_6: 1:{7} 3:{0} 8:{2,4}
- W_7: 3:{0,6} 5:{7} 8:{4}
- W_8: 3:{3} 4:{4} 5:{5}

**Step 3.** Suppose D is an irredundant 4-set. Its four triples are irredundant (Lemma 1), so they are four of the W_i, and any two of them share two vertices. But W_i and W_j share two vertices only when |i − j| = 1, so no three of the W_i pairwise share two vertices. This is a contradiction, so there is no irredundant 4-set, and by heredity none larger. Hence IR(G) = 3, and the IR(G)-sets are W_0..W_8.

Explicit witnesses for all 126 four-sets:
- 121 four-sets contain one of the 63 dominating triples (classes (a) and (c)). The vertex outside that triple fails.
- The other five are U(0) = 1258, U(2) = 0136, U(3) = 2457, U(5) = 0346 and U(6) = 2578. In these, the vertices 2, 0, 2, 0 and 2 respectively fail, since U(D − v) = {w} = U(D).
- The full table is `four_subsets` in `outputs/graph-facts.json`.

**Step 4.** The IR-sets have size 3, so D ~ D′ iff |D ∩ D′| = 2 and the exchanged pair is an edge.
- Of the 36 pairs, exactly the 8 consecutive ones share two vertices. The other 28 share at most one, so they are not adjacent.
- The consecutive swaps are 1→7, 2→4, 0→6, 4→8, 7→1, 6→3, 1→5 and 8→4. All of 17, 24, 06, 48, 17, 36, 15 and 48 are edges of G.
- Hence G(IR) is the path W_0 … W_8. ∎

**Corollary.** P_9 is an IR-graph. Conjecture 1 (part (i)) is false, and so is the MathDB conjunction.

**Remark.** W_0, W_4 and W_8 (the parts A, C and B) are independent IR-sets. H = G(IR) is connected, has order 9 and has maximum degree 2. This answers negatively the source Problem "independent IR-set and H connected of order ≥ 3 ⇒ Δ(H) ≥ 3". It is part of the same result, not a separate claim.

## Machine checks (this lane, fresh)

- `scripts/recompute.py` checks everything above by brute force over all 512 subsets. It also checks the identity in Lemma 2 on all subsets of size ≥ 2 (2295 (v,D) checks), finds an automorphism group of order 2 (9! permutations), and finds irredundant counts by size of 1, 9, 36, 9, 0, …
- `scripts/check_numbers.py` checks 68 printed claims against the outputs; all pass.
- Lean: `IR350452.conjecture_false : ¬ IR350452.Conjecture` in `lean/source.zip`, reused byte-identically. This lane did not run Lean.
