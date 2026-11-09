# expanded-corpus-r209 (Claude lane): summary

This lane covered 20 reserved MathDB IDs (reserve8, 347121–357011). It produced one candidate, 350452. Its ordinary proof and finite certificate are complete; the Lean draft is UNCOMPILED. Of the other 19 IDs, 6 are excluded and 13 are parked. Nothing is self-accepted.

**Restrictions observed.**
- No Lean, lake, leanchecker, or SAT/ILP binaries were run.
- Every computation ran as one foreground `bash -c 'ulimit -v 2000000; timeout 100 python3 -I …'` per tool call, in pure Python (numpy is not installed).
- No child agents and no git. Writes stayed inside this lane.
- Downloads went into fresh `sources/<label>-<utc>/` folders with receipts that were never overwritten.
- No 403 or 429 responses were met. Crossref, Semantic Scholar, the arXiv search API and ScienceDirect were not used.

## Candidate: 350452 (Mynhardt–Roux non-IR conjecture for paths and cycles)

The conjecture says that P_n is not an IR-graph for any n ≥ 3, and C_n is not an IR-graph for any n ≥ 5.

**Counterexample.** Take the 9-vertex graph G = K_{3,3,3} (parts {0,1,2}, {3,4,5}, {6,7,8}) with the edges 05, 08, 14, 23, 26, 37, 56 removed; it has 20 edges.
- IR(G) = 3, and G has exactly nine IR(G)-sets.
- Their swap graph is the path P_9: {0,1,2}–{0,2,7}–{0,4,7}–{4,6,7}–{6,7,8}–{1,6,8}–{1,3,8}–{3,5,8}–{3,4,5}.
- So P_9 is an IR-graph, which refutes the conjunction.

**Certificate.** Heredity of irredundance, then:
- for each of the 126 four-subsets, a vertex with no private neighbour;
- each of the 84 three-subsets classified (exactly the nine above are irredundant, with their private neighbours listed);
- exactly 8 adjacent pairs among the 36 IR-set pairs.

**Exhaustive coverage.**
- No connected source graph on ≤ 8 vertices has a path or cycle IR-graph.
- On 9 vertices (all extensions of the 12346 eight-vertex graphs), the path IR-graphs that occur are exactly P_7, P_8 and P_9, in 3 isomorphism classes. There is no P_6 and no cycle.
- So 9 is the minimum source order.

**Growth evidence.** One-vertex extensions reach P_14 on 11 vertices, with no cycles. This suggests infinitely many paths are IR-graphs; that is not proved.

**Prior-art screen.**
- Literature and citing works show the conjecture still open: the 2022 Discrete Mathematics companion paper and the 2020 survey both list it.
- Lean Pool, OpenAI/math, and Omega (complete D5, Problems and Library subtrees at the moved head e0da8fcc) have no IR-graph result.
- GitHub repository search (5 queries) returned no hits.

**Lean cost: low.** The plan is kernel `decide` on 126 + 84 subsets and 81 pairs, plus short Finset lemmas. The IR-graph adjacency is literal; symmetry is proved from the equal cardinality of IR-sets.

**Files.**
- `CANDIDATE.md`: proof, statement correspondence and Lean plan.
- `outputs/certificate-350452.json`
- `lean-packet/IRPathCounterexample.lean` (UNCOMPILED)
- `outputs/registry-screen.json`

**Open issue for root.** Part (ii), for cycles, remains open. The negation of the record needs only part (i), but root may weigh significance on (i) alone. A by-product also answers the authors' companion Problem (independent IR-set ⇒ Δ ≥ 3) negatively; that Problem is not reserved and not claimed.

## Other reserved IDs

| ID | Disposition | Basis |
|---|---|---|
| 354089 | parked after computation | Source (Balogh–Clemen–Lidický Conj. 2.8) proves the 3-partite case. Tested below the bound: W5 blow-ups up to n=24 and at n=45 (90 < 100); simulated annealing over K4-free graphs at n=9 (tight at 4) and n=12; I_a ∨ (maximal triangle-free) at n=12 (max 6 < 7.11) and n=15 (max 10 < 11.11). Sibling Conj. 2.7 refuted by Xu–Zhang via I_7 ∨ C_5. |
| 356083 | excluded: source-internal | Source Thm 1 plus greedy completion (≤ 15 blocked colours of 111) shows every partial 6-factorization of any sub-hypergraph of K_10^3 extends to K_38^3. The 106-colour conjecture is false by a two-line source bridge (zero credit). |
| 349147 | parked after exhaustive computation | No violation for any k over all trees with n ≤ 16. The k=n case is the open Radenković–Gutman minimum Laplacian-energy conjecture. |
| 352073 | excluded: publicly refuted | Genevois, Pacific J. Math. 340 (2026): PFB_n = PT_n is not virtually a RAAG for n=7 and n ≥ 11. |
| 351156 | excluded: proved | Labbé–Lapointe–Steiner, Algebr. Comb. 6 (2023). |
| 348416, 348866, 356852 | excluded | Solved in the source (record text). |
| 356212 | parked | First set proved by Chern–Fu–Lin. The others are all-n enumeration claims. |
| 352605 | parked | All-n composition equivalences, verified to n=35 by the authors. |
| 349851 | parked | Authors verified n ≤ 8. A pure-Python S_9 push (~1.7e9 steps) was not run. |
| 348375 | parked | Reduces to Serre's density theorem for T_p mod 2 (routine Ono/Radu route); not Lean-feasible. |
| 350804, 351464, 352014, 347121, 348076, 348577, 357011 | parked | Deep, analytic, infinite, or no finite route in this lane (see `results.json`). |

## Deliverables

- `results.json`: 20 ID-keyed entries, each with chunk, line, raw, chunk and statement hashes, outcome, depth and summary.
- `raw/*.jsonl`: exact raw lines.
- `outputs/exact-records.json`
- `scripts/`: all scripts used.
- `outputs/`: full run outputs.
- `sources/`: dated receipts.
