# Candidate 350452: the path P_9 is an IR-graph (Mynhardt–Roux conjecture refuted)

Lane expanded-corpus-r209 (Claude). Status: **candidate only**. The ordinary proof and the finite certificate are complete. The Lean draft is **UNCOMPILED**, because this lane may not run Lean. Zero credit until root accepts.

## 1. Record and source

- MathDB 350452, "Non-IR conjecture for paths and cycles". Corpus `mathdb-normalized-chunk-0007.jsonl` line 4787. Raw sha256 `a37401f2cdfd8208b8da153b0e4747ef577175ccc520392ac23ee67a455b3ac3`; statement sha256 `202a3342692ab879eb785af329027d1d30ee0997836e07b9f02383649d316436`. Raw line saved in `raw/350452.jsonl`.
- Literal statement: "The path P_n is not an IR-graph for each n ≥ 3, and the cycle C_n is not an IR-graph for each n ≥ 5."
- MathDB source: C. M. Mynhardt and A. Roux, *Irredundance Trees of Diameter 3*, arXiv:2104.09004v2 (Discrete Math. 2022), Open Problems, Conjecture 1(i)(ii). It is attributed there to Mynhardt–Roux, *Irredundance Graphs*, arXiv:1812.03382v3 (Discrete Appl. Math. 2022), Conjectures 1 and 2 in Section "Open Problems". It is repeated in the survey arXiv:2003.05956 by Mynhardt and Nasserasr.
- Source definitions (arXiv:1812.03382v3, Section 1.1 and the paragraph on IR-graphs):
  - A vertex w is a D-private neighbour of v ∈ D if w ∈ N[v] − N[D − {v}].
  - D is irredundant if every v ∈ D has a D-private neighbour.
  - IR(G) is the maximum size of an irredundant set, and an IR(G)-set is an irredundant set of size IR(G).
  - The IR-graph G(IR) has the IR(G)-sets as its vertices. D and D′ are adjacent iff there are u ∈ D and v ∈ D′ with uv ∈ E(G) and D′ = (D − {u}) ∪ {v}.
  - H is an IR-graph if H ≅ G(IR) for some graph G.
- What the source proves: P_3, P_4, P_5, C_5, C_6 and C_7 are not IR-graphs (Theorem `Thm_Main`(ii) of arXiv:1812.03382v3). The authors write: "A direct proof that P_5 is not an IR-graph is … not simple enough to easily generalize to … longer paths and cycles. Nevertheless, we believe this to be true."

## 2. The counterexample

The graph G has vertex set {0,…,8} and these 20 edges:

`03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58`

Structure: G is the complete tripartite graph K_{3,3,3} on the parts {0,1,2}, {3,4,5} and {6,7,8}, with the seven edges 05, 08, 14, 23, 26, 37 and 56 deleted. Its complement is three disjoint triangles plus those seven cross edges. G is not a named classical graph: it is not regular, it has degrees 4,4,4,4,4,5,5,5,5, and its automorphism group has order 2.

Closed neighbourhoods:

| v | N[v] |
|---|---|
| 0 | {0,3,4,6,7} |
| 1 | {1,3,5,6,7,8} |
| 2 | {2,4,5,7,8} |
| 3 | {0,1,3,6,8} |
| 4 | {0,2,4,6,7,8} |
| 5 | {1,2,5,7,8} |
| 6 | {0,1,3,4,6} |
| 7 | {0,1,2,4,5,7} |
| 8 | {1,2,3,4,5,8} |

**Theorem.** IR(G) = 3. G has exactly nine IR(G)-sets, and its IR-graph is the path

{0,1,2} – {0,2,7} – {0,4,7} – {4,6,7} – {6,7,8} – {1,6,8} – {1,3,8} – {3,5,8} – {3,4,5}.

Hence G(IR) ≅ P_9, P_9 is an IR-graph, and the conjunction in MathDB 350452 is false.

### Proof

1. **Heredity.** If D is irredundant and D′ ⊆ D, then D′ is irredundant. For v ∈ D′, N[D′ − {v}] ⊆ N[D − {v}], so every D-private neighbour of v is also D′-private.
2. **No irredundant 4-set.** For each of the C(9,4) = 126 four-subsets D, the certificate `outputs/certificate-350452.json` (key `four_subsets`) names a vertex v ∈ D with N[v] ⊆ N[D − {v}]. Each row is checked from the table above. For example, D = {0,1,2,3}: N[0] = {0,3,4,6,7} ⊆ N[1] ∪ N[2] ∪ N[3]. By heredity no irredundant set has 4 or more vertices, so IR(G) ≤ 3.
3. **Irredundant 3-sets.** Of the 84 three-subsets (key `three_subsets`), exactly these nine are irredundant. Private neighbours are shown as v:{…}:
   - {0,1,2}: 0:{0}, 1:{1}, 2:{2} (an independent set)
   - {0,2,7}: 0:{3,6}, 2:{8}, 7:{1}
   - {0,4,7}: 0:{3}, 4:{8}, 7:{1,5}
   - {4,6,7}: 4:{8}, 6:{3}, 7:{5}
   - {6,7,8}: 6:{6}, 7:{7}, 8:{8} (independent)
   - {1,6,8}: 1:{7}, 6:{0}, 8:{2}
   - {1,3,8}: 1:{7}, 3:{0}, 8:{2,4}
   - {3,5,8}: 3:{0,6}, 5:{7}, 8:{4}
   - {3,4,5}: 3:{3}, 4:{4}, 5:{5} (independent)

   Each of the other 75 three-subsets has a named vertex with no private neighbour. So IR(G) = 3 and these nine sets are the IR(G)-sets.
4. **Adjacency.** Two 3-sets can be adjacent only if they share exactly two vertices and the swapped pair (u,v) is an edge. Among the 36 pairs of IR-sets (key `IR_set_pairs`), exactly eight are adjacent. They are the consecutive pairs of the displayed path: swaps 1→7, 2→4, 0→6, 4→8, 7→1, 6→3, 1→5 and 8→4, which are edges 17, 24, 06, 48, 17, 36, 15 and 48. Every other pair either differs in two or more vertices or differs by a non-edge. So G(IR) is the path P_9. ∎

### Independent verification (diagnostic)

- The bitmask search (`scripts/irgraph_chunk.py`) and a separate plain-set implementation (`scripts/verify_ir.py`) give identical results.
- The certificate script (`scripts/certificate_350452.py`) asserts every row.
- `scripts/lemma_check.py` confirms two things:
  - The private-neighbour definition and Brewster's closed-neighbourhood definition (N[v] ⊄ ∪_{u∈D−v} N[u]) agree on all 512 subsets.
  - The example is consistent with the source's Lemma `Lem_Not_Path`. Every flip-set X′ built from external private neighbours is an IR-set at distance 4 or 5 from X, never 3, so the lemma's hypothesis never applies.

## 3. Search coverage (exact)

- **Order ≤ 8, exhaustive.** All connected graphs on at most 8 vertices: the non-isomorphic graphs on at most 7 vertices, plus every one-vertex extension of all 1044 graphs on 7 vertices. No IR-graph is P_m (m ≥ 3) or C_m (m ≥ 5). Output in `outputs/irgraph-N7.txt` and `outputs/irgraph-N8.txt`.
- **Order 9, exhaustive.** Every one-vertex extension (all 256 neighbourhoods) of all 12346 non-isomorphic graphs on 8 vertices; connected source graphs only. The path IR-graphs found are P_7, P_8 and P_9: 21 labelled hits in 3 isomorphism classes. There is no P_6 and no C_m with m ≥ 5. So **9 is the minimum order of a connected source graph** for any path IR-graph of order ≥ 3. Output in `outputs/irgraph-N9-chunks.jsonl`.
- **Growth evidence (not exhaustive).** One-vertex extensions of the 9-vertex hits give P_7, P_8, P_9, P_10 and P_12 on 10 vertices. Extending the long ones gives P_9 to P_14 on 11 vertices. The 11-vertex P_14 example contains the 9-vertex graph above plus two gadget vertices that lengthen the path at both ends. No cycle IR-graphs were found. This suggests infinitely many paths are IR-graphs. That is **not proved**, and it is not needed for the refutation.
- **By-product.** {0,1,2} is an independent IR-set, and G(IR) is connected with order 9 and maximum degree 2. This answers negatively the authors' Problem in arXiv:1812.03382v3 (independent IR-set ⇒ maximum degree ≥ 3). That Problem is not a reserved record and is not claimed.

## 4. Prior art and novelty screen (bounded)

- **Literature.** Web searches (standard and extended) on the conjecture, IR-graphs, Mynhardt–Roux and citing works. Later sources still list the conjecture as open: the companion paper arXiv:2104.09004v2 (DM 2022) and the survey arXiv:2003.05956. A 2025 irredundance paper (arXiv:2509.18486) does not discuss IR-graphs (grep of its TeX). No paper realizing a path or cycle as an IR-graph was found.
- **Not reached.** Journal versions (DAM 2022; DM 2022) are on ScienceDirect, which campaign rules deny; the arXiv final versions were read instead.
- **Registries** (`outputs/registry-screen.json`):
  - Lean Pool HEAD 01db1d70 is unchanged; its full untruncated tree has no hits.
  - OpenAI/math HEAD 4eaee875 is unchanged; neither its tree nor the cached preprints listing has hits.
  - Omega HEAD has moved to **e0da8fcc** (2026-11-05). Its complete D5, Problems and Library subtrees were fetched. The only hit, `Library/GraphInvariants/mynhardtroux2021irredundance.md`, was read: it cites the paper only for "minimal dominating ⇔ irredundant". There is no IR-graph result.
  - GitHub repository search: 5 queries, 0 results.
- **Campaign.** No credited or excluded family involves irredundance graphs. Other lanes mention irredundance only for Burcroff's α = IR question.
- **Exclusion checks.**
  - The source does not contain a gadget for this graph. Its realizations are 2K_2, 2P_3, double-spider sources and the disjoint-union construction.
  - Nothing follows from the source's lemmas, which only exclude small cases.
  - G is not a classical extremal graph on an order or density convention.
  - It is not a source-formula evaluation.
  - It is not a wording, domain or endpoint correction: the conjecture is stated for each n ≥ 3, and the obstruction is at n = 9, far beyond the proved cases n ≤ 5.

Remaining risk for reviewers: part (ii) on cycles remains open. Refuting the conjunction needs only part (i), but root may judge significance on (i) alone.

## 5. Statement correspondence for the Lean endpoint

The draft is `lean-packet/IRPathCounterexample.lean` (UNCOMPILED).

- `IsPrivateNbr G D v w := (w = v ∨ G.Adj v w) ∧ ∀ u ∈ D, u ≠ v → ¬(w = u ∨ G.Adj u w)` is the source's w ∈ N[v] − N[D − {v}].
- `Irredundant`, `IsIRSet` (irredundant and of maximum cardinality among irredundant Finsets) and `Swap G A B := ∃ u ∈ A, ∃ v ∈ B, G.Adj u v ∧ B = insert v (A.erase u)` are literal.
- `IRGraph G : SimpleGraph {D // IsIRSet G D}` takes `Adj := Swap`. Symmetry is **proved**: the IR-sets have equal cardinality (`swap_symm`, `swap_irrefl`). No symmetrisation is used, so adjacency is exactly the source's relation.
- `IsIRGraph H := ∃ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), Nonempty (IRGraph G ≃g H)`. Source graphs are finite simple graphs.
- The endpoint `mynhardt_roux_paths_cycles_conjecture_false` is `¬((∀ n, 3 ≤ n → ¬IsIRGraph (pathGraph n)) ∧ (∀ n, 5 ≤ n → ¬IsIRGraph (cycleGraph n)))`. It uses Mathlib's `SimpleGraph.pathGraph` and `SimpleGraph.cycleGraph`.
- Finite steps use kernel `decide`:
  - `no_irredundant_four` (126 sets) and `irredundant_three_iff` (84 sets);
  - `walk_injective`, `walk_card`, and `swap_walk_iff` (81 pairs).
- General steps are short Finset lemmas: heredity, the card bound via `Finset.exists_subset_card_eq`, and the IR-set characterisation.
- The isomorphism is `Equiv.ofBijective`, with `map_rel_iff'` from `swap_walk_iff` and `pathGraph_adj`.
- Expected Lean cost: low. If the kernel `decide` over `Finset (Fin 9)` is slow, the fallback is a proved-sound `Bool` checker on bitmasks. Witnesses are in the certificate JSON.
- Allowed axioms: propext, Classical.choice, Quot.sound. No `native_decide`.

## 6. Reproduction

Run each command separately, under `bash -c 'ulimit -v 2000000; timeout 100 python3 -I …'`:

- `scripts/irgraph.py 8`
- `scripts/irgraph_chunk.py <lane> 9 <lo> <hi>` over the chunks recorded in `outputs/irgraph-N9-chunks.jsonl`
- `scripts/verify_ir.py '<edge list>'`
- `scripts/certificate_350452.py outputs/certificate-350452.json` (sha256 of output 32b73b38…a27e)
- `scripts/lemma_check.py`
