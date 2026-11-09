# MathDB 355217: a counterexample to the strict middle-graph increase conjecture

Status: candidate (zero credit until root acceptance). Lean sources in `lean/MiddleOCD.lean` are an UNCOMPILED draft. This lane was not allowed to run Lean.

## 1. Source and exact statement

- MathDB 355217, "Strict middle-graph increase conjecture for outer-connected domination". The exact corpus line is in `../raw/355217.jsonl`; provenance and hashes are in `../results.json`.
- Primary source: F. Kazemnejad, B. Pahlavsay, E. Palezzato and M. Torielli, *Connected and outer-connected domination number of middle graphs*, arXiv:2206.15439. Only v1 exists (20 June 2022, checked 2026-11-03). PDF sha256 is `446c68bb…f9d7`; see `../sources/pdf-receipts.txt`.
- Source Definition 1.2 (after Cyman 2007): a dominating set S of G is *outer-connected* if G − S is connected. γ̃c(G) is the minimum cardinality of such a set.
- Source Definition 1.3: the middle graph M(G) has vertex set V(G) ∪ E(G). Two edges are adjacent if they share an endpoint, and a vertex is adjacent to an edge if it is incident with it. No two vertices of G are adjacent in M(G).
- **Source Conjecture 7.1** (Section 7, "Open problems"): *Let G be a graph of order n ≥ 2. Then γ̃c(G) < γ̃c(M(G)).* MathDB reproduces this statement word for word.

The authors support the conjecture with trees (their Corollary 4.5) and with K_n, W_n, F_n, K_{n1,n2} and C_n (their Theorems 4.8 and 4.10–4.13).

**Domain remark.** Literally, the conjecture fails for the edgeless graph on 2 vertices. Then M(G) = G, so γ̃c(G) = γ̃c(M(G)) = 2. This is a trivial domain defect and we claim nothing for it. The counterexample below is **connected**, so it refutes the intended statement as well as the literal one. Section 4 of the source works only with connected graphs.

## 2. The counterexample

Let G8 have vertex set {0,…,7} and these 11 edges:

    01 06 16 | 23 27 37 | 46 47 56 57 | 67

So G8 consists of two triangles {0,1,6} and {2,3,7}, the hub edge 67, and two "twins" 4 and 5, each adjacent to both hubs 6 and 7. G8 is connected.

**Claim A.** γ̃c(G8) = 4.

*Upper bound.* Take S = {0,2,4,5}. Vertex 1 is dominated by 0, vertex 3 by 2, and vertices 6 and 7 by 4. The complement {1,3,6,7} contains the path 1–6–7–3, so it is connected.

*Lower bound.* Let S be an outer-connected dominating set (OCD set) with |S| ≤ 3. The complement R = V − S is non-empty.

- If 6 ∉ S and 7 ∉ S: the closed neighbourhoods of 4 and 5 are {4,6,7} and {5,6,7}, so 4, 5 ∈ S. The sets N[0] and N[1] lie inside {0,1,6}, so S meets {0,1}. Likewise S meets {2,3}. Then |S| ≥ 4, a contradiction.
- If 6 ∈ S and 7 ∉ S: then 7 ∈ R. If some a ∈ {0,1} were in R, its neighbours in R would lie in {0,1}. Its component in G − S would then miss 7, contradicting connectivity. So 0, 1 ∈ S. Vertex 2 needs a dominator in {2,3,7}, and 7 ∉ S, so S meets {2,3}. Then |S| ≥ 4.
- The case 7 ∈ S, 6 ∉ S is symmetric.
- If 6, 7 ∈ S: the graph G − {6,7} has components {0,1}, {2,3}, {4} and {5}. So the connected set R lies inside one of them and |R| ≤ 2. Then |S| ≥ 6.

**Claim B.** γ̃c(M(G8)) = 4.

*Lower bound.* This is the source's Theorem 4.1, γ̃c(M(G)) ≥ ⌈n/2⌉, and it uses only domination. In M(G) the vertex nodes are pairwise non-adjacent. A vertex node dominates one vertex node (itself), and an edge node dominates exactly its two endpoints. So any dominating set of M(G) has at least n/2 = 4 elements.

*Upper bound.* Take D = {m01, m23, m46, m57}, the edge nodes of the perfect matching F = {01, 23, 46, 57}.

- D dominates M(G8). Every vertex v lies on its matching edge, and every edge e shares an endpoint with the matching edge of either of its endpoints (or is that edge).
- M(G8) − D is connected. It contains every vertex node and the edge nodes of G8 − F = {06, 16, 56, 67, 27, 37, 47}. That edge set is a spanning tree of G8: 0, 1, 5 and 7 hang off 6, and 2, 3 and 4 hang off 7. Each remaining edge node is adjacent to both of its endpoints.

Hence γ̃c(G8) = 4 = γ̃c(M(G8)), and the strict inequality of Conjecture 7.1 fails. ∎

Both claims hold whichever convention is used for the empty graph in "G − S is connected". Every set used in the upper bounds has a non-empty complement. The lower bounds use only domination, or complements with at least 5 vertices.

## 3. Structural explanation and an infinite family

**Lemma.** For n even, γ̃c(M(G)) = n/2 if and only if G has a perfect matching F such that the spanning subgraph G − F is connected.

*Proof.* For (⇐), argue as in Claim B. For (⇒), let D be an OCD set of M(G) with |D| = n/2. By the counting argument, each element of D dominates two vertex nodes and no vertex node is dominated twice. So D consists of the edge nodes of a perfect matching F. Then M(G) − D is connected, and so G − F is connected: contract each edge node onto an endpoint. ∎

**Family.** Let a, b ≥ 1. Let G_{a,b} consist of a hub edge xy, twins t and u adjacent to both x and y, a triangles x α_i β_i at x and b triangles y γ_j δ_j at y. So n = 2a + 2b + 4. Then

γ̃c(G_{a,b}) = n/2 = γ̃c(M(G_{a,b})).

The M side follows from the Lemma with F = {tx, uy, α_iβ_i, γ_jδ_j}. The G side repeats the four-case argument of Claim A. Without the hubs, S ⊇ {t, u} and S meets every triangle pair, giving at least a + b + 2. With x but not y, S ⊇ {x} ∪ all α, β, plus one vertex per y-triangle, giving at least 2a + 1 + b ≥ a + b + 2. With both hubs, at most two vertices lie outside S. G8 = G_{1,1}. The family was also checked by brute force for 1 ≤ a, b ≤ 3 (`family.py`, log `../logs/family355217.log`).

## 4. Search record (diagnostic, not part of the proof)

`ocd.py` ran exhaustively over all connected graphs of order 2 ≤ n ≤ 8: 1, 1, 2, 6, 21, 112, 853 and 11117 graphs. The graphs came from a pure-Python canonical augmentation generator, `../scripts/graphgen.py`. Its counts match OEIS A000088 and A001349 for n ≤ 8. Connected graphs with γ̃c(G) < ⌈n/2⌉ were decided by the source's Theorem 4.1. Every other graph was checked by exhaustive subset search of M(G) up to size γ̃c(G).

Result: there is no counterexample of order ≤ 7, and G8 is the **unique** connected counterexample of order 8. It is a case of equality, so no connected graph of order ≤ 8 has γ̃c(G) > γ̃c(M(G)). `verify_witness.py` is an independent set-based verifier. It reproduces γ̃c(G8) = γ̃c(M(G8)) = 4, finds exactly two minimum OCD sets of M(G8), and finds 8 minimum OCD sets of G8.

## 5. Credit checks (for root)

- **Source's own theorems.** No source theorem or family violates 7.1. Every family the source computes satisfies the strict inequality. The source's ⌈n/2⌉ lower bound (Theorem 4.1) and its matching set for K_n (Theorem 4.8) are standard ingredients. The new content is a graph whose own γ̃c already reaches n/2, together with the Lemma in Section 3. The source has neither.
- **Classical example?** G8 is not Petersen, Heawood, Clebsch, Paley, Kneser or complete multipartite. It does not sit on an order or density convention: it is connected, and the edgeless defect is separate.
- **Current version.** arXiv:2206.15439 has only v1. The authors' later paper arXiv:2308.02127 (v1, 4 August 2023, on total outer-connected domination of middle graphs) cites 2206.15439 as an arXiv preprint and does not discuss Conjecture 7.1.
- **Prior art (bounded).** Three web searches on 2026-11-03 found no counterexample, citation or published version that changes the conjecture. They covered the conjecture wording, the title with "journal", and 2024–2026. The live Omega trureturing tree was screened at HEAD e73ca9e3ea14ce3adf84a6ec9d0a7fd5fcd3dd66 (2026-11-03T20:22Z), covering the full recursive D5 (13787 entries), Problems (1700) and Reg (3619) trees. The openai/math HEAD is 4eaee87548250b2682affda7d05d947c05554bae, unchanged; its preprints listing was cached by fresh-corpus-r10. Neither registry has a middle-graph or outer-connected-domination entry. Not done: Google Scholar, MathSciNet and zbMATH citation searches (no access); root should run them.
- **Significance (honest).** The conjecture comes from a short 2022 arXiv paper in a niche area. It is human-posed, not automatically generated. The refutation is an 8-vertex graph with an exact, kernel-checkable certificate, and it extends to an infinite family. Root decides whether this meets the significance bar.

## 6. Lean plan (statement correspondence)

`lean/MiddleOCD.lean` (UNCOMPILED) contains the following.

- `IsDominating`, `IsOCD` and `IsOCD'` are the literal Definition 1.2. `IsOCD` uses `Preconnected` and so allows an empty complement. `IsOCD'` uses `Connected`.
- `ocd` and `ocd'` are defined as `sInf` of the attainable cardinalities.
- `middle G : SimpleGraph (W ⊕ G.edgeSet)` is the literal Definition 1.3.
- `Conjecture71` and `Conjecture71'` quantify over every finite type W and every `SimpleGraph W` with `2 ≤ card W`. `Conjecture71Connected` is the intended connected form.
- The endpoints are `conjecture71_false`, `conjecture71'_false` and `conjecture71Connected_false`.

Proof architecture:

- Generic lemmas:
  - `reach_of_parent` and `connected_of_parent`: a parent map plus a decreasing depth certifies connectivity of an induced subgraph.
  - `not_preconnected_of_closed`: a closed set separates two vertices.
  - `two_mul_card_ge_of_dominating_middle`: the vertex-node counting.
  - `dominating_middle_of_mate`: a perfect matching dominates M(G).
- Concrete certificates on `Fin 8`:
  - The lower bound for G8 is a kernel `decide` over all subsets of size ≤ 3 (`badCert`; a PERF risk). The fallback is the four-case hand argument of Claim A.
  - The connectivity of M(G8) − D uses a spanning-tree parent map. Edge nodes go to their shallower endpoint (`lowEnd`, via `Sym2.lift`).

Expected axioms: propext, Classical.choice, Quot.sound. Lines marked PERF may need `fin_cases`/`simp` fallbacks if kernel `decide` is slow. A root or Sol worker must compile and repair the file, then run the strict extracted replay and `#print axioms`.
