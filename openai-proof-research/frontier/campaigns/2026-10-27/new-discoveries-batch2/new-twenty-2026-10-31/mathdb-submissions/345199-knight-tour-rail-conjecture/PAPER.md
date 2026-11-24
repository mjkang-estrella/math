# Closed knight's tours without rails: a counterexample family to Parberry's Rail Conjecture

MathDB 345199. Lean-verified (see §8 and LEAN-SOURCE-APPENDIX.md).

**Provenance.** The first refutation was found by GPT-6.1 Sol: a periodic family of closed tours on the boards n = 252 + 24t, each with exactly 104 rails. A Claude Opus 5.5 cross-model review confirmed that family mathematically, but it was not formalized. The zero-rail family below, its SAT-found template and the Lean proof are by Claude Opus 5.5. The final pre-publication check was also done by Claude Opus 5.5, so it is not independent of the packager by model family.

## 1. The problem

**Source.** Ian Parberry, *Tourneys and the Fast Generation and Obfuscation of Closed Knight's Tours*, arXiv:2001.06044v1 (2020).

**Definitions, verbatim from the source.**

§2: "For all n ∈ N, the n × n knight's graph K_n is a labeled undirected bipartite graph with n² vertices, one for each square (also called a cell) of an n × n chessboard, and an edge between vertices u and v iff a knight can move from cell u to cell v." The displacements are "M = {(±x, ±y) | x, y ∈ {1, 2} and x + y = 3}". "A knight's tour is a Hamiltonian cycle on a knight's graph."

§4: "A rail in a subgraph G = (V, E) of a knight's graph K consists of a pair of parallel moves between cells that are separated by knights moves that are not present in G, that is, an unordered pair of edges r = (e, e′) such that e = (v0, v1) ∈ G, e′ = (v2, v3) ∈ G, and (v0, v2), (v1, v3) ∈ K \ G."

**Conjecture, verbatim (§4, p. 9).** "Conjecture. (The Rail Conjecture) An n × n knight's tour has Ω(n) rails."

**MathDB record 345199.** "Let an n × n knight's tour be a closed knight's tour on an n × n board, and let a rail be the structure defined by the preceding discussion: a pair of edges that can be switched with their complementary pair while preserving vertex degrees. Rail Conjecture. An n × n knight's tour has Ω(n) rails."

**Reading of Ω(n).** The standard reading is: there are c > 0 and N such that every closed knight's tour of an n × n board with n ≥ N has at least c·n rails. A single tour cannot refute an asymptotic statement. A refutation needs, for every c > 0 and every N, a board n ≥ N and a tour with fewer than c·n rails. Equivalently, it needs an infinite family of tours whose rail count is o(n).

This is the reading (Knuth's) used throughout the source, e.g. "K_n has 4n² − O(n) edges" and the O(n²) running times. Under the Hardy–Littlewood reading of Ω ("not o(n)"), a refutation would need few-rail tours for *all* large even n. The family below covers only n ≡ 4 (mod 8), and the Sol family only n ≡ 0 (mod 12), so neither settles that reading. Nothing in the source suggests it was meant.

**Rails as Parberry computes them.** Parberry's Algorithm 1 (FindRails) enumerates, for each cell u and each downward tour edge (u, v), the downward cross moves j ≠ km(u, v), and keeps the pair if (u + j, v + j) is a tour edge while (u, u + j) and (v, v + j) are not. The final checker transcribed this algorithm and the literal condition below into a script. On 23 closed tours (six 6 × 6, five 8 × 8, five 10 × 10, two 12 × 12; 4 to 85 rails each), the two counts give the same set of rails.

## 2. Result

**Theorem.** For every t ≥ 0 there is a closed knight's tour of the (60+8t) × (60+8t) board with **no rails at all**. Consequently the Rail Conjecture is false: for every c > 0 and N there are n ≥ N and a closed knight's tour of the n × n board with fewer than c·n rails.

The rail count is zero under the literal source condition, which does not even require the two edges to be parallel. It is therefore zero under every narrower reading, including "parallel moves" and the MathDB paraphrase "a pair of edges that can be switched with their complementary pair while preserving vertex degrees". Rails are counted as unordered pairs {e, e′}, with every labelling (v0, v1, v2, v3) allowed.

## 3. The construction

**Coordinates and moves.** Cells are (x, y) with 0 ≤ x, y < n. The eight knight moves are numbered 0–7: (1,2), (2,1), (2,−1), (1,−2), (−1,−2), (−2,−1), (−2,1), (−1,2). Move d+4 (mod 8) is the negation of move d.

**Reference board.** The data is one 2-factor E₀ of the 60 × 60 knight graph, i.e. a spanning subgraph in which every vertex has degree 2. It is given by a table T(x, y, d) ∈ {0, 1}, with T(x, y, d) = 1 iff the edge from (x, y) along move d is in E₀. E₀ is itself a Hamiltonian cycle. Its table is periodic in both coordinates on the strip [6, 54):
- T(x, y, d) = T(x+8, y, d) whenever 6 ≤ x and x+8 < 54, for all y;
- T(x, y, d) = T(x, y+8, d) whenever 6 ≤ y and y+8 < 54, for all x.

E₀ was found as follows. A z3 SAT search produced a 36 × 36 template with zero rails, closed horizontal bands of height 8 in the periodic region, and every strand advancing by exactly one period (8 columns or 8 rows). E₀ is the 60 × 60 member of the family below built from that template. The solver plays no role in the proof: every property of E₀ used below is checked exhaustively. The data is in `data/E60.json` (SHA-256 `81e1dc98…f7f`) and in `src/RailData.lean`.

**The family.** For a side m = 60 + 8t define the coordinate map

τ_m(x) = x if x < 14; x − (m − 60) if x ≥ m − 14; 14 + ((x − 14) mod 8) otherwise.

On the m × m board, cells u and v = u + move d are joined iff T(τ_m(u), d) = 1 or T(τ_m(v), −d) = 1, where τ_m acts on each coordinate. Informally, board m is the reference board with its middle period of 8 columns and 8 rows repeated t more times. Call this graph H_m. Each edge is a knight move, so H_m is a subgraph of K_m. The same rule on an m × n rectangle, with τ_m on x and τ_n on y, defines H_{m,n}; §4.4 uses these rectangles. τ_60 is not the identity on [14, 46), but by periodicity H_60 = E₀ (checked directly by the final checker).

## 4. The proof

### 4.1 The view lemma

Call coordinates a and b *equivalent* if a = b, or if both lie in [6, 54) and a ≡ b (mod 8). By periodicity, T takes the same values at equivalent positions. A short case analysis of τ (the axis lemma) gives the following. For every cell x of a side-m board and every offset |δ| ≤ 8:
- x + δ is on the board iff τ_m(x) + δ ∈ [0, 60);
- if it is on the board, τ_m(x + δ) is equivalent to τ_m(x) + δ.

Hence, around any cell u, the board H_m looks exactly like the reference board around τ_m(u) up to distance 8. More precisely, for offsets within 8, the pair (u + δ₁, u + δ₂) is an edge of H_m iff (τ_m(u) + δ₁, τ_m(u) + δ₂) is an edge of E₀ (*view lemma*).

Two further *views* hold:
- near the left edge (or top edge), every board coincides with the reference up to periodicity for all coordinates below 54;
- the 60-board is its own view everywhere.

A walk in E₀ that stays inside a view box is carried to a walk in H_m (path transfer).

### 4.2 Degree two

The reference E₀ has exactly two edges at every cell (finite check). By the view lemma with radius 2, the edges of H_m at a cell u correspond bijectively to the edges of E₀ at τ_m(u). So every vertex of H_m has degree 2.

### 4.3 No rails

Let e = (v0, v1) and e′ = (v2, v3) be edges of H_m, and let v0v2 and v1v3 be knight moves. Write
v1 = v0 + a, v3 = v2 + e, v2 = v0 + b, v3 = v1 + c,
with a, b, c, e knight moves. Then a + c = b + e. A check over all 8⁴ combinations shows that one of three things holds:
- b = a: then v2 = v1, so (v0, v2) = e is in the graph;
- c = −a: then v3 = v0, so (v1, v3) = e is in the graph;
- c = b and e = a: the four cells form a parallelogram.

The first two cases contradict the requirement that both cross pairs be absent. In the parallelogram case the four cells lie within distance 4 of v0. By the view lemma the configuration is a parallelogram rail of E₀ at τ_m(v0), and an exhaustive check shows E₀ has none. So H_m has no rail in the source's sense.

### 4.4 Connectivity by period insertion

Connectivity is the essential point, since a 2-factor with many cycles would refute nothing. It is proved by induction on the board size, not by any structural description of the cycle.

*Column insertion.* Let H′ be the board with 8 more columns (side m + 8 in x, same height n). Map ι(x, y) = (x, y) if x < 22, and (x + 8, y) otherwise. Two facts make the argument work:
- ι preserves τ, so every edge of H that does not cross the cut x = 22 is an edge of H′.
- The two local conditions below hold. Each is a finite check on E₀ by explicit walks in the window 6 ≤ x < 54, |Δy| ≤ 8, transferred to H′ by the left-aligned view in x and the anchored view in y:
  - (cross) for every edge (a, b) of E₀ with 20 ≤ a.x < 22 ≤ b.x, there is a walk in E₀ from a to b + (8, 0) inside the window. In H′ this walk replaces the crossing edge.
  - (strip) every cell with 22 ≤ x < 30 has a walk inside the window to a cell outside the strip.

If H is connected, then H′ is connected: the images of H's cells are mutually reachable through these replacement walks, and every new cell reaches an image.

*Row insertion.* This is done only at width 60, at the cut y = 24 with window rows [6, 54); the views in x are exact. The crossing condition is again checked by explicit walks. The strip condition follows from the descent table of §4.5: descending from a cell of the inserted rows, the first cell outside them lies within two rows.

*Base case and induction.* The 60 × 60 board is E₀ up to periodicity. It is connected because each cell other than (0, 0) has a neighbour with smaller position along its Hamiltonian cycle; the position table is part of the data and is checked. Row insertions give connectivity of every 60 × (60+8s) board, and column insertions then give every (60+8t) × (60+8s) board. In particular every square board of the family is connected.

### 4.5 Hamiltonian cycle and the edge set

H_m is a connected graph in which every vertex has degree 2. Hence it is a single cycle through all m² cells, a Hamiltonian cycle of K_m (Mathlib: `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`). Let p be that cycle, viewed as a closed walk in K_m. The edge set of p is all of H_m:
- its m² edges are distinct and lie in H_m;
- by the handshake lemma, H_m has exactly m² edges.

So the rails of the tour p are the rails of H_m, of which there are none (§4.3).

### 4.6 Refutation

Given c > 0 and N, take t = N and n = 60 + 8N ≥ N. The tour p on the n × n board has 0 < c·n rails, contradicting "≥ c·n". ∎

## 5. The finite certificate

Every finite fact is a Boolean computation evaluated by the Lean kernel (`decide +kernel`); no unchecked evaluation (`native_decide`) is used:

| Fact | Size | Compile time (clean build) |
|---|---|---|
| x and y periodicity of T on [6, 54) | 2 × 19,200 table comparisons | 12 s together |
| degree 2 on the 60 × 60 reference | 3,600 cells, 12 chunks | 38 s |
| no parallelogram rail on the reference | 3,600 cells × 64 move pairs, 30 chunks | 41 + 42 + 46 s |
| descent table (base connectivity, row strip) | 3,600 cells, 12 chunks | 27 s |
| column-crossing walks (≤ 56 steps) | 60 rows × 2 columns | 19 + 16 s |
| column-strip walks (≤ 15 steps) | 480 cells | 18 s |
| row-crossing walks (≤ 472 steps) | 2 rows × 60 columns, one column per chunk | 40 + 2 + 43 s |
| 4-cycles of knight moves are parallelograms or degenerate | 8⁴ cases | < 1 s |

The standalone kernel checker (`leanchecker`) re-verified every module, with similar times (see `clean-rebuild.log`).

Each check was first prototyped in Python (`scripts/mirror.py`, `scripts/insertion_check2.py`). Independently of Lean, `scripts/family.py` builds the boards from the 36 × 36 template directly. For n = 36, 44, …, 100 every board is a single Hamiltonian cycle with 0 rails, counted with the literal source condition. The Lean family starts at 60, not 36, because the insertion windows need the margins of the 60-board. The final checker wrote its own constructor from `data/E60.json` and the map τ_m alone. For n = 60, 68, 76 and 84 it found a single Hamiltonian cycle with 0 rails, under both the literal condition and Parberry's Algorithm 1.

## 6. Significance and limits (honest assessment)

- **What the refutation needs.** The conjecture is asymptotic, so no finite search refutes it. Zero-rail tours on single small boards (10×10, 12×12, 16×16, 20×20) are easy to find with a SAT solver, so the conjecture was "false in spirit" for anyone who ran such a search. The cross-model review reports that no rail-free 2-factor exists on 6×6 or 8×8 (z3, UNSAT), so 10 is the smallest side. The content of this result is an *infinite* family with a uniform proof of Hamiltonicity.
- **Comparison with the earlier proof.** It is stronger than the first refutation (GPT-6.1 Sol: 104 rails on n = 252 + 24t, confirmed by review but not formalized): **zero** rails on every member, and a family starting at n = 60. Both families rest on the same idea: a periodic rail-free bulk plus a proof of Hamiltonicity that is uniform in n.
- **What is new.** The one ingredient beyond computation is the connectivity argument by local period insertion. It turns Hamiltonicity of a periodic family into finitely many checks on one reference board. It is a variant of the classical technique of extending knight's tours by strips of columns (e.g. Schwenk's 1991 classification of rectangular boards with closed tours). Here it is applied to a template whose strands advance by exactly one period, and a SAT search found the template with exactly that requirement.
- **Weight.** A skeptical specialist could fairly call the combinatorics engineering: a SAT-found periodic template plus a general-purpose induction. The conjecture itself is a niche question from a 2020 arXiv preprint. Its interest is mainly that Parberry's join and shatter algorithms rely on rails being plentiful, and this result shows that a closed tour can have none at all.

## 7. Prior art (from the adversarial review)

- **Source status.** arXiv:2001.06044 has only v1; §8 lists "a proof (or counterexample to) the Rail Conjecture" as open. No journal version was found (author page, DBLP).
- **Registries.** Principia, mio-math, openai-math and omega clones: no hit for `2001.06044` or `345199`. Omega issues and PRs for "2001.06044", "rail conjecture knight" and "Parberry tourney" returned empty.
- **Web search.** Extended web search turned up only the source. One citing work (Nascimento–Brasil, genetic operators for knight's tours, 5 ≤ n ≤ 20) could not be opened at its publisher (access denial respected). Its public thesis version is an evolutionary tour generator for small boards and does not address the asymptotic rail count.
- **Refresh (final check, 2026-11-21).**
  - arXiv abs page: still v1 only (16 Jan 2020).
  - Parberry's tourneys page (ianparberry.com/research/tourneys/, "Last updated May 31, 2020") has no update on rails. The README of his Tourney repository (github.com/Ian-Parberry/Tourney, last push 2024-11-07) does not mention rails or the conjecture.
  - Omega issues and PRs for "2001.06044", "rail conjecture knight", "Parberry knight tour" and "345199": all empty.
  - `gh search code` for "2001.06044" and "rail conjecture": both empty.
  - ReuF2F (cmu-l3/reuF2F, 244 test problems plus validation): no knight's-tour, rail or Parberry entry.
  - Principia (backup clone and `principia-ids.txt`), mio-math, openai-math and omega clones: no hit for 2001.06044, 345199, "rail conjecture" or Parberry.
  - Extended web search: only the source, plus unrelated knight's-tour papers (minimum turns and crossings, arXiv:1904.02824; whirling tours, arXiv:2605.04603).
- **Coverage gap.** The citation traversal is incomplete: OpenAlex and Semantic Scholar returned HTTP 429. No prior refutation was found. This is not a worldwide novelty clearance.

## 8. Formal verification

- **Endpoint.** `Rail.rail_conjecture_false : ¬ RailConjecture`, together with the explicit form `Rail.rail_conjecture_false'` and the family theorem `Rail.tours_without_rails`.
- **Definitions.** `RailConjecture` is stated with Mathlib's `SimpleGraph.Walk.IsHamiltonianCycle` on the literal knight graph `knightGraph n`. Rails are counted with the literal source condition `IsRail` over unordered pairs (`Sym2`).
- **Axioms.** `propext`, `Classical.choice`, `Quot.sound` only.
- **Toolchain.** Lean 4.34.1 with the pinned Mathlib; 27 modules, 1,964 lines (431 of them generated data and chunked check statements); see REPORT.md for receipts.
