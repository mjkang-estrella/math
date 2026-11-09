# CANDIDATE — expanded-corpus-r217

**No candidate is nominated.** None of the 20 reserved records produced a new, significant, exact
resolution that survives the campaign's exclusion rules. No Lean was written or run (Claude lane
restriction).

## Strongest parked leads (for a later lane)

### 1. 373718 — 2-tone 6-colourability of cubic Halin graphs (Bazzal–Togni, arXiv:2603.18674v1, Conjecture 3.1)

- **Evidence:** I checked every cubic Halin graph of order 6 to 28 exhaustively. That is all triangulations of the l-gon for l = 4..15 (742,900 at l = 15), and every one is 2-tone 6-colourable. Each colouring was re-verified independently.
- **Why no counterexample is expected:** the search stays easy (at most 11,421 backtracking nodes at n = 28).
- **Proof status:** the obvious induction (contract the deepest triangle {x, x1, xl} to a leaf) is *not* reducible. Of 120,000 admissible generic boundary colourings, 73,968 do not extend without recolouring (`scripts/halinreduce.py`).
- **What a proof needs:** either Kempe-type recolouring with a larger set of reducible configurations (fans, double triangles), or a global labelling scheme.
- **Lean cost if proved:** high. It needs a combinatorial model of plane Halin graphs, for example via polygon triangulations, plus a statement-correspondence bridge to "tree with no degree-2 vertices + cycle through the leaves in planar order".
- **Uncompiled Lean plan (only if a proof is found):**
  1. Define `CubicHalin l` as the dual graph of a triangulation of `Fin l` (a finset of triangles with the standard non-crossing axioms) plus the leaf cycle.
  2. Prove that `HalinGraph` (an embedded tree plus a cycle on its leaves) is equivalent to this model for cubic trees. This is the expensive bridge.
  3. State `TwoTone6 G := ∃ f : V → Finset (Fin 6), (∀ v, (f v).card = 2) ∧ (∀ u v, G.Adj u v → Disjoint (f u) (f v)) ∧ (∀ u v w, u ≠ w → G.Adj u v → G.Adj v w → f u ≠ f w)`. This is equivalent to Definition 1.1 for t = 2, because distance-2 pairs are exactly the pairs with a common neighbour and no adjacency, and adjacent pairs are already disjoint.
  4. Prove the inductive theorem.

### 2. 372424 — total isolation game two-thirds conjecture (Henning–Rall, arXiv:2601.03363v1, Conjecture 1)

- **Evidence:** exhaustive with no violation over all graphs of order ≤ 9 whose components have order ≥ 3 (273,623 graphs). Also clean on all trees of order ≤ 14 and on 50 exact unions of the only "Staller-start excess" components (both of order 5) up to order 15.
- **Proof status:** no proof route beyond the charging gap r131 identified (q ≤ 2e).
- **Lean cost:** a counterexample would be cheap (kernel minimax over 2^n states), but none exists in range.

### 3. 326025 — Cooper–Rowland weight-four size-one count

- **Evidence:** the formula matches my independent computation for every n = 9..27. The source only had n ≤ 20; my implementation was validated on the source's weight-2 and weight-3 formulas.
- **Lean cost:** a literal endpoint needs Whitehead peak reduction in Aut(F2). Infeasible here.

## Zero-credit literal failures found (not nominated)

- **373480 (Bérczi, Conjecture 7):** false at n = 2 and n = 4 for every Latin square, because matching permutations are derangements, so they have no odd cycle when n ≤ 4. It is also false at every n = 2^k for 2-group Cayley tables (e.g. Z_2^3 at n = 8, inside the author's tested range, where the author already flags possible "genuine absence"). These are smallest-order / classical-group defects. All 9,408 reduced Latin squares of order 6 *do* have an odd-cycle trade.
- **372834:** false for arrangements of at most 2 pseudolines (no triangles). This is a domain defect; the record is otherwise equivalent to the parked 372833.
