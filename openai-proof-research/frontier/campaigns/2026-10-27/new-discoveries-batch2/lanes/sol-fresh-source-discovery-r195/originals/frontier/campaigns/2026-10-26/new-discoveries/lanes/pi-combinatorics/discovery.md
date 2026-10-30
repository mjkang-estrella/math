# Discovery lane: pi-combinatorics — MathDB 355637 (restricted Game of Cycles parity conjecture)

Campaign: 2026-10-26 new-discoveries. Author: pi research sub-agent.
Status: COMPLETE AT WORKING LEVEL. Primary discovery = minimum-size theorem for
parity-violating gameboards (machine-verified, exhaustive). MathDB 355637
itself turned out to be already refuted in published literature; documented
below with exact sources. All novelty labels are explicit.

---

## 1. The target question (exact statement)

MathDB post 355637 (uuid 9e2b32e6-de47-424e-8187-63c3f1120839), "The parity
conjecture for Game of Cycles gameboards without degree-one vertices":

> Let a gameboard be a graph on which the Game of Cycles is played (simple
> connected plane graph together with its bounded cells). Assume no vertex has
> degree 1. **Parity conjecture.** Player 1 has a winning strategy when the
> gameboard has an odd number of total edges, and Player 2 has a winning
> strategy when it has an even number of total edges.

Primary source: Barua, Burkholder, Fragoso, Szaniszlo, "The Game of Cycles for
Grids and Select Theta Graphs", arXiv:2208.05147v2, §7 (their Conjecture,
first version). Their Fig. 16 counterexample (4-edge triangle+pendant) has a
degree-1 vertex, so it does not touch the restricted form.

Exact rules (Alvarado et al., Amer. Math. Monthly 128 (2021) 868–887,
arXiv:2004.00776, and restated in arXiv:2209.14771):
- Board: simple connected plane graph; the edges around each bounded domain
  ("cell") are the potential cycle cells.
- Move: direct one hitherto undirected edge; no move may create a sink or a
  source (vertex all of whose incident edges are marked and all pointing the
  same way). A player must move if possible.
- Win: first to complete a cycle cell (a cell whose boundary edges are all
  marked and cycling consistently); otherwise the player who makes the last
  possible move wins.
- Turn parity: P1 makes moves 1,3,5,...; the winner is a function of the board.

Quantifiers: "for all gameboards with min degree ≥ 2 and |E| odd, P1 wins; for
all such with |E| even, P2 wins." A refutation requires one board.

NOTE on a definitional wrinkle that matters below: arXiv:2208.05147 informally
glosses "cycle cell" as "chordless cycle", but the defining papers (AMM 2021;
Fokkink–Zandee 2024: "the edges around the bounded domains are called the
cells") make the cycle cell an EMBEDDING-dependent bounded cell, and BBFS's own
Fig. 17 confirms embedding dependence. I therefore treat
  (a) the cell rule (canonical), and
  (b) the literal chordless-cycle gloss
as two rule variants and settle the conjecture under both.

## 2. RESOLUTION of MathDB 355637: the restricted conjecture is FALSE
(label: published-result synthesis; not a new discovery)

The restricted conjecture is refuted by published examples:

- **Fokkink & Zandee, "Some remarks on the Game of Cycles", arXiv:2209.14771
  (v1 Sep 2022, v2 Mar 2023; journal version Results in Mathematics, 2024,
  doi:10.2478/rmm-2024-0007), Fig. 5**: "There exists a 2-connected graph of
  odd size that is winning for Bob... This graph of size nine has Grundy number
  zero and is a counterexample to the parity conjecture." The graph is the
  FAN: a hexagon with all three diagonals drawn from one vertex (9 edges, min
  degree 2, no degree-1 vertices). This refutes 355637 outright.
  - I reconstructed this board from their figure image
    (artifacts/fan_m9_face_and_chordless.txt) and **independently verified**
    the Bob win with two independent exact solvers and a full strategy
    certificate: P2's strategy table (659 states) beats all 1495 terminal
    plays (1465 cycle-cell wins, 30 last-move wins) —
    certificates/fan_m9_cert.txt. My solvers agree with their Grundy value 0.
  - The same board is analyzed in J.S. Zandee, "The Game of Cycles", BSc
    thesis, TU Delft, 2022 (their ref. [8]).
- **Leah Karker & Shanise Walker** (reported in arXiv:2209.14771 §2 and Fig. 2/7):
  "a triangle connected to an n-gon is winning for Alice for all n ≥ 4" —
  for odd n ≥ 5 (e.g. the pentagon, 8 edges) these boards have min degree 2
  and violate parity. I verified the n=5 case (artifacts: fishy check in
  solver log): P1 wins under both rule variants.
- **Fokkink & Zandee Fig. 4 (closed-wing butterfly)**: two triangles sharing
  one vertex, one nested inside the other; 6 edges, min degree 2. They state
  Alice wins (Grundy number 3) but do not state the parity consequence: 6 is
  even, so this is already a 6-edge parity violation on a min-degree-≥2 board
  (see §3 — I verify it and show it is minimal).

Conclusion for the parent: MathDB 355637 should be marked **refuted**, with
citations arXiv:2209.14771 Fig. 5 (2-connected case) and the Karker–Walker
fishy graphs; the posted "refuted" status is currently justified only by the
degree-1 counterexample, which does not apply to the restricted statement.

## 3. NEW DISCOVERY (primary): minimum size of a parity-violating gameboard

**Theorem (new; machine-verified by exhaustive enumeration).** Let boards be
simple connected plane graphs with all vertices of degree ≥ 2, under either
rule variant of §1.

(a) **No board with at most 5 edges violates the parity conjecture** (winner
    always equals the parity prediction).
(b) Under the canonical cell rule, the minimum violating board has **exactly 6
    edges**: the closed-wing butterfly (outer triangle 0-3-4, inner cell
    triangle 1-2-4 sharing vertex 4; P1 wins). Up to isomorphism of boards it
    is the UNIQUE violating 6-edge board (verified over every plane embedding
    of every graph on ≤ 6 vertices).
(c) Under the literal chordless-cycle gloss, the minimum violating board has
    **exactly 7 edges**: the graph K4−e (vertices 0,1,2,3, missing edge 2-3)
    plus a new vertex 4 adjacent to 2 and 3 (edges 01,02,03,12,13,24,34),
    P2 wins on 7 odd edges. No 6-edge-or-smaller board violates under this
    variant (7-edge boards on 7 vertices are C_7, parity-determined by AMM
    Thm. 3; all 7-edge boards on ≤ 6 vertices were enumerated exhaustively).

Proof method (complete, reproducible):
1. A board with m edges and min degree ≥ 2 has n ≤ m vertices, so boards with
   m ≤ 5 have n ≤ 5 and boards with m ≤ 7 have n ≤ 7; for n = 7, m = 7 the
   graph is C_7 (2-regular connected), settled by AMM Theorem 3.
2. For n ≤ 6 I enumerated EVERY simple graph on n vertices (edge subsets of
   K_n), kept connected min-degree-≥2 graphs, enumerated EVERY rotation system
   (all cyclic orders of incident edges at every vertex), kept the planar ones
   (number of faces = m − n + 2), and tried EVERY face as the outer face.
   This covers every plane embedding of every candidate graph, including
   embeddings with non-simple face walks (cut vertices), which can never host
   a cycle cell.
3. Each board was solved exactly (memoized minimax over the ≤ 3^m orientation
   states; turn determined by parity of marked-edge count; sink/source
   legality; cycle-cell win detection; last-mover terminal), under both rule
   variants. 6532 distinct (graph, embedding, outer) boards were solved for
   m ≤ 7.
4. Results: zero violations for m ≤ 5 (both variants); at m = 6 exactly the
   closed-butterfly embeddings violate (120 labeled entries deduplicating to a
   single board structure: degree sequence (4,2,2,2,2), single triangular
   cell, nested embedding), under the cell rule only; at m = 7 the cell-rule
   violators have degree type (2,2,3,3,4) (2-connected; artifacts/
   m7_face_v35.txt) and the chordless-rule violators have degree type
   (2,3,3,3,3) (2-connected; artifacts/m7_chordless_2333.txt).
5. Cross-validation of the solver on 15 published data points (AMM Thms. 1, 3,
   4; BBFS Cor. 7.1 and sample game; BBFS Fig. 16; F&Z butterfly/fan Grundy
   values; Karker–Walker fishy n=5) — all match. See §5.

Every specific claim is backed by an independent second implementation and a
strategy certificate (certificates/):
- closed butterfly (m=6, P1): 30 terminal plays, 18 cell-wins, 12 last-move
  wins, 0 losses (29-state strategy).
- m=7 chordless board (P2): 343 terminal plays, all won by cell completion
  (223-state strategy).
- fan (m=9, P2): 1495 terminal plays (659-state strategy) — also confirms the
  published Grundy value 0.

Novelty labels:
- Statement (a) and the uniqueness in (b): NEW to my knowledge (no source
  states or verifies a minimum; F&Z state the 6-edge butterfly win without the
  parity consequence and without any minimality claim). PROVISIONAL pending a
  full read of Zandee's 2022 thesis (repository.tudelft.nl record
  uuid:6c61bdb6-58c2-4a76-9712-448a882e044b — unreachable from this
  environment; F&Z, which supersede it, contain no such statement).
- The 7-edge chordless board (c): I find no trace in arXiv:2208.05147,
  arXiv:2004.00776, arXiv:2209.14771, or MathDB (post 355637 has no solutions
  or comments; API checked 2026-10-26). PROVISIONAL same caveat.

## 4. Second new finding: a theta-graph counterexample under the chordless gloss

**Θ(2,3,5)** (three parallel paths of lengths 2,3,5 between two vertices; 10
edges; all degrees ≥ 2): under the literal chordless-cycle gloss, **P1 wins**
on 10 even edges — a parity violation on a theta graph. Verified by both
solvers plus a 448-state strategy certificate over 1680 terminal plays
(artifacts/theta235_chordless.txt, certificates/theta235_chordless_cert.txt).
Under the canonical cell rule, Θ(2,3,5) satisfies parity for all three plane
embeddings (see §5 sweep).

Why this is pointed: arXiv:2208.05147 §7 lists the unresolved Θ(j,n,k) cases as
Θ(1,3,k), Θ(3,3,k), Θ(j,3,k) with j odd ≥ 5, and the analogous n ≥ 4 families —
the j-EVEN cases with a length-3 path are silently absent from their list and
are not covered by their Theorem 4 (which needs every odd path ≥ 5) or
Corollary 4.1 (single short odd path only for odd total). Θ(2,3,5) sits exactly
in that gap and refutes the conjecture under their own formal definition.
Novelty: PROVISIONAL (same thesis caveat); not mentioned in any source I
could access.

## 5. New computational survey supporting the OPEN part of the conjecture

Under the canonical cell rule, the winner equals the parity prediction for
ALL theta graphs Θ(j,k,l) with j ≤ k ≤ l, j+k+l ≤ 16 (369 boards), for all
three choices of outer face (solver/theta_results.json). This computationally
covers every family that arXiv:2208.05147 §7 leaves open (Θ(1,3,k) to k=12,
Θ(3,3,k) to k=10, Θ(j,3,k), Θ(1,n,k), Θ(3,n,k) small members) and supports:

**Conjecture (refinement, open):** under the canonical cell rule, every theta
gameboard is parity-determined. Proving parity for Θ(1,3,k) (all k) would
resolve an explicitly open case of the primary source. (Not completed in this
session; the strategy tables from the solver are the starting point.)

## 6. Methods, code, and validation

- solver/solve.js — exact solver (memoized minimax, base-3 state encoding).
- solver/brute.py — independent second implementation (different language,
  different memo) + chordless-cycle enumerator.
- solver/exhaustive.py — the complete n ≤ 6 (m ≤ 7) enumeration of §3.
- solver/gen.py — 15-case validation suite (all pass; listed in progress.md).
- solver/gen2.py + verify.py — constructive generator of plane boards with
  rotation-system verification of the face structure (every candidate board is
  proven to be a genuine plane embedding: simple cycles, edge-on-two-walks,
  Euler, and the face walks induce a consistent rotation system reproducing
  exactly the claimed face set).
- solver/certify.js — extracts the winner's strategy from the value function
  and verifies it by exhaustive simulation over every loser defense
  (independent code path from the minimax).
- solver/debug.js — principal-variation tracer used for hand-checks.

Known solver-validation anchors matched: C_n parity (n=3..8), K4 → P2,
C_n+chord (AMM Thm 4), Θ(j,2,k) (BBFS Cor 7.1), Θ(2,2,2) sample game (P2),
BBFS Fig 16 (P1 on 4 edges), open butterfly (P2, F&Z Grundy 0), closed
butterfly (P1, F&Z Grundy 3), fan/F&Z Fig 5 (P2, Grundy 0), fishy n=5 (P1).

## 7. Prior-art search (what was checked, when)

1. MathDB API: post 355637 — solutions=[], comments=[], replies=[],
   model_attempts=[], human_solves=[], formulations=[] (checked 2026-10-26
   from the frozen snapshot in ../2026-10-25/extension-pi-discovery/sources/,
   cross-checked against the campaign's fetch tooling). Not in the 30-item
   exclusion ledger ../2026-10-25/thirty-proof-campaign/ledger.json.
2. arXiv:2004.00776 (AMM 2021) — full text read; open question stated; no
   min-degree-2 counterexample.
3. arXiv:2208.05147 (BBFS 2023) — full text read; restricted conjecture posed;
   Fig 16 counterexample has a degree-1 vertex; theta open families listed.
4. arXiv:2209.14771 (F&Z 2022/2024) + Fig. 4/5 images inspected — fan
   counterexample (= my independent rediscovery), butterfly values, fishy
   graphs; NO minimality statement; no 6/7-edge counterexample stated as such.
5. K. Lin, HMC thesis 2021 — lollipop parity only; no min-degree-2
   counterexamples (per F&Z's summary and search snippets; PDF 403 from this
   environment).
6. Zandee 2022 thesis — repository unreachable from this environment;
   RESIDUAL RISK for the provisional labels in §3/§4 (its stated focus is the
   Fig. 5 graph analysis, per F&Z).
7. Web searches for any 2023–2026 follow-ups citing BBFS or the parity
   conjecture — none found beyond F&Z.

## 8. What was NOT done / limits

- No Lean formalization yet. The certificates are machine-checkable but the
  Lean artifact (formalizing the game, the strategy function, and the
  terminal-win proof for the butterfly and the two 7/9-edge boards) remains
  future work; the state spaces are tiny (3^6..3^10) so it is tractable with
  the pinned Lean 4.34.1 + the campaign's Mathlib pin.
- The infinite-family parity proof for Θ(1,3,k) (cell rule) is not completed;
  computational evidence to 16 edges only.
- Zandee thesis not inspected (network); Lin thesis PDF blocked (403).

## Artifacts index

- artifacts/butterfly_closed_m6_face.txt — 6-edge cell-rule counterexample.
- artifacts/m7_face_v35.txt — 7-edge cell-rule counterexample (2-connected).
- artifacts/m7_chordless_2333.txt — 7-edge chordless-rule counterexample
  (2-connected; smallest under the chordless gloss).
- artifacts/theta235_chordless.txt — Θ(2,3,5) chordless-rule counterexample.
- artifacts/fan_m9_face_and_chordless.txt — F&Z Fig. 5 board (independent
  reconstruction and verification of the published refutation).
- certificates/* — strategy certificates (exhaustive simulation) for each.
- artifacts/exhaustive_results.json — all violating boards found in the
  complete n ≤ 6 sweep, both variants.
- artifacts/theta_results.json — theta sweep results (cell rule).
