# Progress notes — pi-combinatorics lane (2026-10-26)

Incremental log of the session, newest last.

## Setup
- Target selected: MathDB 355637 (restricted parity conjecture, min degree ≥ 2).
  0 solutions/comments/model_attempts on MathDB; not in the 2026-10-25
  exclusion ledger. Rules pinned to AMM 2021 (arXiv:2004.00776) +
  BBFS (arXiv:2208.05147); interpretation wrinkle (chordless gloss vs. bounded
  cell) identified and tracked as two rule variants throughout.
- Toolchain: solver/solve.js (memoized minimax over 3^m orientation states),
  solver/brute.py (independent Python solver + chordless enumerator),
  solver/debug.js (PV tracer), solver/certify.js (strategy extraction +
  exhaustive simulation), solver/gen.py (15-anchor validation), solver/gen2.py
  (constructive plane-board generator), solver/verify.py (structural
  verifier), solver/exhaustive.py (full enumeration).

## Validation
- 15/15 anchors pass (C_n parity n=3..8, K4, C_n+chord, Θ(j,2,k), Θ(2,2,2)
  sample game, BBFS Fig 16, open/closed butterfly Grundy values, fan Grundy 0,
  fishy n=5). Both implementations agree on every case.

## Chronology of findings
1. Theta sweep (cell rule, all 3 outer faces, j≤k≤l, total ≤ 16): 369 boards,
   0 violations — parity holds on all BBFS-open theta families in range.
2. Fan board (hexagon + 3 diagonals from one vertex, m=9, 2-connected):
   P2 wins — independently rediscovered F&Z Fig. 5 after prior-art search
   (initially believed new; discarded as a novelty claim; kept as independent
   VERIFICATION of the published refutation of 355637, with full certificate:
   659 states, 1495 terminal plays).
3. Closed-wing butterfly (m=6, min deg 2, one triangular cell): P1 wins —
   parity violation; board appears in F&Z Fig. 4 (Grundy 3) but the parity
   consequence and minimality are new.
4. Exhaustive search n ≤ 6, m ≤ 7 (every graph, every rotation system, every
   outer face; 6532 boards/variant): m ≤ 5 no violations (both variants);
   m=6 face-rule violations all isomorphic to the butterfly (unique); m=7
   face-rule violators = degree type (2,2,3,3,4), 2-connected; m=7
   chordless-gloss violators = degree type (2,3,3,3,3), 2-connected.
5. Karker–Walker fishy graphs (triangle + n-gon sharing a vertex): verified
   n=5 (P1, both variants) — published claim, not new.
6. Chordless-gloss theta sweep: Θ(2,3,5) violates parity (10 even edges, P1
   wins) — a gap case in BBFS §7's open list (j-even with a length-3 path is
   absent from it and uncovered by their Thm 4/Cor 4.1). Certificate: 448
   states, 1680 terminal plays. Face rule: parity-consistent (all embeddings).
7. Generalized certify.js to either winner and turn-alternating simulation;
   certificates regenerated for all five boards (artifacts/ + certificates/).

## End-to-end re-verification (final step)
All five artifact boards re-solved with the independent Python solver and
cross-checked against the recorded values and node certificates:
- butterfly (m=6): face=P1 (VIOLATION), chordless=P2 (consistent)
- m7_face_v35 (m=7, deg (2,2,3,3,4)): face=P2 (VIOLATION), chordless=P1
- m7_chordless_2333 (m=7, deg (2,3,3,3,3)): face=P1 (consistent),
  chordless=P2 (VIOLATION); canonical embedding re-checked from
  exhaustive_results.json
- fan (m=9): P2 under both (VIOLATION) = F&Z Fig 5 confirmed
- theta235 (m=10): face=P2 (consistent), chordless=P1 (VIOLATION)

## Residual items
- Zandee 2022 thesis not reachable (TU Delft resolver timeout from this env):
  novelty labels for the small counterexamples are PROVISIONAL.
- Lean formalization not started (documented as future work in discovery.md §8).
- Open proof target for a future session: parity for Θ(1,3,k) under the cell
  rule (would resolve an explicitly open BBFS case); computational support to
  16 edges.
