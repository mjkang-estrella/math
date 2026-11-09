# Lead agent's independent milestones (third implementation)

Run by the lead agent while subagents worked, using `src/persistence.py` only —
an independent path from A's lattice searcher and C's heap generator.

## Max P(m) over 𝓜_D for growing D (single core, exact)

| D | domain points | max P | argmax (a,b,c,d) → m |
|---|---|---|---|
| 8 | 2,025 | 8 | (11,7,0,0) → 4478976 |
| 10 | 4,356 | 9 | (12,7,0,2) → 438939648 |
| 12 | 8,281 | 9 | (12,7,0,2) → 438939648 |
| 14 | 14,400 | 9 | (12,7,0,2), (33,3,0,0) → 231928233984 |
| 15 | 18,496 | **10** | (19,4,0,6) → **4996238671872** |
| 16 | 23,409 | 10 | (19,4,0,6) |
| 18 | 36,100 | 10 | (4,20,0,5) → **937638166841712**, (19,4,0,6) |
| 20 | 53,361 | 10 | same two |
| 22 | 76,176 | 10 | same two |

Anchors all reproduced: maxP(𝓜₅)=6 (brute-force equivalence gate), the first
P=10 7-smooth appears at D=15 and is 4996238671872 = 2¹⁹·3⁴·7⁶ = Π(277777788888899).

## New frontier member

`937638166841712 = 2⁴·3²⁰·7⁵` has P = 10 (naive-verified) with chain
937638166841712 → 438939648 → 4478976 → 338688 → … → 0 — i.e. it merges into the
record chain at 438939648. So the P=10 7-smooth frontier (parents of persistence-12
candidates) contains at least {4996238671872, 937638166841712, 231928233984? (P=9)}.

## Smallest 7-smooth number with P ≥ 10

**Claim:** `min{ m 7-smooth : P(m) ≥ 10 } = 4996238671872`.
Coverage argument: any 7-smooth m < 4996238671872 ≈ 4.996×10¹² has dc(m) ≤ 12,
hence len(m) ≤ 1.431·dc(m)+1 ≤ 18 (ratio bound: len(m) ≤ dc(m)·ln10/ln5 + O(1),
since the worst digit-per-value is 5) — well inside the swept len ≤ 22 domain,
where maxP = 10 is attained first at 4996238671872. ∎ (machine-checked for
len ≤ 22; subagent A's larger D only strengthens it)

**Corollary.** Any 7-smooth m with P(m) ≥ 11 satisfies Π(m) ≥ 4996238671872,
so m has ≥ 14 digits (9¹³ = 2.54×10¹² < 4.996×10¹²).

## Merge-monotonicity lemma

Verified exhaustively: 145,035 (X, Y, R) triples, 0 counterexamples
(`src/verify_merge_lemma.py`) — underpins Lemma 4 in notes/theory.md.

## Heuristic calibration

`src/heuristic_calibration.py` → `results/heuristic_calibration.md`:
over 10⁶ random L-digit samples (L = 10…300), persistence ≥ 11 never occurred;
max persistence *decreases* with L (zero-wall + shrink-tail, theory.md §7).
