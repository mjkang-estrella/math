# Expanded corpus r96 (reserve5: computationally verified discrete conjectures)

**I investigated all 20 reserved IDs. One candidate carries a full literal Lean endpoint: 368807, refuted at n = 8. Four items are excluded as already resolved in the literature, and fifteen are parked.** No credit is claimed. Root acceptance, independent reviews and a paper come separately. No shared counts, ledgers or indexes were changed, and nothing was written outside this lane.

## Candidate: 368807 (ASEP neighbourhood-tour conjecture), refuted

The source is Vercesi–Barta–Gambardella–Gualandi–Mastrolilli, arXiv:2506.10671 (v1 only). Its Conjecture 1 says that every vertex of the asymmetric subtour elimination polytope P_ASEP^n is adjacent to at least one tour. The authors base this on preliminary tests for n ≤ 6.

At **n = 8**, the point x* = X/4 (support 19, denominator 4; matrix in `ASEP-COUNTEREXAMPLE.md`) is a vertex: its tight rank is 56 = n(n-1). It is adjacent to **none** of the 5040 tours.

- **Proof.** For each tour T there is an integer direction v. It lies in the minimal face of [x*, T], has zero degree sums and zero flux across the cuts tight at both points, has Σ|v| ≤ 64, and is not parallel to x* - T. Then z ± v/512 ∈ P with z = (x* + T)/2, so [x*, T] is not a face.
- **Independent diagnostics.**
  - Exact integer ranks: the maximum common tight rank is 54 < 55.
  - A separate BigInt JavaScript implementation, which also enumerates the constraints and tours itself, gives the identical rank histogram.
  - The method reproduces the source's n = 4 facts.
- **Search.** Sampled vertices give minimum adjacent-tour counts of 5, 4 and 3 for n = 4, 5, 6. Annealing walks on the vertex graph reach 1 at n = 7 (not exhaustive, so n = 7 is still open). At n = 8 they reach 0, and 101 zero-count vertices were found.
- **Lean.** `ASEP.arc_counterexample` and `ASEP.arc_neighborhood_tour_conjecture_false` are stated on the literal arc space ℝ^A, with the source's (2)–(4),(6) and δ(S) = {(i,j) : i ∈ S, j ∉ S}. Vertices are extreme points, adjacency means the segment is an extreme subset, and tours are incidence vectors of n-cycles. Matrix-form versions are included, and the exposed-face reading is excluded as well.
  - The 5040 certificates are checked by proved-sound Boolean checkers under kernel `decide` (48 chunks). Coverage of all cyclic orders is a kernel-checked equality with `List.permutations'`, and n-cycles are bridged to cyclic orders through `IsCycle.orderOf`.
  - The fresh extracted strict replay (`lean-replay-3/result.json`) rebuilt all 21 modules with `-DwarningAsError=true` and ran `leanchecker` on all 21; everything passes. The forbidden-construct scan is clean, and the axioms are only `propext, Classical.choice, Quot.sound`. Peak RSS was 4.9 GB.
- **Prior art (bounded).** Only arXiv v1 exists. The same group's follow-up (arXiv:2511.05045, PDF read) does not mention the conjecture, and a web search found nothing. Omega HEAD `9e88f6fb…` (complete untruncated D5/Problems trees, newer than root's `0ef26ad5…`) and the OpenAI HEAD `4eaee875…` preprint listing (unchanged) have no ID or keyword match. These are path and keyword screens, not novelty clearance.
- **Caveat for root.** The conjecture comes from preliminary tests in an OR paper, and n = 8 is two sizes beyond what the authors tested. Root should judge significance. The refutation does defeat the source's proposed use of the conjecture (obtaining the full V-description by pivoting once from an integer vertex), because no S_8-image of x* is adjacent to a tour.

Full dossier: `ASEP-COUNTEREXAMPLE.md`. Lean packet: `lean/README.md`.

## Known resolutions (excluded, zero credit)

- **368627** (non-elementary abelian 2-designs): settled by arXiv:2607.24426, Theorem 1.1 (Jul 2026). The theorem statement and the final proof section were read. My exact pair-count checker found no design in any non-elementary group up to order 128 (some order-128/243 groups were cut off by the CPU cap) and reproduces the elementary-abelian designs.
- **367165** (fixed-perimeter FD ≥ FO): proved by Cuthbertson, arXiv:2609.17389 (Sep 2026), by singularity analysis. I derived the same mechanism independently before finding the paper, which I then read.
- **349717** (strengthened convexity for p_d): implied by O'Sullivan, arXiv:2205.13468 Theorem 1.3, which has the stronger factor 1 - n⁻².
- **363770** (O(n) path separating systems): the record itself cites the 19n theorem of Bonamy et al. (2023).

## Computational coverage of parked items

| ID | Exact space covered | Result |
|---|---|---|
| 341896 | Rectangle/trapezoid (both orientations): 114 jobs beyond the source's n ≤ 8, ℓ ≤ 4 (n to 12, ℓ to 8; largest 1.6M P-partitions). Q^{2n}/I₂(2n): 170 completed jobs (n ≤ 14, ℓ ≤ 12; largest 7.4M), 32 capped | All orbit (size, ddeg-sum) multisets agree. Johnson–Liu (arXiv:2311.07133) already proves orbit-structure equality for the main pair; the open remainder is ddeg homomesy on trapezoid P-partitions |
| 368042 | All 14524 chordal graphs on 9 vertices (new) and all ≤ 8 (reproducing the source), all k, Hochster formula mod 32003 | reg = aim + k everywhere. Lean is infeasible because regularity is not in mathlib |
| 366914 | y = 7..11, every k ≥ 3 with k < y/2, the open window y ≤ a < f(y-k, y), 1 ≤ b, c ≤ 14 or 18 (9872 instances) | All realised, and every path is verified. y = 12, 13 are partial (capped) |
| 382492 | Every μ ⊢ kn for (k, n_max) = (2,13), (3,9), (4,7), (5,6), (6,5), (7,4); reproduces the source example | No negative e-coefficient |
| 376197 | Source Theorem 3.9 plus LPs; random GF(2,3,5,7) matroids with loops and parallel classes, n ≤ 10 (about 3.9k distinct labelled); uniform formulas reproduced | No violation; equality at ω = 2. Lean is infeasible |

The other parked items received source-backed dispositions without a finite surrogate:

- **Analytic, asymptotic or famous:** 349136 graph positivity, 350950 q-Seidel sharpness, 366840 Hajdu–Sárközy k = 2, 370189 harmonious labelling.
- **Beyond caps or no mechanism in this pass:** 347539 GKP 9×9 minors in 7 variables, 342630 fullerenes beyond 216 vertices, 349406 PPS existence, 350489 universal circulant generator sets (follow-ups resolve existence with other sets), 375325 refined scaffold exchange, 375831 Miura-ori sub-top coefficient (downstream of the open degree bound).

`results.json` has exactly 20 ID-keyed entries. Each entry has the raw-line, chunk and statement hashes, the source receipt, review depth, outcome, coverage and remaining lemmas.

## Process and resource notes

See `VALIDATION.md`. Two cap incidents are recorded candidly in `logs/resource-incident-ghv.txt`:

- Four concurrent single-threaded LP processes ran for about 2 minutes.
- An early uncapped Lean kernel `decide` over all 5040 certificates reached 26 GB RSS and was killed.

Every later Lean call ran under an RSS watchdog. No background jobs are left running (`outputs/process-check.json`).
