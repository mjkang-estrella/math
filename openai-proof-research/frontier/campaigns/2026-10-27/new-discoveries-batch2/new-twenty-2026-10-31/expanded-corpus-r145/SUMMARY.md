# Expanded corpus r145: summary (Claude lane)

**Bottom line: no credit candidate.** All 20 reserved IDs have a source-backed disposition in `results.json`. Nothing here is self-accepted.

- One finite literal refutation was found (343469). It only corrects the printed range at a single small value, n = 3, so I recommend zero credit.
- One conjecture (349179) is resolved by a construction already printed in a paper the source cites. Zero credit under lesson 372630.
- One statement (362860) is ill-posed as printed.
- Eight finite conjectures were swept beyond their known ranges without finding a counterexample.
- Eight famous, deep or analytic items received short dispositions.

No Lean, lake, SAT/ILP solver or compiled helper was run. Every computation was a single `python3 -I` process under `timeout 140 prlimit --cpu=120` with `MALLOC_ARENA_MAX=2`, one at a time. No background job is left.

Lane-discipline note: early on, a 140-byte list of the reserved IDs was written to the session scratchpad by mistake. It was deleted before handback, and nothing else was written outside this lane. Two capped runs went to the background after exceeding the tool's 120 s foreground window; each finished within its own 140 s cap before any other process was started.

## Ranked outcomes

| ID | Outcome | Credit view |
|---|---|---|
| 343469 | Gao–Gu Conjecture 4.12 is false as printed (n ≥ 2) for k = 2. Exact certificate uses n in {2, 3, 4, 5, 19}. The same holds for every k ≡ 2 (mod 4) tested, and **only** at n = 3. From n = 4 on, a consistent pair (α_k, c_k = ξ₂(k) + 2) exists for all k ≤ 32 up to n ≤ 600. | Endpoint correction: zero credit recommended |
| 349179 | Liu–Chew–Heule Conjecture 11 holds for every prime k. The Berg/Vivas coloring x₁y₁ + x₂ + y₂ (Fenner et al., arXiv:1005.3750, Theorem 3.14, the source's reference [5]) is already a balanced left-shift pattern. | Cited construction: zero credit |
| 362860 | Rivezzi Conjecture A.10 is ill-posed. The image lies in S_{n+m}, so it can never equal a full class Av(S). The size-restricted reading is trivially true. | Formulation defect |
| 359361 | Hanson–Toft, case (K₃,K₃): the minimum co-critical size is exactly 4n − 10 for n = 6..9. At n = 9 the only co-critical graph with ≤ 26 edges is K₄ + K̄₅. The source says the case is proved only for n ≥ 56. | Bounded non-finding |
| 338138 | Every tree on 3..22 vertices is neighborhood-prime (all 5,623,756 trees at n = 22). The Asplund–Fox large-n theorem has a non-explicit threshold, so a finite sweep cannot close it. | Bounded non-finding |
| 341596 | Lu–Wang Conjecture 6: no counterexample for k = 4 with n ≤ 6 (and n = 7 with m ≤ 7), k = 5 with n ≤ 7, k = 6 with n = 7 (and n = 8 with m ≤ 7), or k = 7 with n = 8. | Bounded non-finding |
| 336197 | Haslegrave Conjecture 2 (distance-two antimagic) holds for all graphs on ≤ 8 vertices with no isolated edge. | Bounded non-finding |
| 348799 | Balister et al.: n = 3 and n = 4 re-verified exhaustively; 12,599 random and structured n = 6 instances are all solvable. | Bounded non-finding |
| 340259 | Siemons–Wagner (Bradley Conjecture 1): the source already checked degree ≤ 200 in Magma and proved the 3-homogeneous case. A proof needs O'Nan–Scott-level analysis. | Parked |
| 338758 | Song–Zhang Gallai–Ramsey conjecture: known for n ≤ 6; no finite route. | Parked |
| 341663, 341664 | The source's own v2 records Adiprasito's (and Adiprasito–Steinmeyer's) claimed proofs. 5.2 also follows from 5.1. | Known (claimed) |
| 336513 | Proved by Griffin–Ono–Rolen–Zagier (2019). | Known |
| 344479 | Proved in the source itself (Craig–Pun). | Known |
| 335932, 343072, 344496, 344631, 344632, 376066 | Deep or analytic: a sum-product growth question, Chamberland's conjecture, GIRS structured matrices, Brill–Noether for R-divisors, the covering-radius conjecture, and Baker's Brill–Noether existence conjecture. | Parked |

## 343469 in detail (the strongest finite object)

**Definitions** (Gao–Gu, arXiv:1908.03914, v1 is the only version):
- A Dyck path has weight equal to the product of b(h) over its up-steps, where h is the height the step starts from. The weighted Catalan number C_n^b is the sum of these weights over all Dyck paths of semilength n.
- L_n^(k) is C_n^b for b(x) = (2x+1)^{2k}.
- Conjecture 4.12 asks for a 2-adic integer α_k and an integer c_k ≥ 0 with ξ₂(L_n^(k) − C_n) = s₂(n) + ξ₂(n − α_k) + c_k for every n ≥ 2.

**Certificate for k = 2.** Write e(n) = ξ₂(L_n − C_n) − s₂(n).

Exact values (`outputs/catalan-k2-certificate.json`):

| n | e(n) |
|---|---|
| 2 | 3 |
| 3 | 11 |
| 4 | 3 |
| 5 | 4 |
| 19 | 8 |

For example, L₃⁽²⁾ = 57349, and L₃⁽²⁾ − 5 = 7·2¹³.

1. If α were even, then ξ₂(3 − α) = ξ₂(5 − α) = 0, so e(3) = e(5). That is false (11 ≠ 4), so α is odd.
2. With α odd, ξ₂(2 − α) = 0, so c = e(2) = 3.
3. Then ξ₂(3 − α) = e(3) − c = 8, so α ≡ 3 (mod 256). Hence 19 − α ≡ 16 (mod 256) and ξ₂(19 − α) = 4.
4. But e(19) − 3 = 5. Contradiction.

**Cross-checks.**
- Three independent computations agree: a modulo-2⁶⁴ height DP, an exact continued-fraction series, and an exact big-integer DP. Brute-force Dyck enumeration matches them for n ≤ 11 or 12.
- k = 1 reproduces Postnikov's α = …010111₂ with c = 2 (Gao–Gu Conjecture 4.11).

**Why zero credit.**
- The failure is the single value n = 3, against a range n ≥ 2 copied from Postnikov's k = 1 conjecture.
- The evidently intended statement (n ≥ 4) survives every test.
- Proving the intended statement would include Postnikov's own conjecture, which has been open since 2000.

A Lean plan is in `results.json`. It was not drafted, because the item is not recommended for credit.

## 349179 in detail

**Shift pattern** (source Section 4.1): in each k×k subgrid, row i+1 is row i shifted cyclically by one, and all subgrids are shifted the same way.

**The coloring.** Index rows by (x₁, x₂) and columns by (y₁, y₂) over F_k, with block (x₁, y₁).
- COL = x₁y₁ + x₂ + y₂ depends only on x₂ + y₂ inside a block. That makes each block a left shift, and each color appears k times per block.
- Rectangle-freeness is Fenner et al.'s Theorem 3.14 proof.
- For prime k the cyclic group Z_k is the additive group of F_k, so the shift is cyclic.

**Computer check.** For k = 2, 3, 5, 7, 11, 13 the equivalent right-shift form (j − i − ab) mod k passes all three checks. The cyclic formula fails for composite k = 4, 6, 8, 9, as it should (`logs/shift-affine.log`).

## Coverage and controls

- **Trees:** WROM generator counts match OEIS A000055 through n = 22. Negative controls behave correctly: C₆ and C₁₀ (n ≡ 2 mod 4) are reported not neighborhood-prime.
- **Graphs:** isomorphism-class counts match OEIS A000088 through n = 8.
- **Co-critical n = 9 search:**
  - Every 9-vertex graph with ≤ 26 edges arises from an 8-vertex class by adding a vertex of minimum degree d ≤ 5.
  - The filter "every non-edge has ≥ 2 common neighbours" is necessary. Extend a good colouring with the new edge red and then blue: each choice forces a monochromatic triangle through the new edge, with two different third vertices.
  - Positive control: K₄ + K̄₅ is found when the cap is 26.
- **Pairing solver (348799):** exhaustive for n = 3 and 4, with controls (non-zero-sum instances are unsolvable). The first n = 6 run hung on a hard instance and printed nothing (`logs/f2pairs.log`). It was replaced by a budgeted solver with randomized restarts (`logs/f2pairs-v3.log`).
- `logs/catalan-1024.log` records the first attempt, which failed for lack of numpy. It was superseded by the pure-Python DP.

## History, prior art and registries

- **Prior campaign notes:** an exact-ID grep over all campaign `*.md`, `*.json`, `*.txt` and `*.jsonl` (excluding this lane) found only corpus copies, coverage or routing lists, and coincidental numeric strings (for example a timestamp ending in 359361). There is no earlier exclusion or lane note for these IDs.
- **Registries:** a path-keyword screen of the cached Omega D5/Problems trees and the OpenAI preprints listing found no same-problem paths (`outputs/registry-screen.json`). This is a path screen against cached snapshots only, not a live HEAD re-fetch, because no candidate reached the significant-investment stage.
- **Literature:** prior-art statements come from source bodies where read, plus web search results, which were checked at snippet or abstract level only. Each entry's `review_depth` says which. Denied routes were not used.
- **Receipts:** fetches went through arxiv.org abs/pdf with TLS verification on. Dated receipts with SHA-256 hashes are in `sources/receipts.jsonl`. Exact raw corpus lines are in `raw/*.jsonl`, and the chunk, line, raw and statement hashes are in `extracted.json`.

## Files

- `results.json`: 20 ID-keyed entries.
- `extracted.json`, `raw/`: literal provenance.
- `scripts/`: every computation. `extract.py` and `fetch.py` are adapted from r144.
- `logs/`: full outputs.
- `outputs/`: the k = 2 certificate, the registry screen, and the cached 8-vertex graph classes.
