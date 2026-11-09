# expanded-corpus-r240 (Claude lane): summary

**Reservation:** 20 MathDB IDs between 346858 and 348627 (`reservation.json`, selection rule reserve8).

**Literal statements:** extracted with exact raw lines, line numbers and chunk/raw/statement hashes. The files are `raw/*.jsonl` and `extracted.json` (with the manifest sha256), built by `scripts/extract.py`.

**Restrictions honoured:**

* No Lean, lake, SAT or ILP was run.
* Every computation was a single foreground `bash -c 'ulimit -v 2000000; timeout 100 python3 -I -B …'` call.
* All writes stayed inside this lane, with no overwrites (outputs opened with `x` mode, new names used for reruns).
* HTTP receipts are in `sources/*.receipt.json`. There were no 403/429 responses and no denied hosts were contacted.
* One edit was made by a python heredoc rather than the Edit tool: creating `scripts/hetyei_literal_vbu.py`, a copy of `hetyei_literal.py` with one documented line changed.

## Candidate (zero credit until root review)

**347230: Hetyei's interval-transform kernel conjecture is refuted at n = 5.**

* Source: DCG 71 (2024), Conjecture 39 = arXiv:2007.07362 Conjecture 5.14.
* Certificate: an explicit symmetric 20-term degree-5 ab-polynomial u with u* = u ≠ 0 and I₂(u) = 0. So ker I₂|₅ = A₅ ⊕ ℚu has dimension 13, against dim A₅ = 12.
* The conjecture holds for n ≤ 4. The exact kernel excess is 1, 2 and 7 at n = 5, 6 and 7.
* Two independent implementations agree: a poset/flag-f one validated on 20 explicit posets, and Theorem 32 with ER Definition 9.1.
* Hetyei's Definition 31 misprints the ER mixing operator base case. The misprinted operator contradicts the paper's own Corollary 33 and Theorem 32; the conjecture fails under both readings.
* Registry screens (Lean Pool, Omega, OpenAI/math, GitHub) are clean.
* An uncompiled Lean draft is in `lean-draft/HetyeiIntervalTransform.lean`. It is a small finite certificate; the remaining routine bridge lemmas are listed.
* Full write-up: `CANDIDATE.md`.

**347231: Hetyei Conjecture 40 is refuted at n = 3. Secondary; same source; elementary.**

* I₂ does not preserve S₃: I₂(aab+baa) is not symmetric.
* So the I₂-eigenvectors inside S₃ span only 5 of its 6 dimensions, whatever compositions are used.
* Also found: Hetyei's Lemma 36 is false, and the 128 Pyr/L compositions span only 71 of 72 dimensions at n = 7.

## Other dispositions (see `results.json`)

**Prior public resolution: excluded.**

* **346858:** I independently found a positive non-constant tEoM solution on T₂ (geometric spine 2ᵏ with constant hanging subtrees of length (3/5)2ᵏ). The Omega trureturing issue #25434 (2026-11-01, settled by merged PR #25509) had already published the same construction.
* **347354:** Proved in the source itself (Han–Zeng Corollary 1.8).
* **347468 and 347469:** These codes reduce to Gold-function codes. Qian–Shi, IEEE TIT 71(7) 2025, solves the four Heng–Ding conjectures (abstract-level evidence).
* **348074:** Refuted by Naserasr–Pham–Pujol–Zhou (arXiv:2505.16808), who give a planar graph with a_f > 2.
* **348627:** Resolved in the source itself (Dujmović et al., Theorem 1 consequence).

**Parked after computation beyond the source range.**

* **346999:** Sundaram's Conjecture 1 is equivalent to coefficient positivity of an explicit polynomial β_T(x). I verified it for all 32767 nonempty T ⊆ [1,15]. No positivity proof was found, and the Lean route (order-complex homology with Sₙ characters) is infeasible.
* **347991:** Wahl's Conjecture 5.9 holds for n ≤ 140 (111895 inequalities), against the authors' n ≤ 20. No closed form was found.
* **348106:** I reduced the question to unions of closed balls and found no disconnecting family for n = r = 7 and 8. This is tied to the classical neighbour-connectivity of Qₙ, so a proof would likely be a routine bridge.

**Parked or disposed: deep, analytic or no finite route.**

| ID | Reason |
|---|---|
| 347000 | Reduces to 346999 via the source's own Lemma 41 |
| 347099 | OEIS A052141 identification plus the source's own recursion: a routine bridge, very high Lean cost |
| 347122 | Analytic |
| 347731 | Complexity trichotomy |
| 347960 | Ryser family; the source proves r ≤ 4 |
| 347972 | Remaining case is Specht Gram valuations; no Lean route |
| 348408 | Open; no structured route |
| 348470 | Undecidability |
| 348613 | Geometric packing |

## Searches and coverage

| Script | Coverage |
|---|---|
| `scripts/subword_beta2.py` | All T ⊆ [1,15] |
| `scripts/hetyei_I2.py` | Kernel ranks n ≤ 9 (mod p) |
| `scripts/hetyei_gen.py`, `scripts/hetyei_spec2.py` | Exact for n ≤ 7 and n ≤ 6 respectively |
| `scripts/teom_horo.py` | Two-type horocyclic ansätze |
| `scripts/wahl_K.py` | n ≤ 140 |
| `scripts/hypercube_star.py` | Q₇ and Q₈ |

Full logs are in `logs/`, and file hashes and receipts are in `outputs/artifact-hashes.json`.

## Lessons

* The Omega registry is actively harvesting conjectures from this arXiv window: 346858 was taken 4 days before this lane started. Screening it before computing paid off.
* MathDB paraphrases dropped key fidelity details, here the misprinted M base case and the n → n+1 codomain typo. The cited primary definition (ER 1998) settled the intended operator.
