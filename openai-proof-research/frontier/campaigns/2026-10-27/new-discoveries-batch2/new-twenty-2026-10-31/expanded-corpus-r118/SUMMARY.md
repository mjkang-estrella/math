# expanded-corpus-r118: summary (2026-11-02)

Investigator: Claude Opus 5.5, high effort, working alone (no child agents). Credit: 0 (no self-acceptance). Writes were confined to this lane. No git operations, no ledger edits and no browser use.

## Headline: one Lean-complete candidate

**MathDB 359279 (linear-bound multiset reconstruction for tableau minors) is false.**

The source is Erickson–Herden–Meddaugh–Sepanski–Hammon, arXiv:2307.13161, Conjecture conj:k+4: for k ≥ 1 and n ≥ k + 4, the multiset mM_k(T) of k-minors determines T ∈ YT(n). The authors verified it for k ≤ 5.

* An exhaustive computation over all of YT(n) shows n = k + 4 is injective for k ≤ 7 but **fails for k = 8 (n = 12)**, and also for k = 9, 10, 11.
* Minimal counterexample: the hooks
  * T₁ = 1 5 7 8 12 / 2 / 3 / 4 / 6 / 9 / 10 / 11, of shape (5,1⁷),
  * T₂ = 1 2 3 7 10 11 / 4 / 5 / 6 / 8 / 9 / 12, of shape (6,1⁶),

  have identical multisets of all 19,958,400 8-minors.
* The result was checked by three implementations: dense Python, a C hash sweep, and an independent exact Python DP.
* **Lean.** `lean-packet/TabMinors.lean` proves `TabMinors.not_conjecture : ¬ Conjecture`.
  * The definitions of SYT, jeu-de-taquin deletion and the multiset of minors are literal.
  * The proof uses a proved-sound DP with eight per-level kernel certificates for each tableau, plus semantic certificates that every deletion terminated properly.
  * Fresh strict replay (`-DwarningAsError=true`) and leanchecker both pass. All 137 local declarations were audited; the only axioms are propext, Classical.choice and Quot.sound.
  * Positive controls reproduce the source's own examples, and two negative controls are rejected.
* **Strengthening (ordinary proof only).** For hooks there is an exact formula, mM_k(H(w)) = k! Σ_P min(P)·{H(w|_P)}. With pigeonhole, it shows that **no bound n ≥ k + c works for any constant c**. Explicitly, n ≥ k + 5 already fails at k = 11 (n = 16).
* Details: `outputs/359279-proof.md`.
* Prior art: no resolution was found in web searches, the 2025 seminar slides, the Omega registry (HEAD 0561ac6, complete D5/Problems path screen) or OpenAI/math (HEAD 4eaee87, unchanged). These were path screens, not body reads, and no journal version of the source was located.
* Open items for root: independent fidelity review and significance adjudication.

## All 20 dispositions (details in results.json)

| ID | Disposition | Depth / coverage |
|---|---|---|
| 358266 | parked: hard analytic (ECH connected sum) | conjecture located in source body |
| 358789 | parked (matching-field algebraic matroids) | body located; needs tropical/M2 software |
| 358810 | parked, verified range | 272 cases, n ≤ 130, all consistent (own meander spectra) |
| 358812 | parked, partial prior | 5228 cases, n ≤ 110, log-concave. Coll 2026 (arXiv:2609.27153) proves smaller block ≤ 128 |
| 358821 | parked: MathDB paraphrase defect | source says "or ML ≥ 1/4", not "= 1/5"; source searched speeds ≤ 400 |
| 358922 | **excluded: known full scope** | Chern–Sellers 2024 Thm 1.1 + Cor (odd k and even k ≥ 2) + Sellers mod 4 (k = 0); own check to 2^20 |
| 358947 | parked: hard analytic (Banach SEP) | source "we strongly believe" located |
| 358968 | parked: complexity hypothesis (PDS recovery) | conjecture located in source body |
| 359121 | parked (gossip rate, regular graphs) | conjecture located; analytic |
| 359261 | parked (3-move segmentation) | informal source definition |
| 359278 | parked, no counterexample in reach | k = 3 sets injective at n = 11–14; k = 4 at n = 13; domain k = 3, n ≥ 15 not reached |
| **359279** | **candidate refutation, Lean complete** | see above |
| 359324 | parked: hard (joints structure) | conjecture located |
| 359380 | parked (Jacobian matroid edge reversal) | source verified p ≤ 6; p = 7 too heavy |
| 359425 | parked, verified range (Hurwitz interlacing) | exact recursion, no failure: g = 0, n ≤ 7, size(μ) ≤ 13; g = 0, n ≤ 2, size(μ) ≤ 20; g = 1, n ≤ 7, size(μ) ≤ 11 (source stopped at n ≤ 5) |
| 359582 | parked (height-two linear extensions) | open per Soukup 2023 |
| 359589 | parked (planar tree counting) | conjecture located |
| 359636 | parked (triangle-free CM oriented) | open girth-4 non-bipartite case; no CM software |
| 359740 | parked, verified range | all lists p ≤ 13; all support-3 lists p = 17, 19, 23: all realizable |
| 359753 | parked (D-optimality bounds) | numerical, continuous |

## Process notes

* Tooling:
  * There is no gcc. C was compiled with the Lean-bundled `leanc` against hand-written prototypes (`scripts/libc.h`).
  * Python scripts that need numpy run with `-P` (user site) instead of `-I`.
  * Every numerical and Lean process ran under `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB. AS was 12 GiB, raised to 64 GiB for Lean only, as the brief allows.
  * Lean always ran with `-M3500`.
  * Limitation: when Lean ran as a grandchild (`leanbuild.py`, `packet_replay.py`, `controls.py`), the wrapper's RSS sampling saw only its direct child, so Lean's own `-M3500` was the effective memory guard. Peak observed Lean RSS was about 2.7 GB in the directly sampled runs.
* Network: arXiv abs/e-print pages, GitHub API (`commits/HEAD`, git trees), a few seminar PDFs, and web search. All receipts are in `sources/`. No denied routes were retried.
* No background jobs remain at handback.

## Files

* `extracted.json` and `raw/*.jsonl`: exact corpus lines with chunk/line/hashes, verified.
* `history-matches.txt`: bounded history check.
* `results.json`: the 20 dispositions.
* `outputs/notes.md`, `outputs/359279-proof.md`.
* `lean-packet/` (TabMinors.lean, Audit.lean, Controls.lean, NegControl*.lean) and `lean/` (the working copy).
* `scripts/` and `logs/` (full logs and resource receipts).
