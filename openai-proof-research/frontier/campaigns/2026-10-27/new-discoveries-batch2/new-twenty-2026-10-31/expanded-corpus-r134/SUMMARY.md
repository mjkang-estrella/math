# expanded-corpus-r134: Claude pass summary (2026-11-03)

Outcome: **no candidate for credit.** Nothing is self-accepted. All 20 reserved IDs have ID-keyed entries in `results.json`, with raw-line provenance copied from `extracted.json`.

There is one strong new **lead**, for 371207 (the Day–Johnson Voronoi conjecture). It is numerical evidence only, with no proof and no Lean.

## Handover from the cancelled Sol worker

- **Kept and verified:**
  - `extracted.json` and `raw/`: 20 rows, with chunk, line, raw and statement hashes.
  - The `sources/` PDFs and texts, with receipts in `sources/receipts-*.json`.
  - The registry HEAD snapshots. OpenAI/math is at 4eaee875 and Omega at 86172888, matching root's 2026-11-03 values.
- **Sol Voronoi data:** the logs in `logs/voronoi-*.log` came from the compiled C helper, which I did **not** run. I reimplemented the search in pure Python (`claude/vor.py`, `claude/t_vor.py`). It reproduces Sol's equilibrium counts exactly for n=3 with k=5,6,7,8 (0, 3, 7, 2) and for n=4 with k=5,6 (60, 59). The other Sol counts, including k=5 at n=7 with 0 equilibria, remain unverified diagnostics from the C helper.
- **history-matches.txt:** only grepped, never read whole. The single 371207 hit is a numeric false positive in `sepperm-proof-r1`. No prior campaign note covers any of the 20 IDs.
- **Resource discipline:** every computation ran through `claude/run.py`. Limits were 2-CPU affinity, CPU 120 s, wall 140 s, address space 1.5 GiB, MALLOC_ARENA_MAX=2 and `python3 -I`. Only one process ran at a time; the maximum sampled RSS was 0.82 GiB. Receipts are in `claude/logs/*.receipt.json`. No background job is left running.

## Dispositions

| ID | Outcome |
|---|---|
| 353008 | Proved in its own source (arXiv:2112.11164, Theorem 1 and Corollary 1: a parity count for bipartite graphs). |
| 362163 | Refuted in print: Guo–Wu arXiv:2608.10687 give χ'_k ≥ (4−2√2+o(1))k. |
| 371858, 375993 | The CHOS 1987 F-irregular conjecture, proved by Schreib arXiv:2609.07745 and by Dovzhenok–Filuta arXiv:2609.19245. For 371858, the MathDB phrase "isomorphic F-neighbourhoods" is a paraphrase; the source uses F-degrees. |
| 361975 | Proved in TWXI (arXiv:2309.04390). |
| 370719 | Disproved by its own source (arXiv:2510.01791, Theorem 1.4). Lead for root only, not investigated: the smallest failing k, especially the k=3 conjecture of Bogdanov et al. |
| 372150 | MathDB copies v1, where the bound is \|Z\| ≤ k−1 (v1 fetched 2026-11-03, sha256 28ef168f…). v2 changes it to \|Z\| ≤ k because of the Albrechtsen–Huynh–Jacobs–Knappe–Wollan counterexample. The printed version is refuted by that cited construction; the corrected version is deep and open. |
| 372153 | MathDB copies v1. The current version's Theorem 6.15, with Lemmas 6.13–6.14 for k ≥ 8, shows F(G, Z_2^k) is connected, so the statement holds for k = 9. Source-resolved. |
| 369933, 361033 | BFP Conjecture 24 on nut graphs. It is still open for some odd semiprime orders; the first open order is 2839, and 457 such orders lie below 10^6 (Rozman–Šparl v2). This is a distinct question from the credited 365943 (no cubic 8-circulant nut graph), not a parameter variant of it. A full answer needs a new construction for all odd semiprimes plus automorphism-orbit proofs for an infinite family, at very high Lean cost. Parked. |
| 372328 | Analytic gap below exp(exp(30.32)); not finitely checkable. Parked. |
| 362516 | Open for k ≥ 9; the first open case (order 17) is far beyond a capped Python search. Parked. |
| 354762, 360349, 367371, 372143, 372773, 376120, 356555 | Deep, structural, asymptotic or classical (356555 predates 2012). Parked, each with a source-backed note. |

## Lead: 371207 — 8-player equilibria for every n from 3 to 22

**Statement (Day–Johnson, as given in Stylianou arXiv:2510.25392, Conjecture 1.1).** For every fixed k ≥ 5 there is an N such that no k-player profile on Q_n is in equilibrium for n ≥ N. A single k with equilibria for infinitely many n refutes it.

**Construction.** Put the 8 players at all points of a 3-dimensional linear subspace S of F_2^n. Such a profile is determined by the multiplicities m_f of the 7 nonzero coordinate functionals f on S. Translations by S permute the players, so every player scores exactly 1/8. The profile is therefore an equilibrium exactly when no deviation of the player at 0 scores more than 1/8.

**Checker.** The deviator's score at every vertex is computed exactly, in integers, as a sum of XOR-convolutions with Hamming balls (Walsh–Hadamard transforms). It was validated three ways:
- against brute force on 40 random profiles;
- against Sol's counts;
- by an independent full brute force over every player, every deviation and every voter, for n=9, 10 and 12.

**Results** (also in `claude/voronoi-k8-subspace.json`):
- **n=3..15, exhaustive over GL(3,2)-orbits of multiplicity vectors.** Equilibria / orbits: 2/4, 3/7, 4/11, 6/19, 11/29, 13/44, 23/66, 30/96, 43/136, 63/193, 87/265, 111/361, 159/485. The fraction stays near one third.
- **n=16..22, explicit equilibria:** (3,3,2,2,2,2,2), (3,3,2,3,2,2,2), (3,3,3,3,2,2,2), (3,3,3,3,3,2,2), (3,3,3,3,3,3,2), (4,3,3,3,3,3,2) and (4,3,3,3,3,3,3).
- **The pattern (t+1, t, …, t) is an equilibrium for t = 1, 2, 3** (n = 8, 15, 22).
- **Failures:**
  - uniform multiplicities t at n=7, 14, 21 (a one-coordinate move is profitable);
  - strongly skewed vectors;
  - the product families (three antipodal pairs, and balanced-4 × one coordinate), which die by n=15–16.
- **Empirical rule for near-uniform vectors:** equilibrium holds exactly when ψ ≠ 0, where ψ is the XOR of the functionals with odd multiplicity. When ψ = 0 every player is at even distance from the others, so ties are possible. Parity alone is not sufficient.

**What is missing.** We need a theorem that, for some explicit family m(n) (for example m = (t+1, t, …, t), or near-uniform with ψ ≠ 0), the deviator's maximum score is at most 1/8 for all n. Stylianou's per-sign-class averaging for k=4 cannot work here: that argument ignores the multiplicities, but (5,5,5,1,0,0,0) fails while vectors with the same parity pattern hold. So the proof must be analytic. It needs:
1. a Gaussian-limit score function on [0,1]^7 with a strict maximum at the corner z=0;
2. explicit Berry–Esseen-type control of moves of size O(√n) and larger;
3. an exact treatment of moves of O(1) coordinates, where the sign is decided by tie and parity terms of order 1/√n;
4. a finite computation for small n.

This is a substantial project. A Lean proof for all n would be expensive: binomial-sum inequalities, not a finite certificate. Finite instances alone cannot refute an "eventually" statement.

**Prior art.**
- Stylianou (Oct 2025) and his Bristol seminar abstract say the problem is open for every k ≥ 5.
- Standard and extended web searches on 2026-11-03 found no later work.
- Nothing appears in the registries at the HEADs above.
- The Day–Johnson manuscript is unpublished and unread, so it is not known whether they examined subspace profiles.

**Recommendation to root.** If analytic proofs are acceptable despite the Lean cost, this is worth a dedicated proof lane. It would be a genuine refutation of a human-posed 2025 conjecture.

## Files

- `results.json`: 20 entries.
- `claude/voronoi-k8-subspace.json`: data, plus log and script hashes.
- `claude/*.py` and `claude/logs/`: scripts and logs. `vor.py` is the checker, `subspace.py` builds profiles, the `subscan*` scripts do the orbit scans, `brute_full2.py` is the independent brute force, and `run.py` is the capped runner.
- `claude/fetched/`: the 372150 v1 PDF, its text and the fetch receipt.

**Not done:**
- No Lean, SAT/ILP or C helper was run.
- The last three vectors in the `skew2` run, including (5,5,5,1,2,0,2), were never reached. That run hit the time limit after (5,5,5,1,2,2,2), so those three were not checked.
