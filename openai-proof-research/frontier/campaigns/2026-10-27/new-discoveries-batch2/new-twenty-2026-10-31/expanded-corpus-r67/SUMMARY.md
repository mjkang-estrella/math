# expanded-corpus-r67 — summary (2026-11-01)

Assignment: the 40 MathDB IDs 371562–372579 in `reservation.json`. Campaign count unchanged at 8/20 beyond 39. Proposed credit: 0 (root decides).

## Headline candidate: 371639 refuted, with a full Lean endpoint

The conjecture is Clow–Kumar–Pragada, arXiv:2511.18747v1, Conjecture 7.5: there is a c > 0 such that χ(G) > ω(G) implies χ_f(G) < c ω(G) |V(G)| / |V(H)|, where H is a largest induced subgraph with χ(H) ≤ ω(G).

It is false for every c. Take the k-th lexicographic power of C₅ (α, ω ≤ 2^k on 5^k vertices) and add 5^k isolated vertices. Then χ_f ≥ (5/2)^k, while the right-hand side is at most 2c · 2^k. A hub variant gives connected counterexamples.

- Ordinary proof: `PROOF-371639.md`.
- Lean: `theorem Clow371639.not_conjecture : ¬ Clow371639.Conjecture` and `theorem Clow371639.not_connectedConjecture`. Definitions use Mathlib's `cliqueNum` and `chromaticNumber`; the LP fractional chromatic number and the largest-H order are defined in `Defs.lean`.
- Axioms: propext, Classical.choice, Quot.sound.
- Fresh extracted strict replay PASS: 6 modules built and leanchecked, 111 local declarations audited, 3 rejected mutations (`lean/fresh-replay-r1/replay-receipts/result.json`).
- Source-only zip sha256: `a68b79c41ac63ee06d32757d71ce265762dd6c2203402f2540061eb5cebbc25e`.
- Prior art (bounded, 2026-11-01): arXiv abs page shows v1 only. Web searches found no refutation. The current Omega HEAD 790d20da has D5/Problems subtree SHAs identical to r65's complete listings, with no relevant path. OpenAI HEAD 4eaee875 is unchanged and its preprints listing has no relevant path.
- For reviewers on significance: the counterexample is short, and padding (or a hub) is essential, since vertex-transitive graphs satisfy the inequality with any c > 1. It refutes the source conjecture exactly as stated, not a MathDB paraphrase. It says nothing about the odd-wheel problems that motivated it. Independent fidelity and significance review is needed.

## Other sustained routes

- **372105** (panchromatic/bipanchromatic equality): found the 6-vertex counterexample independently, but it is already refuted publicly (arXiv:2610.08042, arXiv:2610.27133, and an Omega D5 file plus issue #8518). Known; excluded.
- **372569** (spectral gap of trees): exhaustive numerical check for all trees with n ≤ 19 agrees with the conjecture. Parked.
- **372373** ((3,4)-tournament spanning path): SAT at n = 7 and 8 hit the cap without symmetry breaking, and the local search was too weak to count as evidence. Parked; the next step is isomorph-free generation.
- **371679** (saturation of K_s ∨ P_k): the k = 3 case is already known from Faudree–Gould 2013 Thm 9(i), which matches the formula. k ≥ 4 is parked.

## Dispositions (exactly 40, in `results.json`)

| Outcome | IDs |
|---|---|
| candidate_refutation_lean_endpoint | 371639 |
| known_resolution | 372105, 372272, 372394, 372551 |
| parked_partial_known | 371679 |
| parked_sustained | 372373, 372569 |
| parked_hard | 371562, 371569, 371571, 371617, 371628, 371641, 371691, 371701, 371741, 371757, 371759, 371760, 371788, 371790, 371824, 372004, 372014, 372078, 372117, 372136, 372137, 372141, 372163, 372188, 372239, 372245, 372276, 372330, 372467, 372577, 372578, 372579 |

Each entry records the exact raw line (chunk, line, chunk/raw/statement hashes), the primary source receipt and hash, the label, the recovered definitions and quantifiers, the attempt and remaining gap, and the history, registry and prior-art screen scopes.

Notes:
- 371569 and 371757 are the same assertion.
- The equality wording of 372014 is defective for non-regular graphs; that is a wording issue only.
- The MathDB statement of 372276 garbles Δ ≥ 3; the Δ = 3 case is known.

## History

A history grep over campaign prose and structured reports (`history-matches.txt`, 82 lines) found only the reservation ledger entries and incidental numeric substrings. No earlier exclusion or route exists for any of the 40 IDs. This is not a global semantic clearance.

## Integrity, resources, limits

- `outputs/validation.json` checks raw lines, chunk hashes, source receipts, the reuse of the registry listings and the replay PASS. It is integrity-only.
- Every process ran under 2 CPUs, CPU 120 s and wall 140 s, with sampled RSS of 6 GiB or less (Lean replay also under systemd MemoryMax=6G). Receipts are in `logs/`.
- No background jobs, git operations, shared-ledger edits, uploads or external messages.
- The Lean cache was used read-only.
- Web-search results are leads; only the fetched receipts are treated as read primary sources.
