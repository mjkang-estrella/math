# expanded-corpus-r61 — Claude Opus 5.5 investigator handback (2026-11-01)

Counts are unchanged: 6/20 beyond the 39 prior. Nothing is self-accepted, and both candidates below carry zero credit until independent review and root acceptance.

## Assignment and provenance

- 40 reserved MathDB IDs, 366272 to 367107 (`reservation.json`).
- `scripts/extract.py` re-extracted every raw line from the bound corpus chunks: exact raw bytes in `raw/<id>.jsonl`, plus chunk path, one-based line, chunk SHA-256, raw-line SHA-256 and statement SHA-256 in `extracted.json`. It also wrote `history-matches.txt`, a grep of campaign prose and JSON by ID and title.
- The extract script was copied from r60. The only change is `grep` replacing `rg`, which is not installed in the subprocess path.
- All 38 arXiv source pages were fetched over public HTTP and textified (`sources/`, one receipt per fetch). Plain-text helper: `scripts/ctx.py`.

## Registries (GitHub `/commits/HEAD`, fetched 2026-11-01T17:54Z)

- OpenAI/math: HEAD 4eaee87548250b2682affda7d05d947c05554bae, unchanged.
- Omega: HEAD 615d1d58b1cf668e5979245ecb6bdc9ac5ec1525. Its parent is the previously verified 8824ef07e683ac10ae019a2a355bc08dedac4985, and the only file added is `docs/develop/theory/AURIC_CIRCLES_PERIODS_AND_ENDOGENOUS_CLOCKS_V78_CONTINUATION.md`. That doc is unrelated, so the cached D5/Problems trees still apply.
- Path screen of the cached D5/Problems trees and the OpenAI preprint listing for both candidate topics: no relevant entries (`outputs/registry-path-screen.json`). This was a path screen, not a reading of proof bodies.

## Candidates (two small exact refutations, both with full Lean endpoints)

### 1. MathDB 366834 — caterpillar maximum-centre conjecture

Source: Hurlbert survey arXiv:2501.16144v4, Conjecture 39, attributed to Zhang–Ran–Huang, DAM 2024.

- Witness: an 11-vertex caterpillar with spine leaf counts (1, 2, 1, 0, 2), at r = 6 < α = 7.
- Its maximum 6-centres are exactly the two leaves on v4, and v4 has degree 3, while Δ = 4.
- This refutes the universal reading and the charitable existential reading. Among caterpillars with n ≤ 11 it is the unique strong failure up to reversal, so it is minimum.
- A diagnostic family with fixed r = 5 and growing α suggests the failure is not a large-r artefact.
- Ordinary proof: `PROOF-366834.md`. Lean: `formal/CaterpillarCenter.lean`, endpoints `not_caterpillarCenterConjecture`, `not_caterpillarCenterConjectureWeak` and `witness`.
- Caveats: the literal statement also fails trivially at r = 1 and r = 2; that is not claimed. The original DAM wording is unread (paywall, no arXiv version).

### 2. MathDB 366371 — Keller–Petrov Conjecture 7.4 (majorization ⇒ line-embeddable)

- Witness: a six-point, tie-free ordinal space whose identity enumeration has the majorization property for every k. Repeats and permutations are handled by a proved reduction to strictly increasing lists followed by a kernel-checked finite check.
- It does not embed in ℝ: the embedding order is forced, and then five comparisons add up to 0 < 0.
- The source had sufficiency only for n ≤ 4. A diagnostic scan finds no counterexample at n = 5, even with ties.
- Ordinary proof: `PROOF-366371.md`. Lean: `formal/OrdinalLine.lean`, endpoints `not_majorizationConjecture` and `witness`.
- Significance caveat for review: classical measurement theory already shows bounded-order cancellation conditions are insufficient. This witness is a concrete chain-majorization failure, and no prior counterexample to this specific conjecture was found.

### Lean replay (both modules)

- Run `python3 scripts/replay.py`. It copies the sources into an empty `replay/fresh`, scans the proof files for forbidden tokens, builds with the pinned Lean 4.34.1 `lean -j1 -DwarningAsError=true -o` (build logs are empty), runs `leanchecker` on both modules, and audits every local constant of each module by module index, generated auxiliaries included.
- CaterpillarCenter: 52 constants. OrdinalLine: 95 constants.
- Allowed axioms are only `propext`, `Classical.choice` and `Quot.sound`. No unsafe or partial local constants exist: `_unsafe_rec` was avoided by using `List.rec` helpers. There is no sorry, admit, axiom, native_decide or ofReduceBool; finite facts use `decide +kernel`.
- Result: `replay/replay-result.json`, PASS. Peak anonymous RSS was at most 780 MiB and each run took at most 7.5 s wall.
- Trust limit: the cached mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 oleans are trusted as prebuilt; there was no upstream rebuild.

## Other dispositions (full entries in `results.json`, exactly 40)

Excluded (7):

- 366438 — inherited root exclusion (supertoken: routine adaptation).
- 366458 — already solved and formalised in the earlier 2026-10-25 algebra lane.
- 366489 — Furtula–Oz conjecture is known. Gao, arXiv:2503.01343, proves it, and the k-range follows from Saber et al. 2501.01295 plus the n ≤ 10 data. The full 2501.01295 body was read; for 2503.01343 only the statement was read.
- 366625 — resolved in its own source.
- 366816 — the source says a proof is claimed in [9], and the MathDB wording is confused.
- 367083 — the source v2 says Conjecture 7.1 was proved by Saengrungkongka.
- 366485 — a definition, not a claim.

Sustained but parked, with diagnostics:

- 366514: exhaustive n = 6 and closed-multiplication sweeps found no non-H_{a,b} λ₃-extremal graph.
- 367075: all 4,165 digraphs with n ≤ 4 and all 59,049 oriented graphs with n = 5 are 2-colourable.
- 366489: a layer identity, cM₂ = Σⱼ (2j − 1) e(H_j, L_j), was explored before the published proof was found.

Parked after reading the statement (famous, asymptotic, or outside reach with no tractable exact route): the remaining 29 IDs.

## Resources and state

- Every run went through `scripts/limited.py` or `scripts/replay.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS cap 6 GiB.
- One early Python sweep hit the 140 s cap and was killed by its own timeout; it was rewritten. Two other runs were killed by the CPU cap, also handled.
- Full logs are in `logs/`, with copies in `outputs/`. The C diagnostic `scripts/c/lir.c` is compiled with the bundled `leanc` (no system C compiler).
- No background jobs remain. There were no git operations and no shared-ledger edits.
- External access: arXiv HTML, abs and API; the GitHub API (two HEAD calls); and four web searches. No 403 or 429 responses were encountered.
