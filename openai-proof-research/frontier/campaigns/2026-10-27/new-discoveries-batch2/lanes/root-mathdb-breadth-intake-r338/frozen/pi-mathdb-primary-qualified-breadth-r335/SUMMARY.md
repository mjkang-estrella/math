# r335 — MathDB primary-qualified breadth screen (next 50 disjoint reserved IDs)

Lane: `pi-mathdb-primary-qualified-breadth-r335` (solo breadth delegate; root-only orchestration; no children; no shared/index/ledger/git/public mutations).

## Scope and method

1. **Freeze before content.** 28 sha256+size bindings recorded in `bindings.json` before any scientific content was read: r334 reservation/queue/coverage-status, r332 frozen `coverage-delta.json` (233 IDs), r326 frozen ranked queue, r301 inventory manifest, all 20 normalized corpus chunks, r304 `accepted-exclusions.json` + `historical-dispositions.json` (bound before read; zero overlap with the 50 reserved IDs). Immutable in-place references only — **no corpus copy was made**.
2. **Root manifest validated read-only.** The r334 `verify.py` logic was replicated without writing to r334: reserved IDs re-derived from the ranked queue match `reserved-ids.json` (50 disjoint, full-statement, open), all r334 payload hashes verify. Result: `work/freeze-result.json` — PASS, 2026-10-31T01:45:46Z.
3. **Corpus verified before content.** All 20 `mathdb-normalized-chunk-0001..0020.jsonl` hashes match the r301 inventory manifest before any record was read.
4. **Full-statement screen.** All 50 reserved records extracted to `sources/reserved-records.jsonl` (sha256 a2bb73e8…, 66,675 bytes) and each **literal full statement** read. Zero MathDB HTTP requests (429 hold). Public primary HTTP/search only; Exa rate-limited 3 queries (not retried); live `equilibrium.pdf` 404 → preserved copy used. No claim of exhaustive current-registry clearance.

## Achieved coverage

- **50/50** reserved IDs: literal full-statement screen, compact disposition each (`dispositions.json`).
- **3/50**: primary bodies and successor/prior documents retrieved and retained under `sources/` with UTC/hashes (`provenance.json`); decisive exact calculations executed under the pinned helper guard.
- Metadata screening tags were **not** treated as technical review. Open labels / empty solution arrays were not treated as novelty.

## Dispositions (50)

| category | count |
|---|---|
| proposed | 2 (389505, 388271) |
| proposed_with_novelty_objection | 1 (384757) |
| resolved_publicly_reported | 1 (387118 — Kourovka 21.38: affirmative record, Thompson's-F subgroup with spread exactly 1) |
| rejected_deep | 37 |
| rejected_ill_posed_or_fragmentary | 5 (384786, 386938, 388885, 388970, 388984) |
| rejected_likely_publicly_subsumed | 2 (385905 — Cocks–Pinch resolves the literal k=13 ask; 388108) |
| rejected_expensive | 1 (384989 — rank-156 unit lattice, SVP-type) |
| rejected_infeasible_by_design | 1 (389362 — RSA-1024) |

## Proposals (ranked; root allocates each separately)

1. **389505** — Explicit bound for symmetric sets on S². Mechanism: intrinsic-isometry extension lemma (Gram) → orbit of finite G ≤ O(3) → classical bound |G| ≤ 120; **decisive exact calculation done**: explicit 120-point I_h-orbit of p=(2,3,6)/7 with 30 distinct latitudes, not on a great circle (exact ℚ(√5) determinant ≠ 0). The proposer's guess (60, truncated icosahedron) is false under the literal statement. Certificate small. Objection answered: not a routine corollary — the extension step is substantive.
2. **388271** — Erickson/Eppstein all-k shortest intervals. Open since 1997; no published progress found. Exact controls show the argmin-monotone D&C is valid exactly on convex-gap inputs (C4 pass) and fails in general (C2 counterexample). Delegate routes: extend subquadratically, or prove a superlinear bound in a named model. Both endpoints publishable.
3. **384757** — AIM Polypartition 2.3 (ranked **with a strong novelty objection**): exact counterexample (z+5)³ → x²+19x+216 (disc −503) answers the literal question, but Brändén–Jochemko publicly disproved Brenti's conjecture for the shifted operator on the same hypothesis class, and Athanasiadis (JLMS 2025) published the positive family. Recommend **do not allocate**; park unless root values the one-line unshifted delta.

## Integrity notes

- Counts unchanged: 9 additional / 39 total / next 40. No new coverage IDs claimed. No Lean, no manuscript.
- Helper-script failures preserved: `sum()` on ℚ(√5) tuples concatenated instead of adding (caught by unit-norm assert), negative-index wrap in the Eulerian recurrence (A₁ computed as 2), and an out-of-range Monge cell — all fixed and re-verified; nothing was silently papered over.
- A separate final verifier (`verify.py`) re-checks every original binding hash, re-extracts all 50 reserved records from the hash-verified chunks and byte-compares them to the retained copy, and verifies the exact payload set with SHA256+sizes (excluding only `manifest.json` and `verification-receipt.json` by exact relative path); it exits **nonzero** on any failure. Integrity verification is not mathematical or novelty clearance.
