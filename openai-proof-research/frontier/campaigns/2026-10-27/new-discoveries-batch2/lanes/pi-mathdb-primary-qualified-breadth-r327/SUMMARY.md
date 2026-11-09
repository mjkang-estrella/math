# r327 — MathDB primary-qualified breadth screen (50 reserved IDs)

Lane: `lanes/pi-mathdb-primary-qualified-breadth-r327`. Solo worker; no child agents,
no git, no shared/ledger/index/other-lane writes, zero requests to mathdb.com (429
hold respected), no browser tabs. All computation under the pinned helper guard
(`sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`; 512 MiB AS and
group RSS, 210 CPU s / 230 wall, single-thread BLAS/OMP, `python3 -B`).

## Method and integrity

1. **Frozen before reading.** `scripts/freeze_inputs.py` copied and SHA-256-bound all
   inputs before any substantive read: r326 `reserved-ids.json`, `queue.json`,
   `coverage-delta.json` (183 IDs), `QUALIFICATIONS.md`; r301 `manifest.json`;
   r304 `accepted-exclusions.json`, `historical-dispositions.json`; r320
   `dispositions.json`/`proposals.json`; r322 and r324 `DECISION.md`
   (`work/frozen-inputs.json`).
2. **Corpus bound before read.** All 20 `mathdb-normalized-chunk-*.jsonl` files were
   SHA-256-verified **in place** against r301's own manifest (no 169 MB copy;
   `work/corpus-verification.json`), then the 50 reserved full statements were
   extracted (`work/reserved-records.json`, `work/reserved-statements.txt`).
   50/50 found; zero missing, zero extra. **Disjointness verified: 0 overlap with
   the 183 prior reported review IDs** (incl. 371202, 338289, 368302 — not re-counted).
3. **Primary sources retained** (16 + 1 files, actual bytes, per-file UTC + SHA-256 in
   `work/source-bindings.json`): full HTML bodies of 2407.19583v1 (Cayley
   permutations), 2406.01790v1 (Hollom), 2506.22284v2 (Przybyłowski), 2604.02404v1
   (Golomb), 2605.05198v1 (S-LCG); the published AJC 94(2) PDF for 2407.19583; and 12
   arXiv abstract pages. No ScienceDirect, no GitHub API/raw/codeload, no Google.
4. **Decisive calculations** (guard-logged, no raises): the Conjecture 8.8 sweep and an
   independent re-verification, plus source-consistency validations
   (`work/decisive-cayley-sweep.json`, `work/decisive-cayley-verify.json`,
   `work/decisive-cayley-validation.json`). One earlier run hit a transient
   implementation state explosion and was rescaled; one run had a dead-loop bug
   (timeout, exit 137) and was fixed — both logs are in the scripts' history, neither
   result was used.

## Headline results

- **1 proposal (364119).** Conjecture 8.8 of Cerbai–Claesson–Ernst–Golab (arXiv:2407.19583v1;
  published Australas. J. Combin. 94(2) (2025) 267–299) is **false**: p=1122, q=1112
  (same length 4, max both 2) give |Cay₅(1122)|=520 < 522=|Cay₅(1112)| (n=6: 4340<4394).
  Complete exact certificate, verified by two independent implementations, machinery
  validated against the source's own formulas ((n+1)!/2 for 112/122; the 13442/14233
  equality check reproduced). Published version checked verbatim (p.30); no public
  resolution found. This is a new-to-literature refutation candidate, not merely a
  diagnostic: the negation is existentially quantified and fully witnessed.
- **Public retirements (labels stale), body-confirmed:** 363374 — Hollom's Conjecture 6.2
  (simple digraph, model E₈) is resolved by arXiv:2506.22284v2, Thm 1.2 + Def 4.1
  (simple acyclic digraph counterexample, accepted EJC); body read and retained.
  377313 — the k-Schur involution is a public theorem (Lapointe–Morse math/0505519,
  published 2006; independently quoted in Trans. AMS): retired by direct prior theorem.
- **In-source solves/refutations:** 374999 — the source's abstract states the exact
  formula `disc(n)=2^{1-1/⌈n/2⌉}` for every n, contradicting the record's "open"
  framing (abstract-level; provisional until body read). 376076 — Voss's conjecture
  disproved for all k≥5 in-source, k=4 by Alexeev et al. (2026) (abstract-confirmed).
  361505 — counterexample announced in the source itself (abstract-confirmed; the
  record's "Zykov" attribution is garbled). 364117 — Conjecture 8.6 is refuted
  in-source pending one bounded automaton check (p∼_c q for 13442/14233; the source
  verifies p≁_cm q via 742943≠742944). 402057, 402062 — solved at record level per
  their own cached statements.
- **Scope-unclear reject:** 374594 (S-LCG) — body read shows the source's α_max is an
  algorithmic artifact; under the natural cycle-minimum reading x=2ⁿ is a fixed-point
  generator, contradicting the conjectured bound for all n≥5.
- **Holds (11):** 350633, 361105, 367622, 367849, 368242, 370443, 371246, 371547,
  378570, 380427, 382482 — concrete mechanisms and decisive next calculations are in
  `dispositions.json`. **Flags:** 361105 (the record's "refuted" status is wrong — the
  source proposes a counterexample family); 367849 (normalized statement's definition
  is not self-contained; needs body semantics); 371547 (potential in-house overlap with
  the campaign's edge-irregulator manuscript packet — root must clear before any work).
- **Rejects (30):** deep programs, famous separations, and broad AimPL/Oberwolfach
  items, each with a compact reason; per-ID fields in `dispositions.json`.

## Coverage and evidence levels (exact)

- 50/50 reserved IDs: full cached statement read and dispositioned (0 missing).
- Evidence: 5 records with retained primary bodies (364119, 364117, 363374, 382482,
  374594); 1 published-version PDF read (364119); 13 records with abstract-page reads;
  all 50 at `cached_full_statement_read` minimum. 2 kills rest on cached statements
  alone (402057, 402062 — record-level).
- **Not achieved / open:** no whole-corpus coverage claims; published-journal bodies
  not retrieved except the AJC PDF (paywalled/other routes not attempted); no GAP, no
  group libraries; the 346000/400943-style body confirmations from r320 were not
  repeated here; hold rows remain unreviewed beyond statement + abstract.
- **Counts unchanged: 9 additional / 39 total / next 40.** This lane claims zero
  accepted credit and zero coverage beyond the 50 reserved dispositions; the 364119
  refutation is proposed, not accepted (root assigns independent review).

## Failures

- First DP design (achievable-match states) exceeded 512 MiB at pattern length 5,
  m=9 — rescaled to exact enumeration sweeps; no result from the failed run was used.
- One verification run died on a dead loop (guard kill, wall 210 s) — fixed, rerun.
- EJC published version of Hollom (10.1016/j.ejc.2025.104188) not retrieved
  (Elsevier route forbidden); arXiv v2 body used instead. No other access failures.
