# expanded-corpus-r167 (Claude lane, reserve7, 20 IDs 354706–374800): one candidate

**Outcome.**
- One candidate refutation: **373112**, Tyomkyn's finiteness conjecture (arXiv:2602.11892 v1 and v2, Conjecture 6.1). The ordinary proof is complete. The Lean draft is **UNCOMPILED**.
- Two finite conjectures got substantial exhaustive support: 372835 and 368246.
- A third is supported exhaustively through n = 9: 363761.
- The other IDs are settled or parked.

Accepted credit is 0 and nothing is self-accepted. Per the Claude lane restriction, no Lean, lake, leanchecker or solver was run. All numerics are capped python3 -I, run one process at a time.

**Statements and history.**
- All 20 literal records are in `extracted.json` and `raw/` (chunk, line, chunk/raw/statement sha256), extracted with `scripts/extract.py` copied from r165.
- ID/title history grep: `history-matches.txt` has no prior dispositions.
- Source arXiv IDs grepped across campaign results: only siblings were handled before (358857 and 366391 in r94, 369902 in r81, 370156 in r65).
- Every arXiv abstract page was fetched for version history (`outputs/abstracts.txt`). Sources with two versions: 373112 (v1 and v2 read, conjecture unchanged), 367172 (v2) and 362299 (v2).

## Candidate: 373112 (see `CANDIDATE-373112.md`)

**Claim.** For every even n ≥ 8 there is a symmetric abstract 2-rigidity matroid M_n ≠ R_n on E(K_n) in which K_{3,3} is independent, so "only finitely many n" is false.

**Construction.** M_n = R_n with the S_n-orbit of one free Laman basis B_n deleted. The proof uses four lemmas:
- **Lemma A:** B is free iff it has no tight set of size 4 to n − 1.
- **Lemma B:** deleting a family of free bases, no two one exchange apart, preserves the basis axioms.
- **Lemma C:** a degree-3 edge split with z adjacent to neither u nor v preserves freeness.
- **Lemma D:** if the degree set has no two consecutive integers, no exchange gives an isomorphic copy.

The family B_n starts from the 8-vertex graph `GCR`vo` (degrees 3^7 5^1) and adds two splits at a time, keeping degrees in {3, 5}.

**Verification.**
- Brute force over all vertex subsets for n = 8, 10, …, 20.
- Full exchange-axiom check of R_6 minus prisms, which reproduces the source example, plus a negative control.
- At n = 7 the method gives nothing, consistent with the author's hand check.

**Prior art.**
- Patkar–Servatius–Subrahmanyam (JCTB 1994) give the same n = 6 prism deletion. They state "many abstract rigidity matroids for n ≥ 6" but give no symmetric examples beyond n = 6.
- Nothing was found for Conjecture 6.1 itself: 2 web searches, Lean Pool, 7 GitHub queries.

**Honest credit risk: MEDIUM–HIGH.** The key idea extends the source's and PSS's own n = 6 example, and the genuinely new part is about one page. The root may rule it a source-ingredient bridge (the 336565 and 347138 profile).

**Lean cost: MEDIUM.** R_n already exists as `SimpleGraph.countMatroid V 2 3` in bryangingechen/CombinatorialRigidity at 021c2284 (toolchain v4.36.0-rc1, which needs porting or a separate replay). The draft endpoint `¬ Exceptional.Finite`, the literal negation, is in `lean/Rigidity373112.lean`, UNCOMPILED with `sorry` placeholders.

## Other dispositions

| ID | Outcome | Basis |
|---|---|---|
| 372835 | Parked, exhaustive support | Exact reduction to pseudo-chord arrangements in a disk. All 1 + 2 + 5 + 19 + 130 + 1824 arrangements with m ≤ 6 give min corners = m + 5, so the conjecture holds for all (k, m) with m ≤ 6. The open lemma is c ≥ Σ_interior (5 − \|f\|). Literal defects at k ≤ 4 and for unbounded P are zero credit. |
| 368246 | Parked, no counterexample | Literal statement omits "strong" (zero-credit defect). For strong digraphs, exhaustive through n = 9: n ≤ 8 all missing lengths; n = 9 lengths 3 to 7, with length 8 covered by source Theorem 1.5. Only K_{m,m} digraphs survive. |
| 363761 | Parked, support n ≤ 9 | All 3676 non-trivially WD connected graphs of order ≤ 9 fail with H = C4 or C5. The statement is not finitely refutable, and no uniform proof was found. |
| 364157 | Excluded, source-refuted | Mastrogiacomo Theorem 1.2 disproves the DMS conjecture. |
| 367172 | Excluded, known resolution | Companion arXiv:2505.05324 proves the Moseley–Proudfoot–Young conjecture. |
| 362060 | Parked | Part (i) is a literal misprint, refuted by the source's own double banana. In part (ii), the natural 2-sum candidates are provably not 2-edge-apex. |
| 354706 | Parked | A counterexample would need at least two Deming-K4 parts. A faithful Deming implementation is still pending. |
| 357416, 365232, 369903 | Parked | Asymptotic or existential constants. |
| 359935, 370158 | Parked | Existential characterization; deep structural. |
| 366393, 358858 | Parked | Source gives a proof sketch; general-r weighted bound. |
| 374800, 367211, 365712, 359651, 362299 | Parked quickly | Deep geometry, topology, quantum or analytic, as the brief directs. |

## Files

- `results.json`: 20 ID-keyed entries.
- `CANDIDATE-373112.md`, `lean/Rigidity373112.lean` (UNCOMPILED), `outputs/candidate-373112.sha256`.
- `NOTES.md`: the mathematics for 372835, 368246, 363761, 362060 and 354706.
- `outputs/registry-screen.json`: Lean Pool HEAD 01db1d70 (live, unchanged), 7 GitHub queries, the CombinatorialRigidity dependency record. Omega and OpenAI/math were not re-fetched; the root should re-check them live before any acceptance of 373112.
- `outputs/fetch-receipts.json`: all source fetches with sha256, over verified TLS. There were no denials.
- `scripts/`, `logs/`: reproducible capped computations.
