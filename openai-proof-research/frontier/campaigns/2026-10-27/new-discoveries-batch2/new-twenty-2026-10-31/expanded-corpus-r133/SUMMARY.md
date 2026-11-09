# expanded-corpus-r133: summary (Claude Opus 5.5 investigator)

Lane date: 2026-11-03. There are 20 reserved IDs (reserve5 rule). Every disposition is in `results.json`, keyed by ID, with exact provenance: chunk, one-based line, chunk/raw/statement sha256, and `raw/<id>.jsonl` holding byte-exact lines with their newline. The lane records 0 accepted credit and nothing is self-accepted; root decides.

## Headline: one candidate, 345545 (Defant–Propp stack-sorting degree)

Defant and Propp (arXiv:2002.07144, Electron. J. Combin. 2020) defined the degree of noninvertibility deg(f) = (1/|X|) Σ_y |f⁻¹(y)|². In Conjecture 4.4 they conjectured that lim deg(s : S_n → S_n)^{1/n} lies in (1.68, 1.73), where s is West's stack-sorting map. Defant later proved a lower bound of 1.62924 (Troupes, Theorem 7.29) and restated the conjecture as open.

**Result (ordinary proof complete; Lean not run).** The limit is > 1.733, so the conjecture is false. Numerically the limit is ≈ 1.953.

The new ingredient (`candidate-345545/CANDIDATE.md` §3.3):
- Take two binary trees indexed by postorder. The transitive closure of their two descendant orders is again a postorder forest (closure lemma).
- Combined with the forest hook-length formula, this gives d_n = Σ_{(B,B')} Π_j 1/h_j.
- A block recursion over common cut points evaluates this sum in roughly n⁶ time.

Certificates (exact integers, `candidate-345545/certificate.json`):
- P_50 = 50!·d_50 with P_50·100^51 > 4·51·50!·173^51. Iterating the a = b case of source inequality (1) then gives lim ≥ (d_50/204)^{1/51} > 1.733.
- Alternatively, using only the source's sup formula: P_78·100^79 > 79²·78!·173^79.

Verification diagnostics:
- The DP equals brute force for n ≤ 10.
- An independently derived two-stack automaton matches the DP for n ≤ 14.
- The shape-pair closure formula equals brute force for n ≤ 6.
- Source inequality (1) and the elementary recursion hold on all exact data (`outputs/inequality1_check.txt`).

Scope note: MathDB paraphrases deg as "maximum fiber size". That is a paraphrase defect: the maximum fiber is C_n, so its limit is 4 and the literal record fails trivially. The candidate addresses the source quantity.

Prior art (bounded): web searches found no later bound, refutation, or OEIS entry for P_n = 1, 4, 26, 224, 2356, 29064, …. Omega was at HEAD c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539 (moved from b576c901). Path screens of its complete D5 (13753 entries) and Problems (1698 entries) trees found no match. The OpenAI/math HEAD is unchanged at 4eaee87548250b2682affda7d05d947c05554bae; the cached preprints listing has no match. These are path screens only.

Lean: there is an UNCOMPILED draft `candidate-345545/lean/StackSortDegree.lean`. It contains the literal definitions (recursive s on lists, deg per Definition 1.1 over `Equiv.Perm (Fin n)`), the endpoint `¬ ∃ L, Tendsto (deg n)^(1/n) → L ∧ 1.68 < L < 1.73`, and the lemma chain, with `sorry` placeholders mapped to the ordinary proof. Estimated cost is medium-high, dominated by DP correctness. A cheaper kernel plan:
- Evaluate the DP only to n = 20.
- Iterate the elementary root-split recursion G_n ≥ 4G_{n−1} + Σ_{i=1}^{n−2} C(n−1,i) G_i G_{n−1−i} to n = 300, which gives a bound > 1.77.

Truncating the DP to at most 3 trees per side still gives 1.7556 at n = 80 (see below).

## Other dispositions (all 0 credit)

| ID | Outcome | Key reason |
|---|---|---|
| 373432 Matryoshka asymptotics | EXCLUDED_KNOWN_2026 | Proved by J. Liu's note (2026-06-15) and Danus arXiv:2607.06447 Theorem 4 (S ∈ [0.00542831750, 0.00542831848]). The lane had independently found the exact linearized solution p(n) = n⁴+18n³+107n²+242n+168 and the averaging argument. |
| 366896 cubic mp | EXCLUDED_WORDING_VACUOUS | The original (arXiv:2012.10330, all 4 versions) and the survey both literally say n/3 + O(n), which is trivially true. The intended form is unstated. |
| 348108 BA-tree energy | EXCLUDED_LITERAL_SOURCE_TYPO; substantive part parked | Source item (5) as printed is self-contradictory (two limits as α → ∞). |
| 343305 powerful 132 | PARKED_WITH_DATA | Exact PAv_n, Ω_n, SAv_n for n ≤ 14. Archer–Graves 2026 give the SAv asymptotics; PAv and Ω still need a full enumeration. |
| 364593 A_n derangements | PARKED_BOUNDED_NONFINDING | Imprimitive maximal subgroups are fine for n ≤ 36 (minimum margin 0.037 at n = 9). Primitive subgroups need GAP. Lean is infeasible. |
| 365487 AMO Thouless | PARKED_BOUNDED_NONFINDING | Diagnostic Decimal inertia computation beyond q ≤ 95: q = 97, all p, holds (margin 3.2e-4 at p = 33); p ∈ {1,2} holds for odd q ≤ 129. Not validated; Lean-heavy. |
| 358865 firefighting 1/8 | PARKED_PROOF_ROUTE_SKETCH | Continuum race analysis supports optimality of the source n²/8 strategy. No finite certificate is possible for a limit. |
| 382036 affine partitions | PARKED_NO_MECHANISM | v4 (2026-09-08) refutes two other conjectures, not this one. Bounds remain n+1 vs 3n/2 − O(1). |
| 373769 Conway–Guttman | PARKED_PARTIAL_SOURCE_PROGRESS | The source author covers 6 of 7 classes; 4312 is open. |
| 352805 integer tetrahedra | PARKED_LOW_SIGNIFICANCE | The authors flag the denominator 229024 as a tentative choice. |
| 341220 splitters | PARKED | "Asymptotic" is loose (for n = 1 the constant is √(2/π)); the Θ version is not completed. |
| 352307, 372765, 368881, 358020, 373488, 382109, 347590, 341979 | PARKED_HARD | Asymptotic, analytic or extremal statements with no tractable full-scope or finite-certificate mechanism. Each primary conjecture passage was read or located (see `results.json`). |

## Lessons and observations for root
- 345545 matches the reserve5 pattern exactly. The authors' "computational verification" was a typical-fiber average, E[X^{1/n}]. That undershoots the degree's growth (E X)^{1/n} because log X has linear variance, so the conjectured window was off by 0.2.
- 373432 shows that a 2026 AI-system paper (Danus/Rethlas) had already solved an asymptotic conjecture posted in March 2026. Searching such sources early is essential.

## Resource and conduct notes
- All numerical processes ran through `scripts/limited.py`, one at a time: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS cap 1.8 GiB, AS 4 GiB, MALLOC_ARENA_MAX=2. Receipts are in `logs/*.receipt.json`.
- Two runs hit caps by design:
  - `stack_automaton` hit the RSS cap at n = 15, after n ≤ 14 was complete.
  - `amo3_p12_a` hit the wall cap after q ≤ 129.
- No Lean, lake, leanchecker or solver binaries were run. There was no git, no shared-ledger edit, no upload, no browser, and no child agents.
- Incident: one ad-hoc fetch (Liu note and 2607.06447) resolved its output directory from stdin and briefly created `new-twenty-2026-10-31/downloads/`, which is outside the lane. That directory contained only those two items. I moved them into this lane at once and removed the directory; the receipts note this.
- An early broad grep over the frontier tree was stopped after 600 s and replaced by a bounded search.
- Downloads are untrusted. Each is in its own `downloads/<key>/` directory and was read only via pdftotext and python -I.

## Files
- `results.json`: 20 entries.
- `extracted.json`, `raw/`: exact provenance.
- `outputs/statements.txt`
- `candidate-345545/`: `CANDIDATE.md`, `certificate.json`, `lean/StackSortDegree.lean` (UNCOMPILED).
- `outputs/stack_pairs_P_1_82.json`: exact P_n, sha256 a6e6efe6c7323a6c341aba7cb5f899c4898fdc97117ac86e5e8f03ee7179b287.
- `outputs/stack_pairs_trunc_K{2,3,4}.json`
- `scripts/`:
  - stack_deg_brute, stack_deg_shapes, stack_deg_dp, stack_pairs_int, stack_deg_automaton, stack_certificate, stack_simple_rec(2), stack_guess, stack_pairs_trunc
  - matryoshka(2), powerful132, derange_imprim, amo_measure(2,3)
  - extract, fetch, fetchpdf, limited, build_results
- `logs/`: full outputs.
- `sources/`: arXiv abstract pages, registry HEADs, Omega trees.
- `downloads/`: source PDFs with receipts.
