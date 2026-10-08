# Protocol review: retained report, qualified by root

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h034-protocol-cost-fable-20261008-r1`.
Provider/model: Factory/claude-fable-5.1. Completed, no pending children.
This report is not accepted wholesale. Protocol v2 preserves per-INDEX H019
alternation (not the review's per-block suggestion), checks regular arithmetic
components separately from final-block advancement, and labels its seed-rate
and resource estimates as rough model calculations. See protocol v2.

# H034 protocol v1 review (cost / experiment admission)

Read-only. No edits, runs, imports or children. Files read: RESEARCH_LOOP.md, RESEARCH_TEAM.md, research/STATE.md, experiments/H034/protocol.md, findings/H034-finite-contract.md, H034-matched-memory-cost-screen.md, H019-xonly-baseline-screen.md, plus the H034 hypothesis/mathematical/qualification records and H030's c2_protocol.md and the LCG/fixture/peak conventions in H030/c2_probe.py for convention matching.

## Verdict

**Conditional GO for source construction only**, subject to the amendments below being frozen into a protocol v2 (with its hash recorded) before any source hash is taken. **No execution approval**: no source exists. One finding (F1) changes what the diagnostic can actually test and must be acknowledged in the protocol's purpose statement before root decides whether the cap is worth spending.

The protocol is consistent with the finite contract (Emax, ell rule, 2ell² roots, lexicographic edge order, plus-before-minus, batches of at most ell, U=2Emax, affine hash, prepend-and-scan, fresh blinded fallback) and with the H019 screen (D, prefixes 0..ceil(D/2), center index ellH+j(2ellH+1), stride k(2ellH+1), paired inversion). Fixtures, LCG constants, rejection rule and target/hash tags match H030 exactly. Cap/censorship/no-retry language is correct. The sign-recovery example (Q=2G, labels (-1,1),(-3,1): sigma=+1 gives d=0 and is skipped, sigma=-1 gives (3+1)/2=2) checks out.

## Reviewer-derived parameters (hand arithmetic, writer must confirm; the protocol should freeze them)

| q | ell | roots 2ell² | edges ell³ | Emax | U | Hc | D | prefix idx | B for (k,ellH) |
|---|---|---|---|---|---|---|---|---|---|
| 73 | 3 | 18 | 27 | 13 | 26 | 16 | 13 | 0..7 | (2,1)→6, (1,2)→5 |
| 103 | 3 | 18 | 27 | 16 | 32 | 16 | 15 | 0..8 | (2,1)→6, (1,2)→5 |
| 271 | 3 | 18 | 27 | 25 | 50 | 32 | 24 | 0..12 | (4,1)→12, (2,2)→10 |
| 8053 | 7 | 98 | 343 | 135 | 270 | 128 | 127 | 0..64 | (8,1)→24, (4,3)→28 |

q271 is borderline on the ell rule (4·3⁶=2916 vs 9q=2439) and uses 25 of 27 edges; q8053's 98 roots agree with the protocol text.

## Findings and required amendments

**F1 (major, purpose): on these fixtures the candidate will usually terminate in the seed phase, so the leaf/archive/recovery path is rarely exercised on sampled inputs.** Independent uniform roots collide in x with probability about 2/q per pair. Expected equal-x root pairs plus zero roots: q73 ≈ 4.2+0.25, q103 ≈ 3.0+0.17, q271 ≈ 1.1+0.07, q8053 ≈ 1.2+0.01. Rough probability of reaching the leaf phase: ~1%, ~4%, ~30%, ~30%. Expected leaf-phase sampled cases over all eight ≈ 1.3, with roughly a 1-in-5 chance of zero. This is a tiny-q artifact (seed collision scale is ~4ell⁴/q ≈ 7q^(-1/3)), not a defect of the mechanism, but it means: (a) the "complete leaf ledger versus six controls" will exist for at most one or two cases, (b) seed-only solves are cheap and would produce a *favorable-looking* candidate vector that is meaningless against the hypothesis. A q near 2^20 would fix the ratio but its ~340 roots × 20-bit seeds alone exceed the 1M cap.
Required: state these expected seed-termination rates in the protocol; declare the diagnostic's testable scope as setup/seed/dispatch correctness, batch-arithmetic ledger (via the public ell-pair check) and the archive/recovery path *only if reached*; forbid any candidate-vs-control cost headline from seed-only cases; report leaf-reached as a per-case boolean. Root should decide with this in view whether the 1M cap is worth spending now.

**F2 (reproducibility): per-arm stream seeding is underspecified.** Protocol says every arm "restarts its declared hash stream ... uses its own state" but gives no seed/tag distinction between the candidate and the six controls. With initial state (tag xor p xor q xor seed), all seven arms in a case draw identical eta,zeta. Also unspecified: label stream seed (case seed assumed), label draw order (vertex index order, a then b assumed), eta != 0 sampling (must be 1+draw(p-1) to respect "no resampling except declared rejection"), fallback R = draw(q) from the fallback stream, and the control's role slot mapping.
Required: freeze per-arm hash initial states (e.g. tag xor arm_id with a listed arm_id table, fallback = tag xor 1 as already stated), label order, eta sampling, and control slot = hash mod (Hb/2) with role offset.

**F3 (comparability): the control's regular block subtotal is not a contract check.** Only the candidate has a falsifiable "(5b-3)M+2bS+6bA+I" regular-subtotal test. Note that 6bA presupposes computing x_i+x_j once and sharing it across both signs; the source must implement exactly that or the check will falsely fail. The H019 block cost ell·(I+3(k-1)M+2kM+2kS)+(I+3(k-1)M+2kM+kS) should be the control's declared regular subtotal with the same mismatch-is-fatal rule, so both ledgers are falsifiable.
Also freeze: alternate at block granularity (baby block j, then giant block j), query/insert in index order within a block, baby index 0 (=O) handled as sentinel; the control's first baby block deterministically hits the vertical exception, so that exception count must not be reported as a naturally reached branch.

**F4 (comparability): declare the primary comparator and the envelope's status.** Six controls per case versus one candidate makes the lower envelope a min-of-six. The protocol calls the envelope descriptive; it should also name config 1 at Hc as the sole pre-declared headline comparator. Add that the "matched peak" at these q is dominated by the 2ell² full roots with labels (roots ≈ 5k bits vs archive ≈ 8.6k bits at q8053; roots > archive at q73), so essentially every control fits even at 4Hc. This is not the asymptotic matched-memory regime of the cost screen; the grid is a convention.

**F5 (capacity filter): correct principle, needs a procedural rule.** "Declared full lifecycle logical packed peak, never target-dependent observed peak" is right. Require the writer to emit the per-fixture declared-peak table (setup stage: powers+roots+seed index+heads; leaf stage: roots+archive+heads+scratch; fallback stage) and the per-control omission decisions in the JSON header *before* the first arm runs, computed from protocol constants only. Freeze one initialization convention for both arms (heads initialized and paid; node payload declared uninitialized, matching the cost screen). Python object storage, if reported at all, labelled exactly as H030 did ("no Python-byte or exact-peak claim") and never used in the filter.

**F6 (leakage): mostly sound; three places need explicit statements.**
- Reference check per batch runs between the candidate's lookup of batch b and generation of b+1 (needed so prepaid outputs are checked when lookup stops early). Require it to be a pure function over copies of root coordinates and edge descriptors, under its own ledger scope, returning only pass/fail; mismatch fatal; nothing written back; no exception swallowed.
- No cache sharing: harness [q]G/kG power chains, the harness's Q construction, and each control's D·G and stride points must be rebuilt by each arm; no module-level memo.
- Defensive distinct-x invariant before batching: attribute it to a declared sheet (harness/diagnostic) and treat violation as fatal implementation failure, as the text says.
Harness k isolation and compare-after-return are correctly specified.

**F7 (evidence lifecycle): output must survive the inner guard and be unrepeatable.** `--output <file>` differs from H030's stdout redirect. Require: refuse to run if the output file exists; write valid partial JSON on inner cap/55s guard via try/finally; on outer SIGTERM, an absent/invalid file is recorded as inconclusive with no second run. Record which guard fired (event cap is deterministic; the 55s guard is machine dependent). Add that fallback is NOT started after a cap (censorship, as stated) and that controls run after a censored candidate are "untested", not "lost". Define the event unit (one metered modular-RAM primitive, as in H030's meter).

**F8 (cost realism, not a change to parameters): writer should supply a static event budget per stage/fixture at source review.** Order of magnitude: q8053 seed setup ≈ 98 roots × ~26 complete affine additions with expanded ~23-op inverses ≈ 10^5+ events per candidate case; six controls add perhaps 10^5 more per case. The eight sampled cases plus three diagnostic cases plausibly approach 1M. The budget is for honest admission (so a q8053 cap is a predicted outcome, not a surprise), not for retuning.

**F9 (minor):** freeze edge orientation (i = point vertex x·ell+y, j = line vertex ell²+s·ell+t, so labels are (a_point+e·a_line, b_point+e·b_line)); freeze the expanded inverse routine (Fermat chain or extended Euclid) and use the same one in every arm; state whether c4_probe.py reuses H018/H028/H030 support by hash-pinned deferred import (as H030 did) or is standalone; state release-cost convention (per record vs O(1)) identically for both arms; k in [0,q) including 0 differs from H030's 1+draw(q-1), fine but should be noted as deliberate.

## Scope of the later static source review (for whoever root assigns)

1. Stream tags/seeds per arm as frozen in v2; label order; eta sampling; R sampling.
2. Eager build of all roots, then seed scan (infinity before x), then index freed before leaf, roots retained; no early exit on zero/collision during construction.
3. Batch completes before inspection; inspection in edge/sign order; stop at first equality; overshoot charged; no later queries.
4. Recovery: sigma +1 then -1, d=0 skipped, verify against original Q; null → fallback, not continued search.
5. Fallback: release → sample R → Q+RG → primary config at Hc with tag xor 1 → verify → return d-R; never started after a cap.
6. Controls: block alternation, no out-of-prefix query, index-0 sentinel, both candidate verifications paid, per-control rebuilt setup.
7. Declared-peak table and omission decisions computed before any arm runs; one initialization convention.
8. Ledger: completed-inverse boundary rule, raw expansion, candidate and control regular-subtotal checks, 6bA sharing, release costs, no double counting of symbolic I.
9. Reference checker purity and ordering; harness k isolation; no shared caches.
10. Output: refuse-overwrite, partial-JSON on inner guard, hashes of source/support/protocol, guard-fired field, no retry path in code.

## Out of scope / not accepted here

This review does not assess algorithmic novelty, grumpy comparators, or the asymptotic collision law, and does not treat the matched-memory crossover (price- and head-count-dependent, uncalibrated) as something this run can confirm. A favorable finite vector, especially from seed-only cases, is not evidence of improvement; verified improvement remains NONE. No Lean work is implied or requested by this protocol.

---
*Factory usage — local bridge. This turn: 555,209 tokens · ≈971,486 Factory credits. Saved session total: 555,209 tokens · ≈971,486 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
