# H034 source audit (read-only): `c4_probe.py` @ `9ea5b055…21ba3`, protocol v2 @ `585fd2af…0812`

Both hashes verified with `sha256sum`. No execution, import, PRNG sampling, edits, children or commits. Independent arithmetic below was done in a throwaway script that re-derives formulas by hand; it does not touch the experiment.

## Verdict

**GO for the one frozen bounded diagnostic run, with no source change required.** I found no line that would crash, mis-count, leak the harness scalar, reset a cap, or let a wrong answer pass. Four items must be written into root's admission record **before** the run as pre-registered disclosures (D1–D4); the rest are notes. GO covers only this one bounded run; nothing here supports an improvement or benchmark reading.

## Verified (line refs)

| Audit item | Where | Result |
|---|---|---|
| 1M cap is all-or-nothing per tick, never exceeded | L78–80 | `total+count > cap` raises before adding; final total ≤ 1,000,000 exactly |
| 55s guard checked on every event, before cap; `guard_fired` records which | L75–80, L1276 | ok; my wall-time estimate for 1M metered events is 3–8 s, so the **deterministic event cap is the operative guard** and the outcome is machine-independent |
| Outer 60s SIGTERM → Halt → valid partial JSON; handler restored before final dump | L1188–1192, L1270 | ok; the SIGTERM path is practically unreachable because the 55s guard fires first |
| Refuse overwrite; valid pending JSON written before any work; rewrite via seek/dump/truncate | L1184–1186, L1286–1290 | ok; exit 3 on existing path (L1303–1305) |
| Censorship semantics: active arm `incomplete`, later arms `untested`, no cleanup after Halt | L1155–1158, L1200–1201, L1271–1273, L1281–1285 | ok |
| Kernel subtotal: subtract only *completed* inverse expansion | L253–274, L510–520 | ok; interrupted M/S tracked separately (L272–274) |
| Shared `x1+x2` → exactly 6A/edge; paired (5b−3)M+2bS+6bA; full (5b−3)M+bS+6bA | L538–565 | hand-verified; b=0 and b=1 edge cases pass |
| Eager all roots → infinity-before-x seed scan → index freed before leaf → roots retained | L666–672, L700–704, L711 | ok; no early exit |
| Batch completes, reference check, then inspect in edge/sign order; stop at first equality | L744–767 | ok; overshoot keys charged (L747) |
| Independent ordinal decode vs maintained (s,t,x) row bases | L476–483, L724–738, L601–606 | the recurrence matches `edge()` and the finite contract L16–18 exactly |
| Recovery σ=+1 then −1, d=0 skipped, verify vs original Q; null → fallback | L613–630 | algebra checked: k=(σa′−a)/(b−σb′), zero root k=−a/b |
| Fallback: release → R → Q+RG → primary (tag⊕1, first config, Hc) → verify → d−R | L770–779, L948–974 | ok; never started after Halt |
| H019 per-INDEX schedule, baby-O skip, giant-O verified, out-of-cap keys generated/paid/not queried, lazy advance | L898–931, L833–869 | ok; coverage L(D+1) ≥ q−1 holds for all four fixtures |
| Streams: tags, arm ids 0/16–21/1, label order a then b, η=1+draw(p−1), R=draw(q), LCG+rejection | L49–50, L393–416, L471–473, L660–668, L953–954 | match protocol L61–70 |
| Harness k isolation; compare only after solver's own verification | L1243–1249, L1145–1153 | ok |
| Capacity table + omissions for all fixtures before first arm | L1195–1217 | ok |
| Runtime public parameters equal `EXPECTED` | L376–390, L1208–1211 | hand-recomputed: all four tuples match |
| Metadata hash paths exist (`research/findings/…`, interpreter) | L1161–1170 | checked on disk; no FileNotFoundError path |
| No builtin `pow`, dict lookup solving, warmup, retry, or tunable | whole file | none |

## Required pre-run disclosures (not source changes)

**D1. The matched-peak filter admits the primary by construction (L1052–1060), and at q73/q103/q271 the primary's declared peak exceeds every candidate-only stage.** `fallbackst` copies the primary's own capacity into the candidate lifecycle, so `peak ≥ primary` always; L1060 and protocol L179 ("if primary does not fit, invalidate") are unreachable. Independent recomputation of the L977–1068 formulas:

| q | candidate-only peak (bits) | primary (arm16) | lifecycle peak | admitted | omitted (margin) |
|---|---|---|---|---|---|
| 73 | 9739 (leaf) | 9998 | 9998 | 16, 19, 20 | 17 (−66), 18 (−196), 21 (−26) |
| 103 | 9982 | 10124 | 10124 | 16, 19, 20 | 17 (−66), 18 (−196), 21 (−4) |
| 271 | 10653 | 11006 | 11006 | 16, 19, 20, 21 | 17 (−130), 18 (−388) |
| 8053 | 24355 | 17404 | 24355 | all six | none |

The 8192-bit register reserve is ~85% of every small-q stage, so omissions are decided by per-array 64-bit headers and null codes on margins of 4–388 bits. Root must record: (a) the chosen reading (fallback stage inside the lifecycle, per protocol L145/L263) and that L179 is therefore vacuous; (b) the expected omission set above, to be confirmed against the emitted JSON; (c) the direction of the asymmetry is conservative against the candidate (control at Hc gets ≥ memory). Do **not** "fix" this by filtering on candidate-only stages: at q73 the primary would then fail by 259 bits and the whole run would be `Invalid` at fixture 0.

**D2. Control setup builds every center, offset and stride by independent double-and-add (L799–804), not incremental addition.** This inflates control setup by roughly 7% (q73) to 17% (q8053) of the per-control total relative to a `center_{j+1}=center_j+w·step` construction. It is protocol-permitted ("each control independently pays setup") and does not affect correctness, but it biases any candidate-vs-control event comparison in the candidate's favour. Record it as a known baseline-unfavourable convention; it reinforces the existing ban on a cost headline from this run.

**D3. Predicted terminal state.** My independent static estimate (events, inclusive of reference phases and release):

| stage | q73 | q103 | q271 | q8053 | writer allowance |
|---|---|---|---|---|---|
| roots+powers | 13.5k | 14.7k | 20.7k | 216k | 30k/33k/46k/480k |
| seed scan+recovery | 2.8k | 3.0k | 3.6k | ≤11k | 15k/15k/20k/100k |
| leaf (full edge cap) | 8.5k | 9k | 16k | 90k | 40k/50k/80k/750k |
| per control (Hc) | 8.6k | 9.5k | 18.5k | 65–70k | 50k/60k/100k/350k |

Writer allowances are upper bounds by 2–9×: defensible as allowances, not as predictions. Costs **omitted from the four named allowances**: capacity tables ≈22k, certification ≈8k, public checks ≈54k (forced q73 fallback ≈10k inside), explicit O/G/−G cases ≈50–70k; ≈130–150k total (≈14% of cap). Running total through q271 ≈ 535–600k. Expected censoring point: inside the q8053 seed-7 **controls** (after its candidate completes, ≈227k seed-only or ≈320k if leaf reached); if my per-event costs are ~30% low, inside the q8053 seed-7 candidate's root construction. In every scenario q8053 seed 19 is untested and q73/q103/q271 complete. Record this as the pre-registered expectation so a q8053 cap is a predicted outcome.

**D4. `*_unrecoverable` outcomes need a post-hoc check.** The candidate falls back on a null seed/leaf match (protocol L104, L143), whereas H019 raises `Invalid` (L929). A recovery bug would therefore be masked as `seed_match_unrecoverable` → fallback → correct answer → harness pass. `recovery_attempts` (L623, L628) records σ and verified/zero-denominator but not the labels. For any `*_unrecoverable` case root must reconstruct labels from the recorded label stream and, with the known k, confirm the correct σ really had d=0. Practically, a broken `recover` would also fail the public check at L1112–1113 and send essentially every q73/q103 case to fallback, so detection is near-certain; this is a classification duty, not a code gap.

## Minor notes (no action needed)

- Unticked branches on verification booleans (L629, L910, L926, L972, L1150) and `len()` at L447: a few dozen events in total.
- Forced fallback (L1122) and explicit cases (L1232) use seed 7, so their R, η, ζ and label draws coincide with the q73 seed-7 sampled case. Everything is rebuilt; this is not output/setup reuse under protocol L214.
- `Prefix.scratch.ints` (L796) is allocated, paid and declared but unused; the candidate's fp sections 5–9 are likewise over-provisioned. Symmetric and declared.
- `Meter.indices` leaves one final `lt` unpaid when a loop `break`s; negligible.
- Baseline's first baby block deterministically hits the (G,G) tangent/vertical exception; `exception_side_pair` counts will include it and must not be read as a naturally reached branch.

## Not accepted here

No GPU calibration, no asymptotic inference, no improvement claim. Seed-only vectors (the expected outcome at q73/q103) are labelled by `stop_class`/`leaf_reached` and cannot become a headline. Verified improvement remains NONE. Root alone integrates.

---
*Factory usage — local bridge. This turn: 962,104 tokens · ≈2,975,436 Factory credits. Saved session total: 962,104 tokens · ≈2,975,436 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
