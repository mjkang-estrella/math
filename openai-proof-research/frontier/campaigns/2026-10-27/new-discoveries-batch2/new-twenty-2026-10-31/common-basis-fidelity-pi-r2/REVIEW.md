# Independent review — MathDB 332371 (common-basis conjecture, Lasoń)

Reviewer lane `common-basis-fidelity-pi-r2`, 2026-11-05. Scope: literal source fidelity,
mathematical/semantic fidelity, strict Lean replay/audit, package honesty. Novelty/significance
is the other reviewer's lane; root alone accepts; zero credit assigned here.

## Verdict

**PASS on all five review gates.** Verdicts and evidence are ID-keyed in `review.json`.

| Gate | Verdict |
|---|---|
| Literal / source | PASS |
| Mathematics / semantics | PASS |
| Strict replay / audit | PASS (24/24 stages, independent) |
| Package scope / honesty | PASS |
| Reproducibility limits | DOCUMENTED (residuals below) |

## 1. Literal and source fidelity

Conjecture 2.5 was read verbatim in the retained primary bodies: arXiv v5 (`sources/1601.08199v5.txt`,
Conjecture 2.5), v4 (identical), the journal body (`sources/lason-journal.txt`, Selecta Math 27:18 (2021),
DOI 10.1007/s00029-021-00633-6, HTTP 200 receipt), and v2/v3 where it is Conjecture 13 with the same
quantifiers. v1 predates the formulation (only White's Conjectures). The MathDB statement in
`raw/332371.jsonl` is quantifier-identical. No source version restricts to simple matroids; parallel
elements are explicitly in scope (the paper's own Prop 2.3/2.6 closure conditions and the parallel-pair
definition). The endpoint is the literal instance-negation: a `Matroid (Fin 9)` with ground `univ`,
`ncard = 2*4+1`, `eRank = 4`, both deletions partitioned into two disjoint bases, and a full
`¬∃ B C D, TwoBasePartition (E-{1}) B C ∧ TwoBasePartition (E-{6}) B D` over arbitrary `B,C D` —
not a weakened proxy.

## 2. Mathematics and semantics

Independent recomputation (`scripts/independent_check.py`, fresh GF(2) elimination, no author code):
76 bases; basis exchange verified for every ordered pair and element; E−{1}-extendible bases 32,
E−{6}-extendible 24, intersection empty; the two printed partitions are genuine. The parallel pair
(labels 1,4; equal column 6) is an ordinary pair of distinct labeled elements. `matroid-certificate.json`
and the `baseList` literal in `lean/Bases.lean` match my computation set-exactly (76 entries).

Semantic bridges, checked against pinned mathlib `d13f23b7`:
`Matroid.ofIsBaseOfFinite` (IndepAxioms.lean:523) sets `E := univ` and `IsBase := BP` definitionally
(`ofIsBaseOfFinite_E`, `ofIsBaseOfFinite_isBase`, both `rfl`); the exchange property is *proved* by 76
exhaustive `decide` lemmas, not postulated; `eRank = 4` comes from `IsBase.encard_eq_eRank` on a real
base (Rank/ENat.lean:90); `TwoBasePartition` uses the real `N.IsBase`. Partition-order is free under the
existentials, so shared-base-in-second-position is covered; `A = B` is impossible (disjoint, 4+4 into 8)
and the logic is symmetric; `noCommon` decides the negation totally over all 76 bases with the true
`dx = univ-{1}`, `dy = univ-{6}`. Nonvacuity: hypotheses exhibited in-kernel
(`first_partition`, `second_partition`).

## 3. Strict replay and audit (independent)

Fresh extraction of `lean-packet-final.zip` (sha256 `37ac427f…272fd`, verified) into `audit/pi-r2-src`;
member hashes equal the author manifest; sanitized-source scan clean. All 12 modules rebuilt
`lean -j1 -M3500 -DwarningAsError=true` then `leanchecker`: **24/24 rc=0** under 2-CPU/120 s CPU/140 s
wall/12 GiB AS with 6 GiB sampled-RSS guard (`audit/*.receipt.json`, `audit/pi-r2-logs/`).

My `ReviewAudit.lean` (independent of the author's): exactly **106** namespace declarations
(98 theorems, 8 defs, 0 generated-other), every non-axiom declaration carries a body
(`value?` with `allowOpaque := true` — plain `value?` is `none` for theorems by design), zero local
axioms, count asserted. Transitive closure of the endpoint and `#print axioms`: exactly
`propext, Classical.choice, Quot.sound`. The author's `Audit.lean` also re-passed inside my rebuild
(106 AUDITED, no forbidden metadata).

Negative controls: `CtrlSad.lean` proves the audit machinery detects `sorryAx` (and that
`-DwarningAsError=true` flags a sorry — its exit 1 is the control working); the perturbed-column check
in `independent_check.py` shows the 32/24/empty-intersection conclusions are discriminating, not vacuous.

## 4. Package and history honesty

All nine `ARTIFACTS.json` hashes verify. The final ZIP contains exactly the 12 sources. Frozen inputs:
**548/548 hashes match before the work and again after**, bytes preserved. Historical artifacts are
retained and correctly labeled: `lean-packet.zip`/`lean-packet-replay.zip` are byte-identical to the
final packet; `replay-attempt-history.json` records the sanitizer false-positive and the PATH-less
checker failure; early failed builds' `sorryAx` reports stay in the failure logs, none in the success
chain. Pinned binaries hashed in `receipts/pinned-binaries-deps.txt`; mathlib git HEAD verified
`d13f23b7…1612`; cache untouched.

## 5. Reproducibility limits (residuals, non-blocking)

- RSS sampling observes the child leader only — not a transient-peak/cgroup guarantee (stated in receipts).
- Upstream oleans trusted prebuilt; no source→olean attestation (per task convention).
 `leanchecker` re-checks kernels of oleans; it is not a second elaboration.
- Author `Audit.lean` lacks a body-presence check; supplied by this review's `ReviewAudit`.
- Endpoint states rank via `eRank` (ℕ∞); identical to the ordinal rank here (base encard 4).
- Novelty/significance, source-history completeness: other reviewer's lane.

## Artifacts (this lane)

`review.json`; `scripts/` (verify_frozen, independent_check, pi_r2_runner, pi_r2_replay[_ctrl]);
`logs/` (frozen verify pass1/2, independent_check); `audit/` (fresh src/build/logs, receipts,
ReviewAudit/CtrlSad); `receipts/` (pinned-binaries-deps, env-and-historical-zips); `manifest.sha256`.
