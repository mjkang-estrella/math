# Audit supplement r3 — MathDB 332371 (common-basis), lane `common-basis-audit-supplement-pi-r3`

Review sub-agent (Pi, `spark/GLM-5.3-Flash-EXL3`, high thinking), 2026-11-05.
**Narrow scope:** close exactly the two evidence gaps root identified in
`common-basis-fidelity-pi-r2`; the successful 24/24 r2 replay is preserved and NOT repeated.
Zero credit; no acceptance; no novelty/significance claim.

## Verdict

**PASS on all five supplement gates** (ID-keyed in `review.json`).

| Gate | Verdict |
|---|---|
| G1 module-origin inventory reconciled | PASS |
| G2 full unabridged declaration types | PASS |
| Body / safety / metadata / axiom-closure over module-origin set | PASS |
| Negative control (sorryAx detection) | PASS |
| Frozen inputs preserved (640/640 before and after) | PASS |

## Gap 1 — actual originating module (not name substring)

Selection is per-constant via `Lean.Environment.getModuleIdxFor?` over
`env.header.moduleNames` — generated and private constants included by construction.
Result: **107 declarations** in modules `Bases, Cases0..Cases7, Endpoint, Final`;
`Audit` declared none; this lane's module none. The namespace-substring set (r2's basis)
is **106**; the difference is exactly `Matroid.ofIsBaseOfFinite.congr_simp`, a Lean-generated
simp-congruence cache theorem created while elaborating `Final` (no `CommonBasis332371` in
its name). It carries a value and passes every check. Sets reported explicitly; nothing forced.

Per-module: Bases 5; Cases0–6 10 each; Cases7 6; Endpoint 10; Final 16. Kinds: 8 defn, 99 thm,
0 axiom/ctor/rec/induct/opaque/quot. Generated aux visible in the census: `._proof_1`, `.eq_1`,
`._simp_1_1`.

## Gap 2 — full unabridged types

All **107** types printed in full (`SUPTYPE-BEGIN <name>` blocks in `logs/lean-Supplement.log`),
with `pp.deepTerms=true` (default `false` is the `⋯` source), `pp.maxSteps=1000000`,
`pp.proofs=true` (default `false` renders proofs `⋯`). Omission-marker absence (`⋯`, `…`) is
**asserted inside the audit per declaration** — a marker would fail the compile. The endpoint
type is the literal instance-negation over `N.E = univ`, `ncard = 2*4+1`, `eRank = 4`, both
deletions 2-partitioned, `¬∃ B C D …` — unchanged from r2's reading.

## Re-checked per declaration (now over the module-origin set)

`value?(allowOpaque := true)` present for every thm/def (none lacking); no local axioms; no
unsafe/partial/extern/implementedBy/`_unsafe_rec`; transitive closure ⊆ `{propext,
Classical.choice, Quot.sound}` for **each** of the 107 and for the endpoint
(`#print axioms`-equivalent via `collectAxioms`). Control: a sorryed lemma reports
`[sorryAx]` (`logs/lean-CtrlSupp.log`).

## Runs (all in this lane; imported r2 build strictly read-only)

| Stage | rc | wall | Receipt |
|---|---|---|---|
| frozen before | 640/640 ok | – | `receipts/frozencheck-before.json` |
| `lean -j1 -M3500 -DwarningAsError=true -o audit-build/Supplement.olean audit-src/Supplement.lean` | 0 | 1.93 s | `receipts/lean-Supplement.receipt.json` |
| `leanchecker Supplement` (new olean only) | 0 | 1.46 s | `receipts/checker-Supplement.receipt.json` |
| control `lean ... CtrlSupp.lean` (no warningAsError; warning is the signal) | 0 | 0.91 s | `receipts/lean-CtrlSupp.receipt.json` |
| frozen after | 640/640 ok | – | `receipts/frozencheck-after.json` |

Lean 4.34.1 (`5045d005…`, bin hashes = r2's recorded values); mathlib `d13f23b7…` cache
untouched; `LEAN_PATH` = lane build : r2 `pi-r2-build` : pinned package dirs
(`receipts/toolchain-env.txt`). Caps 2 CPU / 120 s CPU / 140 s wall / 12 GiB AS / 6 GiB
sampled RSS — all stages far under; no stray cache (`python3 -I -B`, absolute paths);
all processes terminate before return. Exact commands in `scripts/pi_r3_audit.sh` and the
`bash -x` trace `logs/orchestration.trace`; per-stage logs in `logs/`.

## Remaining issues (non-blocking, recorded)

1. The r2 "106" remains correct **as a substring count**; the authoritative module-origin
   inventory is 107. Consumers should state which basis they quote.
2. Upstream oleans trusted prebuilt per campaign convention; `leanchecker` re-checks kernels,
   not a second elaboration (unchanged r2 residual).
3. A fully-explicit (`pp.explicit`) second rendering was prototyped and dropped: with proofs
   printed it exceeded the 120 s CPU cap on instance-heavy types. The single canonical
   unabridged form is complete and omission-free by in-audit assertion.

## Artifacts (this lane)

`review.json`; `scripts/` (pi_r3_audit, pi_r3_runner, verify_frozen_r3); `audit-src/`
(Supplement.lean, CtrlSupp.lean); `audit-build/Supplement.olean`; `logs/` (per-stage,
orchestration trace); `receipts/` (stage receipts, frozencheck-before/after, toolchain-env);
`manifest.sha256`; frozen `frozen-inputs.json`/`launch.json`/`TASK.txt` untouched.
