# SUMMARY — common-basis-final-replay-pi-r1 (MathDB 332371, 2026-11-05)

Final execution/reproduction check plus two root-mandated dossier corrections for the Lasoń
common-basis conjecture refutation (MathDB 332371). Zero credit; final root acceptance remains a
separate decision. Model: GLM-5.3 Flash via Pi (`spark/GLM-5.3-Flash-EXL3`), per the 2026-11-05
steering. All frozen inputs verified before and after (194/194 hashes).

## Final replay (enforced, fresh lane)

- Source archive `source-only-proof.zip` verified (SHA-256 `31a3c2a7…cbfa`, 18 members), safe-extracted
  with per-member hashes; the 12 mathematical modules are byte-identical to the shipped
  `lean-source-manifest.json` and the author lane manifest; no preexisting oleans; symlinks: none.
- Toolchain pinned and verified: Lean 4.34.1 commit `5045d005…` (binary SHA-256s match the completed
  fidelity review's pin manifest); mathlib checkout head `d13f23b…` as pinned. Upstream packages
  trusted prebuilt; no source-to-olean attestation claimed.
- **24/24 strict stages**: for each of Bases, Cases0–7, Endpoint, Final, Audit:
  `lean -j1 -M3500 -DwarningAsError=true` then `leanchecker`, all rc=0, under per-call caps
  (≤2 CPU affinity, CPU 120 s, wall 140 s, sampled-RSS 6 GiB guard, RLIMIT_AS 12 GiB, 64 GiB hard
  guard, `MALLOC_ARENA_MAX=2`). Max observed wall 30.6 s; max sampled RSS 2.23 GiB.
- **Independent body-presence audit** (byte-identical copy of the completed fidelity review's
  `ReviewAudit.lean`): 106 namespace declarations (98 theorems, 8 defs, 0 other), every non-axiom
  declaration carries a body, zero local axiom declarations, transitive axiom closure of
  `CommonBasis332371.counterexample` exactly `propext, Classical.choice, Quot.sound`. No
  sorry/admit/new-axiom/unsafe/native_decide anywhere in the accepted development.
- **Negative controls** (scoped, fail as required): `CtrlWrongEndpoint` (false endpoint claim) and
  `CtrlFalse`, both rc=1 with explicit `decide ... is false` errors.
- Three earlier harness attempts failed (relative-path cwd bug; audit-path root constraint; a name
  resolution typo) and are preserved under `logs/attempt*/`; only the final run counts.
- Full record: `replay-result.json` + per-stage receipts `replay/receipts/*.json` + logs.

## Correction 1 — Section 7 version history

"printed, with identical quantifiers, in five arXiv versions…" → "in **arXiv versions v2–v5**, the
journal, and an independent 2016 workshop problem list". Rationale: v1 predates the formulation
(only White Conjectures 1–2); v2/v3 carry it as Conjecture 13, v4/v5 as Conjecture 2.5. The
fine-grained correct history elsewhere (page 1 and the reference [1]) is retained unchanged.

## Correction 2 — Section 8 / REPRODUCE replay-tooling honesty

The original `replay.sh` was overclaimed. Root inspection: it inherits PATH/HOME/Lean env and does
not enforce affinity, CPU/wall/RSS/AS limits, nonempty-build-dir rejection, or dependency-hash
verification. The paper's Section 8 now states this and points to the new enforced wrapper
`capped_replay.py` (Python stdlib: safe extraction, fresh build dir, minimal HOME, pinned PATH,
fresh LEAN_PATH, `-j1 -M3500 -DwarningAsError=true` + `leanchecker`, per-call caps as above, every
command/env/exit/peak logged, toolchain+mathlib pin verification, upstream trust explicit). The
original script ships byte-identical in both archives, labeled historical; `CORRECTIONS.md` inside `source-only/` records the honest history.

## Status corrections

The independent strict Lean-fidelity audit (common-basis-fidelity-pi-r2) is complete, verdict PASS on
all gates; the paper's evidence-status block, section-6 header and title block were updated
accordingly, and the fresh final replay of this lane is recorded. The narrow module-origin/full-type
audit supplement (common-basis-audit-supplement-pi-r3, running elsewhere; not polled or copied) and
final root acceptance are pending and are nowhere claimed.

## Deliverables in this lane

`paper.pdf` (corrected, 6 pages, all pages rendered+inspected in `qa/`), `paper-src/` (corrected
generator), `scripts/capped_replay.py`, `REPRODUCE.md` (corrected), `results.json`,
`replay-result.json`, `source-only-proof.zip` and `full-dossier.zip` (new copies; originals
byte-identical inside; manifests `archive-manifests.json`, `MANIFEST.sha256.json`, `hashes.txt`),
`receipts/frozen-before.json`, `receipts/frozen-after.json`, `audit-src/` (audit copy + controls).

## Scope

Exact common-basis refutation only; no White-refutation, minimality, new-matroid or global-priority
claims; no human authors or institutions invented; no shared/author edits; no git; no network
publication.
