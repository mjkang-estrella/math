# Reproduction — root-review lane common-basis-final-replay-pi-r1 (CORRECTED, 2026-11-05)

Corrected reproduction document for the MathDB 332371 common-basis refutation. Supersedes the pi-r2
REPRODUCE.md where the two corrections below apply; the pi-r2 lane and its archives are inputs and
were not modified.

## Corrections carried by this lane

1. **Section 7 version history.** The paper previously said the conjecture is printed "in five arXiv
   versions". v1 predates the formulation (only White Conjectures 1–2); the conjecture appears with
   identical quantifiers in arXiv v2/v3 (Conjecture 13) and v4/v5 (Conjecture 2.5), plus the journal
   and an independent 2016 workshop problem list. Corrected to "arXiv versions v2–v5, the journal,
   and an independent 2016 workshop problem list". The correct fine-grained history elsewhere in the
   paper is unchanged.
2. **Section 8 / replay tooling honesty.** The original `replay.sh` inherits the ambient PATH, HOME
   and Lean environment and sets only `LEAN_PATH`, a pinned-binary PATH prefix and
   `MALLOC_ARENA_MAX=2`. It does **not** enforce CPU affinity, CPU/wall/RSS/address-space limits,
   does **not** reject a nonempty build directory, and does **not** verify dependency hashes. The
   paper now says exactly that and points to the enforced wrapper; the original script is retained
   byte-identical in the archives as a historical, non-cap-enforcing record.
3. **Status.** The independent strict Lean-fidelity audit (common-basis-fidelity-pi-r2) is COMPLETE
   (verdict PASS on literal source, mathematics/semantics, strict replay 24/24, package scope,
   documented reproducibility limits). The fresh final replay below was performed in this lane. The
   narrow module-origin/full-type audit supplement and final root acceptance remain pending and are
   not claimed anywhere here.

## Enforced replay wrapper (the actual reproduction path)

`scripts/capped_replay.py` — Python standard library only.

```
python3 -I -B scripts/capped_replay.py \
  --zip <source-only-proof.zip> \
  --expect-zip-sha256 31a3c2a71dbfbdd723f1a3f5fb58c297fba9cf685e9ffdebd8dd71ccadb1cbfa \
  --lean-bin  /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin \
  --lean-packages /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages \
  --pin-receipt <common-basis-fidelity-pi-r2>/receipts/pinned-binaries-deps.txt \
  --author-manifest <expanded-corpus-r250>/lean-source-manifest.json \
  --workdir replay \
  --audit audit-src/ReviewAudit.lean \
  --control audit-src/CtrlWrongEndpoint.lean \
  --control audit-src/CtrlFalse.lean
```

Enforced per heavy call: ≤2 CPU affinity (`sched_setaffinity`), CPU 120 s (`RLIMIT_CPU`), wall 140 s
(process-group kill), sampled-RSS 6 GiB guard, `RLIMIT_AS` 12 GiB with a 64 GiB sampled-VmPeak hard
guard, `MALLOC_ARENA_MAX=2`, minimal private `HOME`, `PATH` pinned to `LEAN_BIN` first, fresh
`LEAN_PATH` = new build dir + discovered external package trees. Safe zip extraction (relative paths,
regular entries, no symlinks, per-member SHA-256), fresh build dir refused if nonempty, no preexisting
`.olean`, toolchain binaries and mathlib checkout verified against the completed review's pin manifest.
Upstream packages are TRUSTED PREBUILT — no source-to-olean attestation is claimed or checked.

## What was run in this lane (logs in `replay/logs/`, receipts in `replay/receipts/`)

1. Frozen-input verification BEFORE — 194/194 OK → `receipts/frozen-before.json`.
2. The enforced replay above. Result (`replay-result.json`, mirrored at lane root):
   - archive SHA-256 and 18 members verified; 12 modules byte-identical to the shipped AND author
     manifests; no preexisting oleans;
   - 24/24 strict stages: `lean -j1 -M3500 -DwarningAsError=true` + `leanchecker` for Bases,
     Cases0–7, Endpoint, Final, Audit, all rc=0 under caps (max wall 30.6 s; max sampled RSS 2.23 GiB);
   - independent body-presence audit `ReviewAudit.lean` (byte-identical copy of the completed
     fidelity review's audit; hash receipt `receipts/reviewaudit-copy.sha256`): 106 declarations (98 theorems, 8 defs), zero local axiom declarations, no
     declaration without a body, transitive axiom closure of `CommonBasis332371.counterexample`
     exactly `propext, Classical.choice, Quot.sound`;
   - negative controls, scoped explicitly and failing as required: `CtrlWrongEndpoint.lean`
     (false endpoint claim, `decide` proves it false, rc=1) and `CtrlFalse.lean` (rc=1).
3. Corrected paper build: `python3 -I -B paper-src/build_paper.py` → `paper.pdf` (6 pages, letter).
4. PDF QA: `pdftoppm -png -r 100 paper.pdf qa/pg`; all six pages rendered and visually inspected
   (`qa/pg-1..6.png`); PDF skill operation marker run before first authoring command.
5. Archives rebuilt (originals byte-identical inside; additions only): `source-only-proof.zip`
   (18 original members + `capped_replay.py` + `CORRECTIONS.md`; no oleans/caches) and
   `full-dossier.zip` (original reviews/raw record/source receipts/old scripts retained +
   `verification/` receipts, logs and failed-harness attempts + `CORRECTIONS.md` +
   `paper-root-review-copy/`). Manifests: `archive-manifests.json`, `MANIFEST.sha256.json`,
   `hashes.txt`.
6. Frozen-input verification AFTER → `receipts/frozen-after.json`.

## Failed harness attempts (preserved; never counted as passes)

`logs/attempt1-relative-path-fail`, `logs/attempt2-audit-path-and-sampler`,
`logs/attempt3-auditname-resolve-typo` — wrapper defects fixed before the final run; their logs and
result records are retained, and only the final `replay-result.json` (ok=true, 24/24) counts.

## Integrity rules honored

- The 12 Lean modules are byte-identical to `expanded-corpus-r250/lean-source-manifest.json`
  (verified twice: wrapper + staging).
- No source file modified to make anything pass; the two paper corrections are factual only.
- No git, no uploads, no shared-ledger writes, no installs, no cache-permission changes, no upstream
  rebuild; the audit-supplement lane was not polled or copied from.
- Final root acceptance remains a separate decision; zero credit assigned here.
