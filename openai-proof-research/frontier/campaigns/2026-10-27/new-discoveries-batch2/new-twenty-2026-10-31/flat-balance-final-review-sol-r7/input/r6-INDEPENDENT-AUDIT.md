# INDEPENDENT-AUDIT — MathDB 352972 (flat-balance), lane r6

Auditor: independent Pi audit, this lane only, no children. Credit 0; 52/60 unchanged; no self-acceptance. Root routes Sol FINAL delta/manuscript review and acceptance.

## 0. Scope and compliance

- First two commands exactly as tasked: `bootstrap.py` (printed all four AGENTS/TASK files; receipt `bootstrap-receipt.json`) and `verify_frozen.py before` -> 1091 frozen paths, 0 mismatches (`frozen-before.json`).
- All Lean/audit/probe/bookkeeping/PDF operations through `runner.py LABEL` / `write_lane.py`, except the two tasked exceptions. Two throwaway diagnostic probes were written to `/tmp/p*.lean..p15.lean` during API/tactic isolation; documented here, content-free, outside the frozen set.
- Protected lanes `code-loop-sets-formal-pi-r5`, `polynexus-partition-formal-pi-r9`: touched only via the frozen hash list (0 paths of theirs in it; no reads).
- No production proof edits; no git/network/installs; resources per runner caps (CPU 120 s, wall 140, dev-guard 130, AS 12 GiB, RSS guard 6 GiB, arena 2).

## 1. Fresh setup (receipt `receipt/FRESH-SETUP.json`, before any compile)

- `build/` empty at setup (listing recorded). Copied source hashes: FlatBalance `4a4ca90e...889d`, FlatBalanceBridges `05bf58c7...c70` — equal to root bindings and `input/author-source-hashmap.json`.
- Lean 4.34.1 bin sha `e8baaa7...d550`; leanchecker sha `ccef1bf...6fcbe`; version string commit `5045d0056413266e57c625dcd7c365b10e377c52`; mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612` (git-verified in the pinned packages dir).
- `LEAN_PATH` = own `build/` + pinned upstream package lib dirs only (mathlib, batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible). No author/other-project build dirs.

## 2. Rebuild + kernel recheck (primary), then cleanroom replay

Primary (`check.sh`/`checker.sh` -> runner labels `lean_*`, `leanchecker_*`), strict `-j1 -M3500 -DwarningAsError=true`:
- `FlatBalance` build EXIT=0, `FlatBalanceBridges` build EXIT=0; module-name kernel checker EXIT=0 both.
- Post hashes: `FlatBalance.olean aeb27a12596525015e0d88f64113eb578b3e20d02ad8b3b541481c28f5a574e0`, `FlatBalanceBridges.olean 66d371e6f3fa39810b6a090a377001ce0495d2dbe144f592accd0d67fcd36b75` (`receipt/PRIMARY-REBUILD-HASHES.json`).

Cleanroom (`cleanroom/`, source-only copies, `cleanroom/CLEANROOM-SETUP.json` with EMPTY build listing and no olean copies; isolated `LEAN_PATH` = cleanroom build + same pinned upstream):
- build/checker EXIT=0 x4 (runner labels `cleanroom_*`).
- Result: **byte-identical oleans**, same two hashes as primary. No copied oleans, no project paths.

## 3. Independent environment audit (`audit/EnvAudit.lean` -> `results/352972-env-audit.json`, label `audit_EnvAudit`, EXIT=0)

- Enumerated ALL declarations of both production modules from the environment header (`constNames`), no namespace filter: **156** — 122 theorems, 31 defs, 1 inductive (`SimpleGraph`), 1 constructor (`SimpleGraph.mk`), 1 recursor (`SimpleGraph.rec`); plus generated `casesOn/recOn/noConfusion/injEq/sizeOf`, match `eq_N/splitter`, `_proof_*`, `_simp_*`, `_sparseCasesOn_*`, private mangled `_private.src.*` auxiliaries — all present in the inventory with kind, `DefinitionSafety`, `ReducibilityHints`, origin module (`getModuleIdxFor?`), full type, full value via **`value? (allowOpaque := true)`**, direct constant deps, per-constant `collectAxioms`.
- Missing module/name => `throwError` (fatal), never warn-and-pass; exercised (the run would have exited 1).
- Safety: **0 unsafe, 0 partial, 0 opaque**; no `extern`/`implemented_by`/`native_decide`/`sorry`/`admit`/`axiom` declarations in either source (token scan; the single textual occurrences are doc-comment prose). No attributes (`@[...]`) in sources.
- Axiom union over all 156 decls: exactly `{propext, Classical.choice, Quot.sound}` (fatal gate would fire otherwise). `quot` kinds: none. The audit's own recursion is audit-tooling, outside the production import closure, reported here as such.
- Full transitive constant closure of BOTH endpoints (BFS over `getUsedConstantsAsSet` of type+opaque-allowed value):
  - `not_flat_balanced_conjecture`: closure 4808 constants; local (production-module) closure **75**; axioms `{propext, Classical.choice, Quot.sound}`.
  - `not_flat_balanced_conjecture_via_bridges`: closure 4810; local closure **77**; axioms `{propext, Classical.choice, Quot.sound}`.
  - Independent BFS axiom closure == `collectAxioms` for both ( enforced; mismatch is fatal).
  - The bridges endpoint closure contains `not_balanced_of_one_lt_discrepancy` and `K33_discrepancy_gt_one` and does NOT contain `K33_not_balanced` — the revised endpoint provably goes through the generic bridge, not the witness-specific lemma.
- Full unabridged types/proof values printed with `pp.proofs`, `pp.deepTerms`, `pp.proofs/deepTerms.threshold` raised, `pp.maxSteps` 1e6, `maxRecDepth` 8192: 153/156 decls carry values (the 3 without are the inductive/ctor/rec — value-less by kind); machine JSON + full log preserved (`logs/*_audit_EnvAudit.log`).
- Author-claims verdict: "156 declared names" **confirmed**. Author closure "14" and default-`value?`/default-pp audit **confirmed deficient**: with default `value?` theorems have no value, so their closure stops at the first theorem layer — the honest closure is 75/77. Author PDF R2 numbers flagged (see §6).

## 4. Source-fidelity / semantic delta R1 (independent reading; no math done)

Checked against the actual sources (`src/`, hashes above):
- Generic layer unconditional in `G` and `V`: `cliqueFinset_zero`, `cliqueCount_zero`, `cliqueCount_of_card_lt`, all three cutoff lemmas — no hidden endpoint hypotheses; empty vertex type included (definitions are `Finset`-based; EMPTY behaviour independently exercised, §5 P1–P4).
- Flatness is exactly source Def 2.2: every edge in ≤ 2 triangles (`triangleSet` card ≤ 2), unordered `Finset`-based, irreflexive+symmetric `SimpleGraph`; no planarity/connectedness/no-isolated-edge conditions anywhere.
- Counts are actual unordered-clique cardinals (`powerset.filter` + `Finset.card`); no proxy counts, no one-sided `Nat` subtraction: all differences taken in `Z` (`Int.natAbs` of a `Z` difference), `natAbs_cast_abs`, `discrepancyNat_cast_int/_real`, `balanced_iff_absInt/_Real` — cast layer exact.
- Convention separation: `evenCliqueSum_decomp` (even(c0) = c0 + evenPos) with the two conventions distinct objects; `oddAddEvenCliqueSum` parity partition; cutoff independence makes the bounded sums the true finite-support totals.
- Revised endpoint `not_flat_balanced_conjecture_via_bridges` is derived through `flat_not_balanced_exists_via_bridges` -> `not_balanced_of_one_lt_discrepancy` <- `K33_discrepancy_gt_one` (witness-specific `K33_not_balanced` unused there) — no idle bridge lemmas; the endpoint has no hidden assumptions (`∀ V (hV : Fintype V) (G), Flat -> Balanced` with explicit instance binder).
- No idle lemmas detected: every bridge lemma named in the module is referenced by the endpoint closure or the controls; no theorem with hidden endpoint hypothesis found.

## 5. Controls (all built and run under the provided runner; strict flags)

- Author positive suite `audit/CtrlAuthorPos.lean` (copy, sha `e5794d4f...e4f9`) EXIT=0: C1–C10 covering generic c0, witness/empty instances, finite support, cutoff 9, convention decomposition, Int cast, discrepancy-only contrapositive (C9 uses no `Flat` — verified by reading; binder absent by construction), real bound equivalence.
- Author negative-shape suite `audit/CtrlAuthorNeg.lean` (sha `d176c4d2...e08a`) EXIT=0: ten `example`s — six-vertex nonvacuity, a real edge, c2≠8 and c2≠0, pos-discrepancy ≠4 and ≠0, c0-discrepancy ≠ pos-discrepancy, pointwise `¬(Flat→Balanced)`, `Balanced→¬Flat` contrapositive shape, `Flat K33` provable. These are positive proofs, NOT failed-compile tests — confirmed.
- Independent positives `audit/ControlsIndPos.lean` EXIT=0 (P1–P11): EMPTY-graph `c0=1`, all positive counts vanish, **empty graph is Balanced with discrepancy |0−1|=1**, second cutoff 20 and cutoff on the empty graph, parity partition 6+10=16, integer abs form =4, real abs form =4, real cast of discrepancy =4, existential witness restated, conventions distinct 10 vs 9. Nonvacuity and coverage independently established; no fabrication.
- Independent expected-failures `audit/ControlsIndNeg.lean` EXIT=1 **by design**, six true failures with informative residuals exactly `9 = 8`, `10 = 9`, `4 ≤ 1`, `6 = 7`, `4 = 3`, `0 = 9` — proxy/encoding/convention detectors; true expected failure exits, separated from diagnostic failures (all six are the intended `unsolved goals` at the intended lines; nothing else).

## 6. Manuscript QA (skill applied; announced)

Read `~/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md` before any PDF work and applied its read/review workflow. **No new PDF authored** => marker not run (read-only; per skill). Author PDF preserved untouched; no retroactive marker claims.

- `input/author-flat-balance-bridges.pdf` sha `26438 bytes`; pdfinfo: 3 pages A4 595x842, groff/Ghostscript, no encryption.
- Rendered ALL 3 pages (`pdftoppm -png -r 100`, `manuscript/authorpdf-page-{1,2,3}.png`) and inspected each as an image: consistent margins/typography, correct section numbering 1–8, no missing glyphs, no clipped/overlapping text, no black boxes, no bad wraps; ASCII hyphens only (0 unicode dashes in text layer).
- Content cross-checked against the ACTUAL certificate: pins correct; 156 decls correct; c(0)=1,c(1)=6,c(2)=9, odd 6 / even 10 / 9 pos, discrepancies 4 and 3 — all match theorems; bridge-layer description matches sources; "no bridge lemma is idle" true.
- **Flags (factual, for root/Sol; not silently fixed):**
  1. R2 "transitive constant closure of each endpoint contains 14 local constants" — actual full closure 75 / 77 (the 14 is an artifact of default `value?`).
  2. R2 endpoint-axiom split claim ("{Classical.choice, Quot.sound}; propext only via bridge layer") — both endpoints' axiom closures are exactly {propext, Classical.choice, Quot.sound}.
  3. "TEN positive proofs": the controls file has 11 `example`s (C3 split a/b); ten only under that labeling.
- Receipt `receipt/pdf-qa.json` (+ runner receipt), renders hashed.

## 7. Author-results manifest staleness

Root record (`input/root-r5-integration.json`): stale entry claimed `05a0da...3127`, actual `1dadb...f375`; author files preserved untouched; this lane's `results/352972.json` is a NEW independent record hashing current bytes (no placeholder/self-circular entries).

## 8. Reproduction recipe

1. `timeout 20 python3 -I -B bootstrap.py`
2. `timeout 140 python3 -I -B verify_frozen.py before`
3. `bash check.sh FlatBalance && bash check.sh FlatBalanceBridges` (strict build via runner)
4. `bash checker.sh FlatBalance && bash checker.sh FlatBalanceBridges` (module-name kernel recheck)
5. Cleanroom: `cd cleanroom && bash check.sh <M> && bash checker.sh <M>` for both M; compare olean sha256s (byte-identical).
6. `bash audit.sh EnvAudit` (environment audit; EXIT 0; writes `results/352972-env-audit.json`).
7. `bash audit.sh CtrlAuthorPos && bash audit.sh CtrlAuthorNeg && bash audit.sh ControlsIndPos` (EXIT 0) and `bash audit.sh ControlsIndNeg` (EXIT 1 expected; six residuals).
8. `timeout 140 python3 -I -B verify_frozen.py after`.

## 9. Deliverables and manifest

`results/352972.json` (keyed record), `results/352972-env-audit.json`, `results/source-crosscheck.json`, `receipt/*` (all runner receipts incl. every failed intermediate compile of audit tooling — true exits preserved, no unchanged failed reruns: every rerun followed a diagnostic-driven fix), `logs/*` full unabridged, `manuscript/authorpdf-page-*.png`, `receipt/pdf-qa.json`, `cleanroom/CLEANROOM-SETUP.json`, `receipt/FRESH-SETUP.json`, `receipt/PRIMARY-REBUILD-HASHES.json`. Complete sha256 manifest: `SHA256-MANIFEST.json` with named terminal exclusions (the manifest itself and the verifier-written `frozen-after.json`, plus `tmp/` scratch), noncircular. Frozen re-verified after all writes.

## 10. Gates passed by this audit (and only these)

rebuild ✓ kernel-recheck ✓ cleanroom byte-identical replay ✓ environment audit (156/0/0/0; 3-axiom union; closures 4808/4810, local 75/77) ✓ source-fidelity reading ✓ controls 4-file ✓ manuscript 3-page visual+content QA ✓. NOT claimed here: acceptance, novelty, source-acceptance counting, Sol FINAL review — root's routing.
