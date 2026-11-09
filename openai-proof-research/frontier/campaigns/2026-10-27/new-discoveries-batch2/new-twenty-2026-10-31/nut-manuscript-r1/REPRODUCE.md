# Reproduce the Nut8 proof and dossier

This is a DRAFT with zero accepted credit. Do not confuse the local safe-extraction PASS with a complete Lean replay PASS. The manuscript lane executed no Lean compilation and did not start the full replay. Root's separate nut-parent-final-r1 lane owns that acceptance gate.

## Check the delivered packet

The proof packet `nut-source-only.zip` is a byte-for-byte copy of `nut-formal-r7q/nut-r7q-source.zip`, SHA-256:

```
e4710a538ed6ef60e6649fcb288dd873db52ce613eeddca564627f39c96ef402
```

Run `python3 capped.py receipts/local-extraction-repeat.json python3 -B verify_packet.py` from this dossier. The script verifies the archive hash, forbids absolute/traversal/backslash/symlink paths and compiled binaries, extracts under safe-extracted, checks all 1,289 manifest entries, checks every formal module against frozen hashes, and scans comment/string-stripped source for forbidden commands. It does not call Lean. Repeating it writes only inside this dossier. Preserve the original receipts if a distinct run record is wanted.

## Full source-only Lean replay (root or a later verifier only)

Do not run concurrently with root's active replay. Extract `nut-source-only.zip` to a NEW EMPTY directory. Do not inject development oleans. Set these environment variables to independently installed pinned dependencies:

```
export LEAN_BIN=/path/to/lean-4.34.1/bin/lean
export LEAN_PACKAGES=/path/to/pinned/mathlib/.lake/packages
python3 -I replay.py --init-only
python3 -I replay.py --resume --steps 1
```

Repeat the last command until replay-state.json reports PASS. A bounded larger `--steps N` batch is sequential. Lean commit: 5045d0056413266e57c625dcd7c365b10e377c52. Mathlib revision: d13f23b723b8a846827a245b89c10fc7d3f11612. The original r7q instructions inside the packet are authoritative for driver behavior. Its historical fresh-final path is not required: a new empty extraction is the portable choice.

The driver strictly rebuilds 1,151 modules with warnings as errors, runs one separate leanchecker call per module, then runs 128 auditors and 18 controls. The proof closure has 1,024 local modules. Only propext, Classical.choice and Quot.sound are permitted. The auditor checks module origins, full types and opaque-accessible bodies, flags and transitive axioms, including generated companions. Distinguish records from names: development evidence has 46,045 records over 46,022 distinct names, with Nut8.unsignedPatterns.eq_1 repeated 24 times.

Each replay subprocess is limited to two CPU affinity slots, 120 CPU seconds, 140 wall seconds, sampled private RSS 5.75 GiB and MALLOC_ARENA_MAX=2. The driver refuses pre-existing oleans at initialization, checks source and saved output identities on resume, refuses unrecorded oleans and saves progress after every successful step. Its HOME and temporary paths remain inside extraction. Use exactly one active heavy process. Never use --development as acceptance validation.

## Render the manuscript

Install ReportLab in an isolated location inside the dossier if unavailable. build_paper.py currently reads the existing ReportLab dependency directory in the neighboring tabminors model lane; replace its sys.path entry with your local dependency directory for a standalone environment. It reads the frozen Carlito and AdwaitaMono fonts carried under fonts/. Their system originals were hash-bound before and after copying. No proof source depends on these layout dependencies.

```
python3 capped.py receipts/pdf-build-repeat.json python3 -B build_paper.py
python3 capped.py receipts/pdf-render-repeat.json pdftoppm -scale-to 1300 -png nut-draft.pdf qa/page
```

The source uses explicit page separators for ten readable pages. Inspect every rendered page before delivery. The saved QA receipt binds the reviewed PDF and all ten PNG files.

## Evidence boundaries

`inputs-before.json` and `inputs-after.json` bind the frozen external inputs by SHA-256; `receipts/frozen-integrity.json` reports equality. Copies in evidence preserve bytes; `COPY-RECEIPT.json` maps them to input hashes. All formal sources are carried inside the unchanged proof ZIP, not rebuilt or modified. SOURCE-MANIFEST.json is the archive's internal file manifest. MODULE-HASHES.json records all 1,279 Lean source files, including auditors and historical material beyond the scheduled 1,151 modules. The raw MathDB line is preserved byte-exactly, with its own hash receipt; the unrelated 2018 companion metadata is explicitly corrected in the paper.

Development checker/audit/control receipts and six-fix receipts are copied, together with independent verification scripts and results. Large audit-body logs remain at their frozen originating lane; audit-log-index.json locates them and the replay regenerates them. No final full-replay PASS is fabricated or inferred from development status. Read results.json for the exact handback state.

The full-dossier ZIP contains the paper, proof, source-only ZIP, frozen source copies, manifests, receipts and QA pages. DOSSIER-MANIFEST.json covers ZIP payload files excluding itself and detached archive/resource receipts to avoid circular hashes. archive-hashes.json binds both delivered ZIPs. There are no background services or jobs to stop.
