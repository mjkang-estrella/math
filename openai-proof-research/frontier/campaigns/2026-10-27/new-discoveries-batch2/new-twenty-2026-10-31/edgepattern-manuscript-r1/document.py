from pathlib import Path
import json,hashlib,shutil
r=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fontsrc=Path('/home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/libreoffice-headless/libreoffice/share/fonts/truetype')
(r/'paper/fonts').mkdir(exist_ok=True)
for f in ['DejaVuSerif.ttf','DejaVuSerif-Bold.ttf','DejaVuSansMono.ttf']:shutil.copyfile(fontsrc/f,r/'paper/fonts'/f)
p=r/'paper/build.py';p.write_text(p.read_text().replace("font='/home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/libreoffice-headless/libreoffice/share/fonts/truetype/'","font=str(Path(__file__).resolve().parent/'fonts')+'/'"))
shutil.copyfile(r/'evidence/expanded-corpus-r103/raw/342414.jsonl',r/'sources/342414.jsonl')
(r/'sources/342414.sha256').write_text(h(r/'sources/342414.jsonl')+'  342414.jsonl\n')
# Actual destination-to-origin copy manifest.
before=json.loads((r/'input-hashes-before.json').read_text()); copies={}
for origin,sha in before.items():
 rel=Path(origin)
 if rel.parts[0]=='edgepattern-formal-r5' and rel.parts[1] in ['formal','scripts','checks','negative-controls']:
  dest=Path(*rel.parts[1:])
 else:dest=Path('evidence')/rel
 assert h(r/dest)==sha
 copies[str(dest)]={'origin':origin,'sha256':sha}
(r/'INPUT-COPY-MANIFEST.json').write_text(json.dumps(copies,indent=2)+'\n')
shutil.copyfile(r/'evidence/edgepattern-formal-r5/statement-correspondence.md',r/'STATEMENT-CORRESPONDENCE.md')
with (r/'STATEMENT-CORRESPONDENCE.md').open('a') as f:
 f.write('\nThe manuscript source paper/manuscript.md, Section 6, adds the full definition-level correspondence table, and Section 7 gives the canonical-to-tree homomorphism / bridge reflection / numbering architecture. The shallower-tree robustness is ordinary mathematics only.\n')
(r/'MODULE-HASHES.json').write_text(json.dumps({p.name:h(p) for p in sorted((r/'formal').glob('*.lean'))},indent=2)+'\n')
(r/'REPRODUCE.md').write_text('''# Reproduce the draft dossier

This packet is a DRAFT, assigns zero accepted credit, and leaves root acceptance, registry refresh and independent paper review outstanding.

## Lean replay

Use a newly created empty directory INSIDE the assigned lane for verification. Check archive SHA-256 against archive-hashes.json. Inspect member paths and reject absolute paths, traversal and symbolic links before extracting edgepattern-source-only.zip. The source archive contains no compiled modules. Validate SOURCE-MANIFEST.json; do not transplant oleans.

```
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 -I replay.py
```

LEAN_BIN is the executable (its parent is the requested binary directory), not the directory. Both variables can be changed for another installation of the same pins: Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Precompiled external package caches are trusted, not rebuilt. The replay records the actual Lean --version output. It sanitizes inherited LEAN/LAKE search settings and refuses preexisting oleans anywhere under its root.

The wrapper runs scripts/replay.py, scripts/negative.py and scripts/check-auditor.py in order, stops at failure, and prints a final PASS line only after all three succeed. scripts/modules.json is a dependency order for 268 proof modules plus AuditR5. Every strict compilation uses -j1 -DwarningAsError=true; every leanchecker call contains exactly one module. AuditR5 performs the full generated-declaration expression inventory and axiom checks. The separate AuditToolSafety check inspects generated auditor declarations. Only propext, Classical.choice and Quot.sound are allowed. Canonical and inherited Audit/AuditR2/AuditR3/AuditR4 are preserved outside the build/proof closure. No proof source was edited.

The watchdog sets affinity to at most two CPUs, CPU limit 120 s, wall limit 140 s, MALLOC_ARENA_MAX=2, and samples private RSS every 0.05 s, killing at 5.75 GiB (below 6 GiB). Each guarded call is sequential. The full replay is hundreds of short calls, never one uncapped Lean invocation. Logs and resource receipts are in fresh-replay/logs/; the top-level receipts/replay-driver.log includes the final PASS line. An interrupted source extraction cannot be reused for a clean replay because it contains oleans.

Expected failures include the positive conjecture, wrong root, missing acyclicity, the false numeric lower bound on the concrete pattern (whose equality is proved in Concrete), and a false strict upper bound on the minimum tree value. Each must return an ordinary Lean error (exit 1), not timeout or resource kill. Existing-olean refusal is checked separately. Five false Lean controls plus this refusal must pass. AuditToolSafety must compile.

## Ordinary proof and paper

PROOF.md gives the complete ordinary proof, classification, closed evaluation rule and all 81 exact entries. paper/manuscript.md is the editable manuscript text; paper/build.py is the complete PDF typesetting source, with bundled fonts. To regenerate using Python with reportlab installed:

```
python3 paper/build.py
pdftoppm -r 110 -png paper/edgepattern-draft.pdf qa/page
```

Read all six rendered pages. qa/ and receipts/pdf-qa.json bind the delivered rendering. The proof uses no solver: receipts/closed-form-values.json has exact rational values; receipts/ordinary-math.json records equality with the input independent all-subset enumeration. The table scales values by 810000 to display integer entries. The 81 forms include one depth-1 tree; the other 80 have exact depth 2. The extension to depth-at-most is ordinary mathematics, not a Lean theorem.

## Provenance and archives

sources/342414.jsonl is the exact raw MathDB line, with its dedicated SHA-256 file. evidence/ preserves source v1/v6, thesis and citing-body copies, access receipts, previous review and root adjudication. INPUT-COPY-MANIFEST.json maps every copied frozen input to its origin/hash. input-hashes-before.json and input-hashes-after.json bind the inputs without modifying them. The two r5 archives and EDGE-PROOF.md must match TASK.txt's required hashes.

SOURCE-MANIFEST.json covers the source archive payload (excluding itself to avoid recursion). DOSSIER-MANIFEST.json covers the full dossier payload (excluding itself and the full ZIP). archive-hashes.json binds the ZIPs externally. The full dossier excludes redundant fresh-replay source copies and compiled binaries but retains every fresh replay log and resource receipt. A successful local replay is not campaign acceptance and makes no priority claim. Final SIAM body, the inaccessible heuristic body, an edge/vertex-colouring thesis body and MathDB comments remain unread.
''')
print('supporting documents written')
