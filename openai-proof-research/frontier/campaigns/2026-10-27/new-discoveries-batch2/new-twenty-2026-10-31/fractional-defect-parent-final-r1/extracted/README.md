# MathDB 335230 draft dossier

Draft only. Exact certified claim: D(K_2^(4),3) <= 5/3 < 2; universal source equality false. The exhibited maximum is exactly 5/3, with no claim of optimality. Literature HOLD remains material; candidate credit 0; campaign accepted 1/20 unchanged.

- paper.pdf and paper.tex: five-page ordinary manuscript, definitions, complete witness proof, known-result comparisons, formal mapping and limits.
- original/proof-packet.zip: original frozen seven-file packet, byte preserved. This is the only nested archive, explicitly requested, not recursive historical packaging.
- proof/: exact Lean, replay.py, pins, original proof/receipts/literal record.
- reviews/: selected original independent reports and complete local-declaration auditor, unchanged.
- sources/: the three primary version PDFs/texts; dated HTTP history and selected companion, slides and CV evidence.
- provenance/: corpus line plus records/provenance and dated small registry receipts. Other historical input paths in input-bindings.json are integrity/provenance pointers, not represented as bundled bodies.
- replay/: this task's fresh strict replay, all-32-declaration axiom audit, metadata revision check, lexical scan and exact rational arithmetic.
- integrity-before.json / integrity-after.json: all 33 frozen input hashes matched. These are scoped checks, not a workspace-wide unchanged assertion.

## Verify and replay

In a fresh extraction, run `python3 verify-manifest.py`, then `python3 replay-dossier.py`. The latter generates work/strict-extracted and refuses to reuse it. Linux Python3 is required. Defaults:

```
LEAN_BINARY=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
MATHLIB_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

Override those environment variables as appropriate. Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are required, with the other eight packages in proof/lake-manifest.json already available as prebuilt caches. Script uses strict warnings, -j1 -M2048, two-CPU affinity, 8 GiB address cap, 90 CPU seconds soft/95 hard, 105-second wall timeout per run. AuditAll.lean contains the identical candidate followed by the auditor; no candidate edits are made. A separate arithmetic replay is `python3 replay/independent-arithmetic.py`.

Prebuilt imported oleans and exported axiom summaries are trusted external inputs. Revision metadata is checked, but source cleanliness/source-to-olean provenance and a full dependency rebuild are not established. The dossier is not fully vendored and makes no full offline rebuild claim. Original replay.py alone does not authenticate the dependency cache.

Build paper.tex using a standard LaTeX installation with amsmath, amssymb, amsthm, geometry, booktabs, array, hyperref (e.g. Tectonic). PDF bytes may vary with timestamps/tool versions. Final PDF was rendered and every page inspected; render/cache/compiled intermediates are excluded. The manifest excludes itself to avoid self-reference. The outer zip has a separate hash receipt, also outside the zip.

No author contact, external messages, publication, upload, browser tabs, git operation, ledger changes, or candidate changes were performed. Paper review, root final replay, literature adjudication and acceptance are separate gates.
