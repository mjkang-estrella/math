# Reproduction and scope

This is an AI-assisted DRAFT, pending root review, with zero self-accepted credit.
Run all commands from this directory. Keep every output and temporary directory
inside this directory; cap.py sets lane-local temporary/cache paths, two-CPU
affinity, MALLOC_ARENA_MAX=2, a 120-second CPU limit, a 140-second wall watchdog,
and a sampled process-group RSS limit of 6 GiB. It waits for its child.

## Numerical reproduction (no third-party Python packages needed)

```
python3 -I cap.py python3 -I verify.py
python3 -I cap.py python3 -I recompute.py > computations.json
python3 -I cap.py python3 -I numbers.py
```

recompute.py is a byte copy of the independent review implementation, freshly
executed here; it imports no discovery program. It outputs all scan counts,
sorted traces, block checks, the robust minimax policy tree, and every leaf.
numbers.py is a new coordinate implementation with additional assertions: it
checks the unsorted literal plays, mass bounds, rational payoffs, combinatorial
scan sizes and all family boundaries in the printed range. It independently
reimplements the full best-response scans and the adversarial minimax, including
traversal of every opponent branch under its own maximizing policy. Both scripts use
python3 -I. Each normally completes in seconds. Neither invokes a solver.
computations.json and numeric-audit.json are the fresh calculation receipts.
The numeric audit covers game data and tested ranges. Bibliographic years,
identifiers, source line references and tool versions are transcribed metadata.

## Manuscript source and rendering

manuscript.md is the editable paper source. render.py converts it to the PDF,
using ReportLab and installed Liberation Serif and Noto Sans Math fonts. The
renderer uses invariant PDF metadata. In this environment use:

```
python3 -I cap.py /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -I render.py
python3 -I cap.py pdftoppm -r 110 -png manuscript.pdf qa-page
```

Elsewhere use a Python with ReportLab installed and adjust the font paths to
local equivalents. Font substitutions may change pagination. Every final page
was rendered and visually inspected; qa-receipt.json binds the final PDF and
page images. The renderer substitutes actual subscript/superscript typesetting
for Unicode characters absent from the fonts. The final font audit reports no
missing glyphs. No browser, server, network call or upload is needed.

## Lean packet and inherited replay

source.zip is reused byte-identically, SHA-256
e1f35146078b39a2ace25101b02806404f741adb7042e1376f77d7c09e359996.
safe-extraction.json records path traversal, symlink and aggregate-size checks
and hashes every extracted regular member. safe-extracted-packet is an inert
extraction: no contained script or Lean file was run in this lane.

The endpoint is SlowNim360653.conjecture1_false. It proves the literal
conjecture false using (4,4,5), not the general family or robust minimax result.
The packet's original REPRODUCE.md preserves the pinned Lean 4.34.1 and mathlib
revision d13f23b723b8a846827a245b89c10fc7d3f11612 and upstream build
instructions. Do not execute those instructions under this lane's prohibition
on Lean, lake and leanchecker. The existing root replay reports PASS and its
registry refresh reports CLEAN for bounded path screens; both are copied under
evidence/slownim-parent-final-r1. These are inherited evidence, not a new
manuscript-lane kernel replay. See the manuscript's trust limits.

## Evidence, integrity and archives

evidence/ preserves source copies, exact raw MathDB lines, HTTP bodies and
receipts, review and root decisions, formal materials and replay records.
inputs.before.json and inputs.after.json hash the frozen external inputs.
input-verification.json records equality and copy integrity. MANIFEST.sha256
binds delivered files except itself, the full-dossier ZIP and ZIP receipt, and
the live resource log. logs/resources-frozen.jsonl snapshots the capped calls
before packaging. The live log continues to record packaging and verification.
manuscript-source.zip bundles the manuscript source, renderer and these
instructions. full-dossier.zip contains all deliverable files and its internal
manifest. archive-receipt.json binds both output ZIPs and records a CRC and
manifest check of the full dossier. verify.py checks all current manifest
members, original frozen inputs when available, and the byte-identical packet.

The source-copy discovery note contains superseded minimality and formal-cost
claims. It is retained as historical evidence, not endorsed: the manuscript and
independent review explicitly correct those claims. The DAM version of record
is unread. No priority claim is made. Root alone decides acceptance.
