# Reproduce this DRAFT dossier

Zero accepted credit. Root reads the paper and decides. No Lean, lake or leanchecker was run in this manuscript lane.

Work on a review copy of this directory if delivery hashes must be preserved. All commands below write inside the current lane. Python 3, pycairo, PyGObject with Pango/PangoCairo, system Liberation Serif/Sans fonts, and Poppler are required. ReportLab was unavailable; the renderer uses Cairo and Pango without network installation. Renderer/runtime versions and font provenance are in receipts/renderer-environment.json.

Run sequentially, one process at a time:

    MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140 python3 -B scripts/run.py python3 -B scripts/check_math.py
    MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140 python3 -B scripts/run.py python3 -B scripts/render.py
    MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140 python3 -B scripts/run.py pdftoppm -r 100 -png paper.pdf qa/page

The driver caps its child's process group at 6 GiB sampled RSS, 120 seconds CPU per process and 140 seconds wall, CPU affinity 0,1, and MALLOC_ARENA_MAX=2. It also applies a 6 GiB address-space bound. RSS sampling cannot exclude transients between samples. The CPU limit is inherited by child processes; this lane's heavy programs run serially, not as parallel workers. Temporary/cache destinations are lane-local. Short initial reads and file-authoring shell calls were not all wrapped; no perfect all-call resource-enforcement claim is made. Failed dependency, extraction-count and layout experiments are retained in receipts, not counted as validation.

The math diagnostic enumerates every degree-respecting set partition through 3x4 among the displayed cases and directly checks Definition 5.1. Degree pruning is complete by summing neighbour counts over all cells. It compares with orbit partitions of the explicit reflection group. It does not independently compute full Aut. At 4x4 it enumerates subgroups/orbits only; the equitable count there uses the ordinary theorem. None of these tests substitutes for the universal proof.

The delivered paper.md has explicit page delimiters. scripts/render.py enforces page-body bounds and writes a ten-page PDF. Re-rendering may change metadata and PDF bytes; the mathematical source and layout should agree. Every regenerated page must be visually inspected. The delivered qa/receipt.json binds the actual inspected PDF and all ten PNGs. Cached source PDFs under inputs are archival evidence, not newly authored deliverables; this lane's page QA concerns paper.pdf.

The formal packet grid-formal-r6-source.zip is reused BYTE-IDENTICALLY, SHA-256:

a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953

scripts/collect.py documents source copying and safe extraction; it rejects absolute paths, traversal, symlinks, duplicate paths and excessive expanded size, and checks 47 src modules. Four additional .lean controls are separately present. No compiled Lean artifact is in the ZIP. source-extraction/ is a convenience copy and is omitted from the full dossier as redundant. The safe-extraction receipt attests packaging only.

For formal replay instructions ONLY, read inputs/grid-formal-r6/REPRODUCE.md and the archived scripts/replay.sh, scripts/lean.sh, scripts/run.sh and scripts/report6.py. These depend on absolute local tool/package paths; the archive does not vendor mathlib. Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned. The driver strictly compiles and explicitly leanchecks each of the 47 modules, recompiles pinned Bound.Attribute locally, runs auditors, and requires all four controls to fail. This task expressly forbids running it here. Only propext, Classical.choice and Quot.sound are allowed transitive proof axioms. Distinguish reported implementation validation, independent fidelity review, root replay and acceptance.

hashes/inputs-before.json and inputs-after.json bind all designated input paths; receipts/input-integrity.json states any differences and the before-first-read qualification. SOURCE-COPIES.json binds each original to its local copy. The exact MathDB raw line is mathdb-343536.raw.jsonl, including its original newline, with provenance in receipts/raw-record.json. Cached source downloads and retrieval receipts remain byte-identical; no new online access or literature clearance is claimed.

DOSSIER-MANIFEST.json lists every included file except itself. grid-full-dossier.zip embeds that manifest. The packager validates names, ZIP CRC and every member hash. Delivery hashes and package validation, emitted after packaging, sit outside the ZIP to avoid self-reference, as does the packager's own completion resource receipt. DELIVERY-SHA256.json binds both ZIPs. Any regenerated PDF requires fresh QA and packaging.

Late root receipt: inputs/grid-parent-final-r1/replay-result.json reports PASS but explicitly records 46/47 modules PASS. Its first attempt failed before compilation due to executable bits; the second attempt chmodded three scripts without changing contents. This lane preserves the exact record and does not infer a complete 47-module replay. Root must reconcile the build field.
