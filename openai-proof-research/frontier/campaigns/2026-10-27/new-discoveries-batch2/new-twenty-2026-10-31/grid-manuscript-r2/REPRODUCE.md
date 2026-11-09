# Reproduce this DRAFT dossier

Zero accepted credit. Root reads the paper and decides. No Lean, lake or leanchecker was run in this manuscript lane.

Work on a review copy of this directory if delivery hashes must be preserved. All commands below write inside the current lane. Python 3, pycairo, PyGObject with Pango/PangoCairo, system Liberation Serif/Sans fonts, and Poppler are required. ReportLab was unavailable; the renderer uses Cairo and Pango without network installation. Renderer/runtime versions and font provenance are in receipts/renderer-environment.json.

Run sequentially, one process at a time:

    MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140 python3 -B scripts/run.py python3 -B scripts/check_math.py
    MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140 python3 -B scripts/run.py python3 -B scripts/render.py
    MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140 python3 -B scripts/run.py pdftoppm -r 100 -png paper.pdf qa/page

The driver caps its child's process group at 6 GiB sampled RSS, 120 seconds CPU per process and 140 seconds wall, CPU affinity 0,1, and MALLOC_ARENA_MAX=2. It also applies a 6 GiB address-space bound. RSS sampling cannot exclude transients between samples. The CPU limit is inherited by child processes; this lane's heavy programs run serially, not as parallel workers. Temporary/cache destinations are lane-local. Short initial reads and file-authoring shell calls were not all wrapped; no perfect all-call resource-enforcement claim is made. Round-1 receipts and failed experiments are preserved as historical records under inputs/grid-manuscript-r1-receipts. Current receipts are under receipts/.

The math diagnostic enumerates every degree-respecting set partition through 3x4 among the displayed cases and directly checks Definition 5.1. Degree pruning is complete by summing neighbour counts over all cells. It compares with orbit partitions of the explicit reflection group. It does not independently compute full Aut. At 4x4 it enumerates subgroups/orbits only; the equitable count there uses the ordinary theorem. None of these tests substitutes for the universal proof.

The delivered paper.md has explicit page delimiters. scripts/render.py enforces page-body bounds and writes an eleven-page PDF. Re-rendering may change metadata and PDF bytes; the mathematical source and layout should agree. Every regenerated page must be visually inspected. The delivered qa/receipt.json binds the actual inspected PDF and all eleven PNGs. Cached source PDFs under inputs are archival evidence, not newly authored deliverables; this lane's page QA concerns paper.pdf.

The formal packet grid-formal-r6-source.zip is reused BYTE-IDENTICALLY, SHA-256:

a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953

scripts/extract.py performs the source-only safe-extraction test; it rejects absolute paths, traversal, symlinks, duplicate paths and excessive expanded size, and checks 47 src modules. Four additional .lean controls are separately present. No compiled Lean artifact is in the ZIP. source-extraction/ is a convenience copy and is omitted from the full dossier as redundant. The safe-extraction receipt attests packaging only.

For formal replay instructions ONLY, read inputs/grid-formal-r6/REPRODUCE.md and the archived scripts/replay.sh, scripts/lean.sh, scripts/run.sh and scripts/report6.py. These depend on absolute local tool/package paths; the archive does not vendor mathlib. Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned. The driver strictly compiles and explicitly leanchecks each of the 47 modules, recompiles pinned Bound.Attribute locally, runs auditors, and requires all four controls to fail. This task expressly forbids running it here. Only propext, Classical.choice and Quot.sound are allowed transitive proof axioms. Distinguish reported implementation validation, independent fidelity review, root replay and acceptance.

hashes/inputs-before.json and inputs-after.json bind all designated input paths; receipts/input-integrity.json states any differences and the before-first-read qualification. SOURCE-COPIES.json binds each original to its local copy. The exact MathDB raw line is mathdb-343536.raw.jsonl, including its original newline, with provenance in inputs/grid-manuscript-r1-receipts/raw-record.json and hashes in receipts/raw-record.json. Cached source downloads and retrieval receipts remain byte-identical; no new online access or literature clearance is claimed.

DOSSIER-MANIFEST.json lists every included file except itself. grid-full-dossier.zip embeds that manifest. The packager validates names, ZIP CRC and every member hash. Delivery hashes and package validation, emitted after packaging, sit outside the ZIP to avoid self-reference, as does the packager's own completion resource receipt. DELIVERY-SHA256.json binds both ZIPs. Any regenerated PDF requires fresh QA and packaging.

Revision-2 workflow: run scripts/extract.py, scripts/check_math.py, scripts/render.py, then pdftoppm through scripts/run.py sequentially. Inspect every PNG before creating qa/receipt.json. Finally run scripts/package.py through scripts/run.py. The final packager verifies the before/after bindings, source-copy hashes, archive identity, PDF QA binding, ZIP CRC and every member hash. It never runs Lean.

Corrected root receipt: inputs/grid-parent-final-r1/replay-result.json reports PASS, 47/47 strict builds and explicit-module leanchecker passes, 4/4 controls rejected, Audit6 299,549 inventoried = audited and LOCAL 742, with only the three standard axioms. Its correction note explains that the old counter missed the first PASS line. The failed initial extraction attempt preceded compilation; executable permission repair changed no script bytes. registry-refresh.json reports CLEAN at Omega bc417b2d within complete-tree path screening only.

The final fidelity records are now present (A-C PASS, D-E QUALIFIED_PASS). Its replay-driver interruption and detached-child cleanup are disclosed in REVIEW.md; the interrupted Audit6 invocation is excluded and a capped serial resumption completed. Strict flags do not mean warning-free auditor imports. Neither those records nor the successful root replay accept the manuscript. Campaign 29/40 beyond 39; zero new accepted credit.
