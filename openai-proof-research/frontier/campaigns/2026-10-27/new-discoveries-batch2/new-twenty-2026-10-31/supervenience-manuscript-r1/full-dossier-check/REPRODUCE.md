# Reproduce this DRAFT
Unaccepted, zero credit; campaign 12/20 beyond 39 unchanged. Root alone accepts.

Prerequisites: Linux, Python 3, Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52, leanchecker from that distribution, cached mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and its dependencies. LEAN_PACKAGES points to the formal project's .lake/packages, whose ../../lake-manifest.json records the pin. Upstream oleans and toolchain are trusted, not rebuilt. No network or cache writes are needed for replay.

Run python3 tools/extract.py source-only-proof.zip fresh-replay; enter fresh-replay; export LEAN_BIN=/path/to/lean/bin and LEAN_PACKAGES=/path/to/formal/.lake/packages; then run python3 tools/replay.py.

Local paths used:
LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages

The driver refuses existing local oleans; verifies all source-manifest hashes, literal module hash, Lean commit and mathlib revision; builds with -j1 -DwarningAsError=true; runs leanchecker for all three modules; audits all 101 original-module declarations by module origin, including bodies, full types, safety and transitive axioms. Only propext, Classical.choice and Quot.sound are allowed. It deletes only its newly allocated replay-owned-* directory, even on failure. Logs survive in replay-receipts.

Negative controls: a false proof must fail type checking; sorry must fail strict compilation; an injected local axiom compiles but must fail the full declaration audit. These test these specific failure modes, not every conceivable checker defect.

Every subprocess uses two CPUs, CPU 120 s, wall 140 s, AS 64 GiB, sampled private RSS 6 GiB, MALLOC_ARENA_MAX=2, and systemd MemoryMax=6G where available. Receipts report actual scope use. Sampling does not guarantee absence of transient peaks.

Optional finite diagnostics: python3 tools/capped.py receipts models . -- python3 tools/models.py
Output: logs/model-check.json. Expected 263185 one-step and 98304 nested pointed cases. Missing-cell and unguarded-cell controls test only the specified finite candidates; these computations do not prove the theorem.

Paper: paper.md is the readable source; build_paper.py uses ReportLab and system Liberation and Noto fonts. Run python3 build_paper.py with reportlab installed in a private environment. PDF: output/pdf/supervenience-draft.pdf. Render using pdftoppm -r 100 -png output/pdf/supervenience-draft.pdf qa/page. Presentation dependencies are separate from Lean dependencies.

source-manifest.json binds source archive contents except itself. dossier-manifest.json binds full archive contents except itself. archive-hashes.json externally binds both ZIPs. The source ZIP contains no oleans. The full dossier includes target-relevant original source copies, historical reviewer supplements, paper, fresh replay receipts and the source ZIP. frozen-before.json and frozen-after.json hash-bind all frozen input files. Historical reports are evidence, not new acceptance.
