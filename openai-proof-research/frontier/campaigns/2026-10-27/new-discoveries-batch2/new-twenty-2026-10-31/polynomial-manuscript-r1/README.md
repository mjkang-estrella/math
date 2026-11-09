# MathDB 347913 manuscript dossier

Internal draft; focused novelty review ACTIVE/PENDING and root acceptance PENDING. No authority to accept; zero accepted/helper credit. Campaign context 3/20 beyond 39. No unfinished focused-review output has been read or packaged.

- `paper.pdf`: self-contained mathematical manuscript.
- `paper-source.json`, `build-paper.py`: complete authored source and PDF renderer.
- `proof-source-only.zip`: unchanged author archive, SHA256 `859afaf1d4cc7799f6e6559052766bdf0c81ca192d322b93b860ac1704aa5681`.
- `replay/extracted/src/PolynomialConvexity/`: all 18 byte-identical Lean files, including Source, Endpoint and Audit.
- `replay/build/build.json`: 18 fresh strict builds and 18 fresh leanchecker successes; individual full stdout/stderr adjacent.
- `ReviewAudit.stdout`, `declaration-audit.json`: fresh complete types (pp.proofs/pp.explicit true), flags and transitive allowed-axiom audit of all 205 origin declarations, including generated declarations and instances.
- `controls.json`: invalid False theorem and corrupt local olean both rejected (exit 1); expanded audit and version control exit 0.
- `dependency-provenance.json`: freshly read package HEAD/ref metadata and SHA256 of every cached package .olean, plus pinned lean/leanchecker binary hashes. These receipts document consumed caches, not a source-to-object attestation.
- `reviews/`: completed independent reports and provenance only, no recursive historical tree.
- `source-reference-index.json`: exact URLs, versions, hashes, read depths and bibliographic qualifications.
- `bindings-before.json`, `bindings-after.json`: all 178 frozen bindings unchanged.

## Replay

From this directory, `python3 replay.py --output "$PWD/replay-again"` performs another safe extraction into a fresh direct child, with fresh own output only. The output must not exist. All 18 module files are required; no missing-module skip. Drivers inspected before execution. `controls.py` is run in the new child and imports only its own fresh objects plus package caches. The original extracted author drivers are preserved but are not used to write into the author lane.

Pinned Lean 4.34.1: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`.
Pinned mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, packages at `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`.

Environment is rebuilt, with fresh output plus package caches in LEAN_PATH; -j1, asynchronous elaboration disabled, warning-as-error, MALLOC_ARENA_MAX=2, 8 MiB Lean thread stack. Ordinary processes: 8 GiB AS. Audit/checker: 12 GiB AS under the inherited allocation-failure justification in extracted resource-plan.json. Each process: 180 CPU seconds, 240 wall seconds, affinity <= 2 CPUs. Package caches are read without rebuilding or writing; this is not an OS-enforced read-only mount. Only propext, Classical.choice and Quot.sound are allowed; unsafe/partial/axiom declarations are rejected. leanchecker uses the same Lean kernel and trusted imports, not an independent verifier. No upstream own-project outputs enter LEAN_PATH.

## Rebuild the paper

Use Python 3.12 with reportlab 4.4.9, matplotlib 3.11.2 and Pillow 13.0.0 (actual renderer environment versions in pdf-environment.json). Install these into a local environment if needed. Here the runtime Python supplies ReportLab and lane-local pdf-deps supplies matplotlib; `PYTHONPATH=./pdf-deps MPLCONFIGDIR=./tmp/mpl /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 build-paper.py`. Explicit DejaVu font files come from matplotlib. `pdftoppm -scale-to 1200 -png paper.pdf rendered/page` reproduces the visual inspection images. They are retained locally; bulky Python dependencies, local compiled objects and rendered images are excluded from the efficient dossier ZIP.

The completed ordinary review's significance judgment is conditional. The classical Marshall-Olkin construction is acknowledged as antecedent methodology. The 1967 mgf full body and 2025 quantum-channel citing body were unread in that completed review. No worldwide-priority claim or clearance of those bodies is made. Root will integrate the separately active focused novelty verdict later. The draft mathematical theorem covers all n,L,d >= 2, including L>n by the empty-simplex convention; there is no degree ceiling. Signed-weight moment identity and nonnegative convexity are separate statements.
