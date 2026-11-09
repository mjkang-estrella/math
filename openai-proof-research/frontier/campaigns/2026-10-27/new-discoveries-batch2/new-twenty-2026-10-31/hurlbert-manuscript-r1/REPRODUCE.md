# Reproduction and provenance

All commands are run from this lane. No network or solver is required. Do not run archived historical scripts: they are inert provenance copies and some belong to earlier Lean or network workflows. This lane did not run Lean, lake, leanchecker or any SAT/ILP solver.

The active scripts use python3 -I -B. scripts/cap.py sets two-CPU affinity, CPU 120 s, wall 140 s, address-space 6 GiB, aggregate process-group RSS sampling at 6 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR and cache. It waits for its child; heavy commands run sequentially. Receipts retain exit code, sampled RSS and elapsed wall time. The RSS sampler can miss short peaks; the address-space cap is an additional bound. No packages were installed.

Recompute all mathematical numerical claims, tables, comparison graph, CDG windows and reported search frequencies:

    python3 -I -B scripts/cap.py recompute python3 -I -B scripts/recompute.py

The standard-library script does not import any historical search module. It reproduces the recorded generators' random choices. The random generator is Python's standard random.Random; version/environment appears in receipts/environment.json. Counts are checked against the frozen inputs. Statistical observations are not uniform tour frequencies. The search is unnecessary to the proof.

Render the manuscript from manuscript.md, recomputed.json and scripts/render.py. This host's already-installed PDF runtime is:

    /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3

Use that interpreter (or another python3 with ReportLab) under the wrapper:

    python3 -I -B scripts/cap.py render /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -I -B scripts/render.py
    python3 -I -B scripts/cap.py pdf-render pdftoppm -r 110 -png manuscript.pdf qa/page

Fonts are the local Liberation Serif regular/bold and Noto Sans Math faces specified in the renderer. The manuscript Markdown uses table placeholders; the renderer fills them directly from freshly computed values. The resulting PDF has six pages; every page is visually inspected in qa/. PDF metadata timestamps may differ on regeneration, without changing mathematical content. The initial missing-library error and pagination correction are recorded in receipts/authoring-history.json; the final renderer uses the available runtime.

scripts/prepare.py freezes every file in the specified input trees except compiled .olean and .ok outputs, copies those read-only inputs locally and safely extracts the exact whitelist of six source-archive members. It runs no archived code. Safe extraction rejects duplicates, unexpected names, traversal, symlinks and excessive total uncompressed size. On a fresh reproduction use a new lane-local output tree; preserve before/after manifests from this run. scripts/finalize.py validates byte identity, raw-line identity, frozen inputs, numeric assertions and metadata, then creates the full archive. It excludes its own archive/outer checksum, so the archive is nonrecursive.

The exact MathDB raw line (including newline) is 356266.jsonl; receipts/raw-line.json binds its SHA256. Sources and original HTTP receipts are under inputs/, with all copy hashes bound by receipts/inputs-before.json and receipts/inputs-after.json. These are earlier retrieval receipts, not new network access. Full parent replay logs and registry receipts are copied there. The formal archive is byte-identical at the lane root and under inputs/hurlbert-formal-r1/; safe-extracted/ contains only source and module order. Consult the original formal REPRODUCE.md only for understanding the previous replay, not for an action performed here.

Deliverable manifest: manifest.sha256 covers the dossier payload, excluding itself, the full ZIP and the outer ZIP checksum. archive.sha256 binds the ZIP. ZIP integrity, names and per-member SHA256 are verified after writing. Root alone decides acceptance.
