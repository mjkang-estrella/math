# DRAFT replay: MathDB 378395

Extract source-only-proof.zip with `python3 -I safe_extract.py source-only-proof.zip /absolute/new/destination`. The extractor rejects traversal, absolute paths, duplicate names, symlinks and special files; it never overwrites. The replay refuses any existing .olean, controls/ or replay-receipts/. Run from the new extraction:

```sh
LEAN_BIN=/path/to/lean-4.34.1/bin LEAN_PACKAGES=/path/to/.lake/packages python3 -I replay.py
```

Example paths and exact revisions/binary hashes are in pins.json. Here LEAN_BIN is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin and LEAN_PACKAGES is /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages. No lake update or cache write is performed. Cached dependency oleans are trusted, not rebuilt or source-attested. The driver checks cache source revision metadata and supplied executable hashes.

The build uses -j1 -DwarningAsError=true; leanchecker separately checks the new module. ReviewAudit enumerates all 134 declarations, full types, origins, bodies and transitive axioms (only propext, Classical.choice, Quot.sound). ReviewSanity checks literal definitions, non-vacuity and endpoints. The two Review files are reviewer supplements; MathDB378395.lean is the byte-identical mathematical source.

Each subprocess uses at most two CPUs, CPU 120 seconds, wall 140 seconds, AS 64 GiB, MALLOC_ARENA_MAX=2, sampled 6 GiB private RSS guard. Total VmRSS is reported separately because clean dependency pages are mmapped. A systemd user scope sets MemoryMax=6G, MemorySwapMax=0 and CPUQuota=200% when available. The driver reports whether the scope was used. It writes only within its own fresh extraction, deletes nothing, and waits for each child. Inputs outside the extraction are read-only.

Controls: the unchanged prefix must compile; one perturbed coefficient must fail the validity theorem at its exact line; wrong endpoint polarity must type-error; sorry must fail warning-as-error; a declared cheat axiom must fail the explicit audit; a malformed olean must fail leanchecker. These checks test only their named rejection mechanisms, not completeness or universal reliability of the harness. The exact Python diagnostic is corroboration, not the Lean proof.

Build paper.pdf with Python 3 and reportlab, using `python3 build_paper.py`; install reportlab in your own environment if necessary. paper-source.json is the editable eight-page manuscript source. The recorded build used lane-local dependencies; these are excluded from the archives. Liberation Serif and Liberation Mono font paths appear in build_paper.py and can be adjusted on other systems. Run pdftoppm -r 100 -png paper.pdf qa/page to render; inspect every page. PROOF.md also gives the ordinary proof and finite determinant recurrence. tools/certificate.py regenerates receipts/minor-certificate.json; it is not required by the Lean replay.

source-manifest.json binds the source archive contents (excluding itself). dossier-manifest.json binds the full archive contents (excluding itself). archive-hashes.json binds the two final ZIPs. frozen-before.json and frozen-after.json bind all four protected input trees/files; unrelated r73 files are hash-bound for integrity but not included. Prior-art reviews and historical receipts are labelled evidence. The reviewers' HOLD and root's bounded qualified pass are both preserved; no priority is claimed. Dobra's later-open report is inherited from adjudication and not independently body-verified here.

DRAFT; zero accepted credit; campaign remains 11/20 beyond 39. Root alone accepts.
