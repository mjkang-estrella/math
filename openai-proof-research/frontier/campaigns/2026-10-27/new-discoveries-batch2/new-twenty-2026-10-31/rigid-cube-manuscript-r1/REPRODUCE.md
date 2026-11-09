# Reproduce the draft certificate

DRAFT. Zero accepted credit; root alone accepts. No network access is needed for replay. Use Linux with Python 3, systemd-run (user scope if available), the pinned Lean 4.34.1 distribution, and the pinned mathlib dependency cache specified in pins.json. The driver never invokes lake or writes the dependency cache. Its environment overrides are:

```
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/path/to/pinned/.lake/packages
python3 scripts/replay.py
python3 scripts/check_witness.py
```

First safely extract source-only.zip into an empty directory: reject absolute names, traversal components, symlinks and duplicate names. Verify source-manifest.json using SHA-256. Run the commands from that extraction. Existing oleans anywhere in it cause refusal. Run only one driver in an extraction. Receipt and log files go under receipts/. Exit zero and receipts/replay.json status PASS mean all strict builds, separate kernel checks, declaration checks, sanity examples, and the two intended compilation failures passed. The original author modules are byte-identical, not rewritten by the reviewer. ReviewerAudit, ReviewerSanity, NegativeCard and NegativeDistance are labelled reviewer supplements.

Each subprocess has at most two CPU affinities, a 120-second CPU limit, a 140-second wall guard, a 64 GiB address-space limit, MALLOC_ARENA_MAX=2, and a sampled 6 GiB process-tree private-RSS guard. Total VmRSS and private RSS peaks are recorded. Where the user systemd scope probe succeeds the command also has MemoryMax=6G. Sampling cannot detect every transient; cgroup enforcement is supplementary. lean uses -j1 -DwarningAsError=true; leanchecker separately checks each positive module. Negative controls require an actual Lean error and nonzero exit, not an arbitrary timeout. They test rejection of the specified false cardinality and one false signed distance, not the completeness of Lean or all possible attacks.

The driver removes only the olean-related files it names and creates in this fresh extraction, even on failure. No shared-cache mutation is intended or needed. A dependency-cache upgrade is not a valid pinned replay. collectAxioms uses the compiler's exported dependency metadata for imported declarations; the pinned upstream binaries/oleans are trusted, not independently rebuilt or attested here. No Python result is an axiom of the Lean proof.

To regenerate the PDF, install reportlab and run python3 scripts/build_paper.py, then pdftoppm -scale-to 1300 -png draft.pdf qa/page. The paper source is paper.json plus this explicitly retained renderer. Every delivered page was rendered and visually inspected. The first marker invocation used an unavailable relative path. The helper was later resolved inside the installed PDF skill and invoked successfully before the final regeneration. The first build preceded that successful marker; this procedural deviation is retained in the artifact logs.

Manifests: source-manifest.json covers replay sources and instructions inside source-only.zip; dossier-manifest.json covers delivered dossier files except itself and the outer ZIP/hash receipt. Archive hashes are in archive-hashes.json. Frozen-before.json binds every file of all four read-only input trees/objects; frozen-after.json records the final equality check. Gate 1 is independently reported in TECHNICAL-REVIEW.md and technical-review.json. Fresh author extraction and fresh source-only archive replay receipts are kept separately.
