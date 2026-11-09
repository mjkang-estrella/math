# Round 7 replay

This is a partial implementation packet. Replaying it does not prove the three remaining Props or constitute acceptance.

From a fresh extraction, run `bash scripts/validate.sh`. It uses modules.txt in strict serial dependency order, compiles with Lean 4.34.1 using -j1 -M3500 -DwarningAsError=true, and invokes leanchecker separately with each explicit module argument. Pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and its read-only package dependencies are located by scripts/env.sh. No lake or network download is needed.

All Lean, leanchecker and Python calls must go through scripts/capped.sh: CPUs 0,1; CPU 120 seconds; wall 140 seconds; sampled total-session RSS 6 GiB; MALLOC_ARENA_MAX=2. It exports lane-local TMPDIR and XDG_CACHE_HOME, retains uniquely named full logs, and reaps both child and watchdog. Run one driver at a time. Build outputs and success markers are local to the extraction. The driver resumes modules whose hash marker matches; after edits, delete downstream markers as well. No copied bootstrap object is required for the fresh replay.

Then run `bash scripts/controls.sh` for the five inherited expected failures and `scripts/capped.sh python3 -I scripts/regression7.py` for independent numerical end-edge checks. The latter is evidence, not a Lean proof. Full declaration audit Chord7Audit writes audit7.jsonl and checks that every declaration in the endpoint import closure, including generated declarations and opaque values, was audited. LOCAL metadata and transitive axioms are checked strictly. Upstream runtime metadata is reported separately, not confused with theorem assumptions.

`sha256sum -c inherited-before.sha256` verifies all 148 frozen sources. inherited-after.sha256 records the after-check hashes. All new Lean modules start Chord7. Failed development logs are retained, including elaboration failures; only successful strict replay markers are used for validation claims.

The source-only archive is chord7-source.zip. scripts/package7.py packages safe relative paths without object files; scripts/extract7.py rejects absolute paths, parent traversal and symlinks before creating fresh-extraction. scripts/finalize7.py records module hashes, line counts, actual replay markers, exact audit totals and remaining obligations. Logs are outside the source archive and retained in logs/ and fresh-extraction/logs/.

For the entire workflow, `bash scripts/replay7.sh` runs the root build, controls and numerical regression, packages and safely extracts sources, resumes the fresh build, runs its controls, generates results.json and regenerates the final source archive. It refuses stale extracted Lean sources. On a deliberate source change, use a new extraction directory or remove only the lane-local previous extraction before restarting. The final archive includes results generated after replay; its Lean sources are identical to the checked extraction.
