# Reproduction

Toolchain: Lean 4.34.1 at `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`. Read-only mathlib packages at `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`, pinned by the assignment to d13f23b723b8a846827a245b89c10fc7d3f11612. Upstream compiled dependencies are trusted, not regenerated.

Extract schrijver-partial-source.zip into a new empty directory inside this lane. Run `python3 -I scripts/replay.py` there. It verifies SOURCE-MANIFEST.json, clears inherited LEAN/LAKE environment settings, builds modules strictly and serially using `lean -j1 -M3500 -DwarningAsError=true`, runs leanchecker on each, performs the complete local-declaration audit and runs two expected-failure controls. Logs and receipts stay inside the extraction. `--resume` reuses only successful module steps whose receipt matches the complete packet source manifest; use it only on the same extraction, without altering build artifacts.

The dependency order is Definitions, Checkers, Data27, Controls, Audit. Audit is command-only tooling: every original-module declaration, including generated declarations, is selected by module identity. It emits full type/body, unsafe and partial flags, implemented_by, extern and transitive axioms. Only propext, Classical.choice and Quot.sound are permitted. Audit tooling is not a mathematical assumption.

Every child process is pinned to at most two allowed CPUs, has CPU 120 seconds, wall 140 seconds and a sampled aggregate private RSS ceiling of 6 GiB, with MALLOC_ARENA_MAX=2 and lane-local temporary/cache paths. The watchdog is sampled every 0.05 seconds. It limits the process group and joins the child before returning. There is one heavy child at a time.

The two Lean negative controls must reject a false claim via `decide`: a cyclic endpoint pair incorrectly treated as stable, and a corrupted witness mask. A timeout, missing dependency or unrelated error is not a successful control. Controls.lean proves the corresponding true negations.

To regenerate numerical evidence with no execution of input scripts, run `scripts/cap.sh python3 -I scripts/generate.py` from the extraction. The copied reviewer certificates must be present in inputs. The program independently generates masks from gap-compressed combinations, constructs literal disjointness adjacency, computes all representative BFS trees, validates parent edges and labels, and cross-checks every reviewer label under rotation. It rewrites Data27 deterministically; rerun packaging and replay if its source hash changes.

A successful replay means PASS_PARTIAL_ONLY. It does not prove the two remaining graph bridge propositions or an unconditional MathDB endpoint. See SUMMARY.md and STATEMENT-CORRESPONDENCE.md.
