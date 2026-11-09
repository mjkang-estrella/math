# Source-only proof packet (draft, no acceptance)
Game.lean is the unchanged candidate by the expanded-corpus-r48 research lane.
Bridge.lean is the unchanged separately attributed independent fidelity-review supplement;
Review.number_le_iff and its edge controls are not part of the original 63 declarations.
Audit.lean enumerates ALL declarations defined by both modules, including generated ones,
and emits full explicit types, values/proof terms, #print axioms and transitive axiom sets.
Only propext, Classical.choice and Quot.sound may occur. It rejects unsafe flags/new axioms.

Extract into a NEW directory; run `python3 replay.py` there. It refuses to reuse `fresh/`.
Pinned Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52;
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 in external read-only package cache.
Paths default to the author's local pinned installation; LEAN_BIN and LEAN_PACKAGES
can select byte-matched copies. See pin-evidence.json for binary/manifests/cache hashes.
Strict warnings, -j1, MALLOC_ARENA_MAX=2, sanitized environment, at most two CPUs,
6 GiB sampled RSS, 12 GiB AS, 120 CPU seconds and 140 wall seconds PER invocation.
The monitor samples every 25ms; not an aggregate cgroup memory guarantee.
leanchecker uses the same Lean kernel, not an independently implemented checker.
External cached upstream oleans are trusted: no source-to-olean correspondence proof,
standalone dependency distribution, or full upstream rebuild is claimed.

`python3 ordinary-proof.py` checks the exact upper tree and all 105 lower completions,
writing ordinary-certificate.json. No graph search or network access is required.
Negative controls reject a false three-move win, absent module and corrupt module.
