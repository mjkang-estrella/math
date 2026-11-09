The bunkbed conjecture for transitive tournaments - MathDB 382297 - source-only certificate

This archive contains the 33 Lean modules whose final theorem is Bun.bunkbed_E7_transitive, in src/, plus audit and control modules in audit/. PINS.json gives Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and executable hashes. Upstream libraries are trusted read-only.

To rebuild: create an empty build directory, set LEAN_PATH to build followed by the pinned mathlib and dependency library paths, then for each module in BUILD-ORDER.json in order run lean -j1 -M3500 -DwarningAsError=true -o build/MODULE.olean src/MODULE.lean and leanchecker MODULE, with LEAN_NUM_THREADS=1. Use specific imports as shipped. A 6 GiB address-space limit is too small for this toolchain's import mapping; the checked runs used 32 GiB of address space and a 6 GiB real-memory guard. No olean is shipped. SOURCE-HASHES.json binds every production source.

An independent reviewer performed a fresh extracted replay of all 33 modules from an empty build. Only propext, Classical.choice and Quot.sound are transitive axioms. See FINAL-REVIEW.md and review.json.

Limits: bounded prior-art search; the final journal version of Przybylowski, DOI 10.1016/j.ejc.2025.104289, was not read; upstream libraries were not rebuilt; the relabeling of an abstract transitive tournament to Fin n is not formalized; no peer review, priority or worldwide novelty is claimed.
