# Reproduction

From this lane run `python scripts/replay.py`. It deletes its own fresh-extracted directory, safely extracts the flat proof-packet.zip (rejecting path separators and dot paths), and runs strict Lean, the complete axiom audit, and leanchecker. It retains stdout/stderr and exit codes in outputs/fresh-*.log and outputs/replay.json.

For a standalone extraction of proof-packet.zip: set PATH to include the pinned Lean bin directory and LEAN_PATH to the extraction directory followed by each read-only package .lake/build/lib/lean directory under the pins.json cache. Run `lean -j1 -DwarningAsError=true -o SignedMass.olean SignedMass.lean`, `lean -j1 -DwarningAsError=true Audit.lean`, and `leanchecker SignedMass`. Use the lane limited.py wrapper (2 CPUs, CPU120s, wall139s, RSS6GiB; AS64GiB only for memory mapping) for each process. No lake dependency update or upstream writes are needed.

The source file contains no sorry/admit, added axiom, unsafe code, native_decide or ofReduceBool. ListDeclarations.lean enumerates all module-local names; Audit.lean checks all45 generated and public names programmatically and prints axioms of public endpoints. `leanchecker` is kernel verification against trusted imported modules; this does not rebuild the mathlib cache.
