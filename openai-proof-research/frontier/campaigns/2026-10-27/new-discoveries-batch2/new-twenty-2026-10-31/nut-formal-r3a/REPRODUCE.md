# Portable strict replay (partial packet only)

Extract `nut-r3a-source.zip` into a new empty directory. The packet contains only
Lean sources, the replay driver, the capped process wrapper, and documentation.
It contains no olean files and no precompiled local dependencies. Set:

```sh
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/path/to/pinned/.lake/packages
python3 -I replay.py
```

Use Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, and
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, with its pinned cached packages.
LEAN_PACKAGES denotes the directory containing mathlib and sibling packages.
The provided leanchecker next to LEAN_BIN is required. The driver sanitizes its
child environment, puts HOME and TMPDIR inside the extraction, and refuses any
existing olean under the extraction before compiling.

Every Lean and leanchecker call runs separately with one Lean worker, warning
errors for elaboration, at most two CPUs, CPU 120 seconds, wall 140 seconds,
MALLOC_ARENA_MAX=2, and a sampled 6 GiB private-memory watchdog. Only one child
runs at a time; the wrapper waits and reaps it. Full output and JSON receipts
are written under logs. The audit prints module, full type, opaque-inclusive
body, flags, and transitive axioms of every local declaration including generated
ones. It rejects unsafe, partial, axiomatic declarations and all transitive
axioms except propext, Classical.choice, and Quot.sound.

The three Lean negative controls reject a wrong determinant, a nonexistent
endpoint inferred from an unrelated lemma, and a false sign equality. A fourth
control checks the refusal of existing oleans. A successful replay checks the
partial packet; it does NOT establish endpoint_of_finite or acceptance.

The parent lane's `inputs-before.json` and `inputs-after.json` bind the read-only
inputs. Copies under inputs have identical hashes. All inherited formal Lean
sources are byte-identical. The source packet's formal files must match the
successful fresh extraction, as recorded in packet-manifest.json.
