# Reproduce the partial r3b packet

Extract nut-r3b-source.zip into a new empty directory. Set LEAN_BIN to the
Lean 4.34.1 executable (commit 5045d0056413266e57c625dcd7c365b10e377c52)
and LEAN_PACKAGES to the read-only mathlib package directory pinned at
 d13f23b723b8a846827a245b89c10fc7d3f11612. Then run:

```sh
python3 -I replay.py
```

The driver refuses any preexisting .olean anywhere below the extracted root.
It sanitizes the environment, writes HOME/TMPDIR only below the extracted
root, invokes strict lean -j1 -DwarningAsError=true, runs leanchecker for each
module, prints all local declaration types and opaque-inclusive bodies,
checks unsafe/partial/axiom flags and transitive axioms, and requires all five
negative controls to fail without hitting a resource cap. Only propext,
Classical.choice and Quot.sound are allowed. Each individual process has the
inherited 2 CPU affinity, 120 CPU second, 140 wall second, 6 GiB sampled private
memory watchdog and MALLOC_ARENA_MAX=2. Calls are sequential. Full logs and JSON
receipts are below logs/. A PASS applies only to the explicitly partial packet.

Generator scripts are ordinary offline producers, not trusted proofs:

```sh
python3 -I scripts/generate_graph_extensions.py
python3 -I scripts/generate_closures.py
python3 -I scripts/generate_certificates.py 32 32
```

Run generation in a separate fresh extraction before replay, since replay
refuses existing oleans. Graph closure modules check all eligible neighbor
masks for each listed support. Canonicalization is only an offline method for
finding witnesses; Lean checks the explicit permutations. The 32 certificates
are a measured batch, not the complete 9,172-record obstruction.

The successful fresh-extracted sources must match packet-manifest.json.
GAPS.md specifies what is unproved. No invocation proves finite_obstruction.
