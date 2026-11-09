# Reproduce the partial r4c packet

Extract xor-magic-r4c-partial-source.zip into a new empty directory inside the authorised lane. Set LEAN_BIN to the Lean 4.34.1 binary (commit 5045d0056413266e57c625dcd7c365b10e377c52) and LEAN_PACKAGES to the pinned mathlib package directory (mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612). Run `python3 -I replay.py` from the extracted directory. No network is used.

The driver refuses existing oleans, verifies all source hashes, clears the inherited environment and rebuilds each module using `lean -j1 -DwarningAsError=true`. Each expensive call is limited to 2 CPUs, 120 CPU seconds, 140 wall seconds, sampled private RSS 6 GiB and address space 64 GiB, with MALLOC_ARENA_MAX=2. Every call has a log and JSON receipt.

It then checks every local proof-module declaration, including generated declarations, through the four audit modules: full type and body (`value? true`), module, safety/partial flags and transitive axioms. Only propext, Classical.choice and Quot.sound are allowed. The shared expression DAG audits are separately checked for all node references and declaration roots. Leanchecker runs on every proof and audit module. Fifteen negative controls must fail specifically by kernel decide reporting a false proposition. Running the driver a second time must refuse the newly built oleans.

This validates only the partial packet. See GAPS.md before interpreting any endpoint.
