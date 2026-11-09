# Reproduce r4

Extract contact-r4-source.zip into a new empty directory. The packet contains source only and refuses pre-existing local oleans, ileans, ir files, or a build directory. It does not modify the package cache.

Set LEAN_BIN to the pinned Lean 4.34.1 executable (commit 5045d0056413266e57c625dcd7c365b10e377c52), and LEAN_PACKAGES to the read-only pinned mathlib package cache (mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612). Run:

```sh
python3 -I -B scripts/replay-r4.py
```

The inherited replay.py reproduces only the inherited r3 modules. Use replay-r4.py for all 18 r4 modules. Every Lean and leanchecker invocation uses the inherited resource watchdog: at most two CPUs, CPU limit 120 seconds, wall limit 140 seconds, sampled private RSS limit 6 GiB, MALLOC_ARENA_MAX=2. Calls run serially. Strict compilation uses -j1 -DwarningAsError=true. Logs and receipts remain in replay-logs; large full logs are gzip-compressed losslessly.

AuditR4 inventories every declaration from all local modules, including generated names, full expression DAGs for type and opaque-inclusive value, unsafe/partial flags and transitive axioms. The audit parser rejects flags and axioms other than propext, Classical.choice and Quot.sound. Eleven negative controls must fail normally, without watchdog termination. This replay validates a partial certificate, not the missing unconditional contact endpoint.
