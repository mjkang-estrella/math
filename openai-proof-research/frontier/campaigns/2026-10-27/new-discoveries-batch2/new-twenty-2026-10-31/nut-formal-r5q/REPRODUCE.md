# Reproduce the partial r5q packet

Use Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52,
and the read-only mathlib package cache pinned at
 d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract `nut-r5q-source.zip` into a NEW EMPTY directory. Set `LEAN_BIN` to
the absolute Lean executable and `LEAN_PACKAGES` to the package cache directory
whose children contain `.lake/build/lib/lean`. Run:

```
python3 -I replay.py
```

The driver refuses existing `.olean` files and existing replay logs. It constructs
a sanitized environment, with HOME and TMPDIR inside the extraction, and compiles
all modules in modules.json sequentially with `-j1 -DwarningAsError=true`.
Every Lean and leanchecker call uses the private-memory watchdog, at most two
CPUs, 120 CPU seconds, 140 wall seconds and MALLOC_ARENA_MAX=2. Full logs and
JSON receipts stay inside the extraction. AuditR5 prints every local declaration,
including generated declarations, its module, full type, opaque-inclusive body,
unsafe/partial/axiom flags, and transitive axioms. Anything beyond propext,
Classical.choice and Quot.sound fails the audit.

Negative controls test altered determinant values, invalid signs, invalid graph
isomorphisms, a wrong permutation lookup, nonunit switching, incorrect diagonal
fills, and incorrect parent data. The existing-olean refusal is also tested.

`python3 -I scripts/reconcile.py` reruns the diagnostic matrix-set comparison.
This is not part of the trusted proof. Its output gives exactly 669 unsigned
patterns and 9,172 distinct normalized matrices, matching r2 after relabelling
and switching. No downloaded data are executed and no external packages are used.

A successful replay is a replay of a PARTIAL packet. It does not prove
`Nut8.PerSupport`; see GAPS.md. Root alone may adjudicate acceptance.
