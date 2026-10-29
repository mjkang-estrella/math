Implementation failures are retained in failures/: Local-v1, Lower-v1 through v6,
Transport-v1 through v3, Refutation-v1 and v2, Charges-v1 and v2.
They include missing vector reductions, typeclass/coercion mismatches, a deterministic
200000-heartbeat elaboration timeout in an abandoned eight-bit split, missing/deprecated
Archimedean imports, and premature Transport compiles before Lower had an olean.
Several premature Transport attempts produced the same missing-import diagnostic.
No failed attempt is counted as a checked theorem. The final finite cost equality
uses a closed kernel-decide certificate, not the abandoned split proof.

Audit limitation/protocol deviation: the inherited guard overwrote per-module JSON
receipts during early iterations. Failure source/log copies were preserved, but those
early individual JSON files are not all retained. Resource values remain in the task
tool transcript. Later guard invocations archive prior receipts automatically under
component/attempts. No cap was raised and no guard resource kill occurred.
No mathematical source was edited to disable heartbeat checks. Local and Lower disable
only unusedSimpArgs lint; the audit disables auxLemma lint to print generated names.

All Python edits and packaging run through the copied helper guard, AS512MiB,
groupRSS512MiB, CPU210s/wall230s, 40ms nominal sampling, BLAS threads1.
Lean runs through the copied guard, serial -j1 -M2700, groupRSS2800MiB,
CPU210s/wall230s, 45ms nominal sampling, approved AS infinity only in Lean child.
Initial ZIP copy/extraction used shell unzip, not a Python experiment.
