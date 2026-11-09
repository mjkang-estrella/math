PARTIAL CERTIFICATE ONLY; no full MathDB negation.
Unzip into an empty directory and run:
  python check.py PartialEndpoint.lean
Lean4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 must be present at the pinned read-only paths in check.py. The source module uses no locally generated .olean files. The script sets affinity to two CPUs, passes -j2 -M3500 -DwarningAsError=true, imposes180s and propagates the Lean exit status.
packet-manifest.json binds packet inputs; dependency-hashes.json binds the source-import closure (including built imported oleans). All accepted axioms must be among propext, Classical.choice, Quot.sound.
The shorter individual module files can be checked separately; they intentionally repeat standalone graph definitions, so import PartialEndpoint.lean when using the combined declarations.
