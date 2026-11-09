# MathDB 371637 — completed formal endpoint, root acceptance pending

The new theorem `WheelFormal.target_proved : WheelFormal.Target` proves, for every natural t >= 1,

fracChromatic (wheelSquare t) = (6t² + 7t + 3)/(2t² + t + 1).

`WheelFormal.wheelSquare_fractional_eq` exposes the same statement directly. There are no residual combinatorial assumptions. The new `attainingColouring` is a literal fractional colouring of the unchanged inherited graph. All three indexed families are proved independent, every vertex has exact coverage 1, and the total weight is the claimed rational expression. Equal independent sets receive the sum of their index weights.

New proof modules are UpperIndexed, UpperCycle, UpperFamilies, UpperCounts, UpperCoverage, UpperAttaining and Final. Every inherited Lean file, including its audit, is byte-identical. All required input files were copied with SHA-256 identity, and the r2a source-packet hash matches the assigned hash.

The deliverable is wheel-complete-source.zip with replay.py and its resource guard. REPRODUCE.md documents the portable LEAN_BIN and LEAN_PACKAGES settings. Full fresh-extraction logs and per-process receipts are in fresh-replay/logs; the complete driver log is logs/fresh-replay-driver.log. Final verification results and audited declaration counts are recorded in results.json and final-verification.json.

Only propext, Classical.choice and Quot.sound occur in the final theorem's transitive axioms. No mathematical gap remains. This lane does not self-accept, change campaign counts, claim novelty clearance or replace independent statement-fidelity review. Root acceptance is pending and awarded credit remains zero until root accepts.
