# Round 3 changes versus round 2

The certificate matrices, child lists, lower-bound proofs and every original theorem statement are unchanged. All 582 Closure modules replace only the combined census proof with four independently kernel-decided node census lemmas and a sum proof using those lemmas. The values are computed from the unchanged graph rows, and each value is then verified by Lean's kernel. This includes Closure270–Closure290, where independent replays revealed nondeterministic failures.

Literal.lean and Delta153.lean replace the umbrella Mathlib.Tactic import with Mathlib.Data.Fintype.BigOperators, Mathlib.Data.List.FinRange, Mathlib.Tactic.NormNum and Mathlib.Tactic.IntervalCases. Every line after the imports is unchanged. This eliminates the broad-import memory pressure that remained after splitting alone. No dependency pin changes.

The census is used by RawResult.certificate_legal_arc_count. RawResult.canonical_original_lower uses lower2327 rather than the census. Thus the census is retained and proved even though the refutation's lower-bound argument does not require its count.

Replay scripts redirect all temporary/cache writes into this lane, record RSS with /usr/bin/time -v, and use explicit -j2. Resource caps are unchanged. REPRODUCE.md is updated. The manifest is regenerated for the final sources. No other Lean files change.

Machine-readable original/final SHA256 hashes and all byte-identical files are in changes.json. logs/changes.diff contains every modified file's textual diff. The verifier scripts/report.py reconstructs each original Lean source exactly by removing the added node census lemmas, reverting only arc_count proof bodies, and restoring the two umbrella imports. Its successful assertion is the byte-level evidence that data and original statements did not change.

Development failures and their corrections are listed in logs/development-incidents.txt. This is implementation evidence, not acceptance; root decides.
