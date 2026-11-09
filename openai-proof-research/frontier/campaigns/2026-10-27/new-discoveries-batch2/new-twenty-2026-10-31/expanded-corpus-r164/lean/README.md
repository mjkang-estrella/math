This is an incomplete Lean packet for candidate MathDB 333709.

PlaneData.lean defines the literal 31-point incidence structure, the exact unbounded source predicates, and auxiliary finite diagnostics. It deliberately does not prove TargetNegationOnThisPlane. The principal UNSAT certificate is in ../outputs/percolation-5-5.lrat, with a dependency-trimmed version and an independently run Python RUP checker. See ../CANDIDATE.md for the complete mathematical argument and the four formal gaps.

The pinned executable is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean, version 4.34.1. Every invocation must use -M3500 and the lane resource wrapper. No mathlib dependency is needed for the current auxiliary file. No full kernel replay or leanchecker pass for the proposed refutation is claimed.

The first generator is retained as scripts/make_lean_prototype.py for provenance; it produced the failed first attempt and must not overwrite the revised final source. The final PlaneData.lean uses explicit closed separators to avoid repeated closure evaluation. The fresh strict replay is in replay/, and logs preserve both failures and successful rebuilds.
