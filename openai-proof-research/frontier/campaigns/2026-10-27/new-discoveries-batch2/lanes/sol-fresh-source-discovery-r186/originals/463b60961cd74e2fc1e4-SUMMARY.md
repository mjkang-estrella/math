# Root strict-convexity component

Four modules compile with warnings as errors:

- GammaDefs: literal Real.Gamma ratio, defect, profile and source proposition.
- ProfileConvex: exact first and second derivatives; strictly convex profile.
- StrictJensen: adjusted weights, affine-shift identity, distinct shifts,
  termwise Jensen and a strict infinite-sum inequality.
- ConvexAssembly: conditional defect-mixture and level-height strict convexity.

All 17 declaration types and axiom reports were read by root; only propext,
Classical.choice and Quot.sound occur. See formal/Checks.log and the fresh-copy
replay under verification/. These are supporting results, NOT a complete
source-level certificate. ConvexAssembly explicitly assumes the genuine
Gamma HasSum bridge and strict antitonicity; level existence is also unproved.

The ordinary candidate remains frozen under root-gamma-level-r1. This lane's
PERSPECTIVE-OBJECTION.md supplies an explicit classical reduction overlooked
by the preliminary review's substantive discussion. Large formal investment
and paper work are deferred pending an independent re-adjudication. Partial
Gamma bridge worker was stopped with files preserved. No count or acceptance.

Reproduction: in formal/, python3 run_lean.py MOD.lean -o MOD.olean in the
listed order, then python3 run_lean.py Checks.lean. Pinned Lean4.34.1 and
Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 via run_lean.py.
