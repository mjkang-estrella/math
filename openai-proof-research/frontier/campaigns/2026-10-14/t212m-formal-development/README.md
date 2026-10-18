# T212M provisional scoped Lean support

Status: parent/coauthor development; fresh local compilation passes. Independent formal review has not run. This is not a formalization of the full moment-free planar theorem and creates no acceptance or count change.

`T212M.lean` proves deterministic finite-change stability of calibrated escaping walk segments on an arbitrary simple graph. For a finite changed edge set F, the cost budget is Δ = sum over F of |w′(e)−w(e)|. An edge-simple competitor visiting a point at original distance at most C from the root pays at least d(a,b)+2d(x,a)−2C−Δ. Thus sufficiently late calibrated segments remain minimal against edge-simple competitors. The strengthened `ray_tail_stable_all_walks` additionally assumes nonnegative modified weights and derives minimality against every finite walk through loop erasure. Avoidance of F is derived from calibration and nonnegative original weights, rather than assumed in the tail theorem.

`Controls.lean` instantiates the inequality on a four-vertex graph and kernel-proves two counterexamples to deleting hypotheses: repeatedly traversing a changed edge exceeds the one-copy budget, and an unchanged early geodesic loses minimality after another edge becomes cheaper.

Rebuild from this directory with `python3 -B rebuild.py --output /var/tmp/t212m-fresh-output`, choosing a nonexistent output directory. Optional `--lean` and `--cache` override the recorded compiler/dependency cache locations. No network or dependency mutation is required. The nine dependency revisions and compiler commit are checked, but cached dependency objects are trusted, not rebuilt. Source modules are compiled afresh; all 31 declared definitions/theorems have their elaborated types and axiom dependencies recorded. Only propext, Classical.choice and Quot.sound occur. The fresh r5 build produced no warnings.

The recorded receipt binds the two Lean sources. It does not authenticate this entire development directory; it is unsealed pending review and any repair. See coverage.md and provenance.md.
