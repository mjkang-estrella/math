# Root HS/trace support module — compile PASS, no discovery credit

Nine declarations compile warningAsError=true with pinned Lean4.34.1/mathlib.
All actual types and axiom reports in formal/Checks.log were read; standard3
only. Proved: hsSq nonnegativity/adjoint invariance, two exact trace identities,
isometry/coisometry multiplication invariance, trace of frame-projection
products, and orthonormal columns underU*U=I. No matrix norm instance changes.
Arbitrary finite/empty rectangular types allowed. Standard infrastructure.

Remaining: Bessel cross-Gram row/column bounds, grading/block pinching, frame
existence and injectivity from source projection hypotheses, and full source
inequality assembly. The graded spectral worker may copy this STABLE file;
root will extend in new modules so these bytes remain unchanged.

Root extension: CrossGram.lean and ProjectionFrames.lean compiled strictly; all 19 combined named declarations audited in ChecksExtended.log, only standard3 axioms. extended-audit.json preserves the exact source/log hashes. Original audit.json remains the 9-declaration HS-only receipt. Full source endpoint absent.
