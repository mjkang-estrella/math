# Strict convexity of Gamma-ratio level curves

For every c>1 and x>0, a unique positive height h_c(x) satisfies
Gamma(h_c(x))Gamma(h_c(x)+2x)/Gamma(h_c(x)+x)^2=c.
The height is strictly convex on x>0. At c=2 this resolves published
Garrappa–Gerhold–Popolizio–Simon, JMAA551(2025)129588, Remark16(a).
The separate complete-Bernstein questions are not claimed.

paper.pdf and main.tex give the ordinary proof. Run python3 verify_candidate.py
for a fresh source replay: nine modules, 52 public declarations, standard
three axioms only, no residual premises. The verifier checks the absolute
Lean4.34.1 binary hash/version and all eight installed package revisions,
including Mathlib d13f23b723b. Dependency paths in pins/run_lean must be
configured on a different machine; no dependencies or candidate oleans
are vendored. Actual types and axiom reports are in verification/Checks.log.

reviews/ contains independent preliminary, perspective-reassessment and
final reports. All gates PASS within recorded bounded novelty limits.
ROOT-ADOPTION.md preserves the strongest short/routine objection and root's
judgment. Classical perspective convexity, Euler product and Jensen are
credited, not claimed new. historical/ preserves the exact reviewed paper
and status documents; their pending labels are superseded by this README.

One family only. The final archive receipt and acceptance decision are
separate campaign files bound to the precise archive SHA256. No posting,
publication, upload or MathDB edit has been performed.
