# Remaining genuine source bridges after the averaging representation

2026-10-28. This is a work plan, not a completed certificate of Conjecture 3.
The final source theorem in SourceAssembly still has its explicit positivity premise.

`approxTransform_eq_finiteBetaAverage` now identifies the literal approximating
series with the finite Beta-average of the literal E_(1/2)(z sqrt(v)). It uses
actual partial sums, a summable uniform majorant, contractive normalized averages,
and dominated convergence. No existence of a stable distribution is assumed.

The squared-average bridge below is now implemented in SquaredAverage.lean.
The only remaining mathematical kernel bridge is item 1:

1. For the half-order cross kernel
   Re(E_(1/2)(i sqrt(v*t)) conjugate(E_(1/2)(i sqrt(w*t)))), prove the positive
   angular Laplace identity of the frozen ordinary PROOF.md. Neither this identity
   nor its positivity is present in the current component. One implementation
   route derives E_(1/2)(i x)=exp(-x²)(1+i erfi(x)) from the actual series,
   writes the erfi product as a rectangle integral, and applies the polar
   change of variables with an explicit angular split. The zero-scale cases
   require separate handling or a proved continuous extension.
2. IMPLEMENTED: squaredApprox_eq_doubleAverage proves that the squared norm
   of the actual finite complex average is the double real average of the
   literal halfCross kernel. All continuous-linear integral commutations,
   cross-kernel continuity, and actual complex-series analyticity are proved.
   sourceClaim_of_halfCross_positive reduces the full source theorem to
   nonnegative mixed differences of halfCross for both scales >=0; this
   remaining premise is explicit and unproved.

BetaAverages already proves preservation of positive mixed differences under
one or finitely many real averages. DifferenceCriterion proves passage to
positive-argument pointwise limits and to all alternating derivatives. Once
the kernel bridge proves positivity for the actual squaredApprox, the printed
conditional theorem sourceClaim_of_positiveMixedApprox supplies the literal
source endpoint. Until then there is no unconditional source certificate,
full formal PASS, paper, acceptance or discovery credit.

Source/journal fidelity, bounded prior art, and substantive eligibility remain
independent gates under the running preliminary review. A successful helper
replay never clears any of those gates.

A simpler alternative to the polar proof is recorded in ONE-DIMENSIONAL-KERNEL.md: a sum of two positive rationally weighted Laplace integrals, identified by a first-order ODE and an arctangent initial value. Its 20 high-precision checks are diagnostics only; this identity has not yet been proved in Lean.
