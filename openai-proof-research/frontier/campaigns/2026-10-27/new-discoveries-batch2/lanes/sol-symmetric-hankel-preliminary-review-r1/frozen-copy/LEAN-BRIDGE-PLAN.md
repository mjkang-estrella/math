# Literal formal bridge plan — no Lean run or certificate

Do not begin this before independent source and substantive eligibility review.
Use Lean4.34.1 and the supplied pinned mathlib, autoImplicit false, warningAsError,
serial j1, permitted axioms only;240s per run, process-group RSS sampled40–50ms
and killed conservatively before3GiB. No partial/sorry bridge counts.

Endpoint namespace SymmetricHankel. Define D=Metric.ball(0:ℂ)1;
coefficient(f,n)=iteratedDeriv n f 0/(Nat.factorial n:ℂ), and H as the literal
3×3 determinant of coefficients1..5 (coefficient1 is separately normalized1).
SourceClass f must require DifferentiableOn ℂ f D, f0=0, deriv f0=1 and EXISTENCE
of w with DifferentiableOn ℂ w D, w0=0, ∀z∈D, ‖w z‖<1, and for every nonzero
z∈D the literal quotient equals phi(w z), with denominator nonzero.
At0, record the removable limit1. If source inspection requires univalence,
include Set.InjOn f D and close the additional classical bridges below.
SourceClaim := ∀f:ℂ→ℂ, SourceClass f → ‖H f‖≤(1/16:ℝ).
Final endpoint: source_conjecture_refuted : ¬SourceClaim.
Stronger witness endpoint: ∃f, SourceClass f ∧ H f=−(769/12288:ℂ).
There must be NO existential premise for a realizable jet and NO assumed analytic
primitive/coefficient/class-membership theorem.

1. DiskMobius: literal w z=z²*((1/4+z)/(1+z/4)); prove denominator nonzero,
complex differentiability and norm<1 using the exact difference-of-norm-squares
identity. This establishes every source Schwarz-map hypothesis.
2. AnalyticPrimitive: p=phi∘w; E=(p+p∘neg)/2. Prove evenness and E0=1.
Construct normalized G with G'=(E−1)/z extended at0, by a genuine disk primitive
theorem or convergent power series. Define h=z*exp G and f as the normalized
primitive of p*exp G. Prove holomorphy, derivatives and normalizations on D.
Primitive existence on this star-convex disk must be unconditional.
3. OddPart: show G even by primitive uniqueness, h odd, and derivative of
(f−f∘neg)/2 equals h'. Connected-domain derivative uniqueness closes equality.
Prove exp nonzero, h nonzero off0, literal quotient and removable limit1.
4. Coefficients: analyticity of w and rational identity give derivatives through4;
phi composition gives p jets. Differentiate z f'=p h, or multiply actual Taylor
series. Close literal coefficients a2=0,a3=1/8,a4=15/64,a5=−35/768. This module
must connect the analytic f, not a separate polynomial model.
5. Determinant: exact finite determinant reduction, complex norm of a negative
rational real, and 769/12288>1/16 by norm_num. Combine actual f membership and
actual coefficients for the closed negation endpoint.
6. Only if necessary: prove harmonic lower bound for Re phi using the displayed
boundary polynomial and minimum principle; prove/import starlikeness and
close-to-convex univalence criteria for literal h/f. Do not replace the source
class by the weaker A-based class if univalence is a literal requirement.

Independent extraction must audit every actual mathematical-origin declaration,
including generated/private/instances, and the final type/axioms. No helper
certificate alone establishes this source claim. No estimated declaration count
or feasibility PASS is asserted.
