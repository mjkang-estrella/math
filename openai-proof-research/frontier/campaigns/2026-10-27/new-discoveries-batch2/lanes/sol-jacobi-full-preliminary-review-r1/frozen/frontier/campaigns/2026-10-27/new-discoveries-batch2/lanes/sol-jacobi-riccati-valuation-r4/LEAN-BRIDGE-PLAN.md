# Literal Lean bridge plan and actual start

2026-10-28. Complete ordinary proof: PROOF.md. This is a plan for a full
certificate, not a claim that the endpoint below has been implemented.

Pinned compiler: Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52.
Pinned mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612 from the supplied
2026-10-14/formal/lake-manifest.json. No package update, lake build, git command,
or shared-artifact write was performed.

## Actual verified start

formal/ArithmeticStart.lean has one definition Dyadic and five checked lemmas:
dyadic_mul, dyadic_doubled_product, dyadic_weaken, dyadic_square,
dyadic_doubled_product_weaken. They encode the scalar arithmetic in the two
weighted closure steps. Every #print axioms report is exactly [propext].
The actual run exits 0; formal/lean.log and formal/lean-receipt.json are retained.
Only Init.Data.Nat.Dvd and Init.Data.Nat.Lemmas are imported with `prelude`, to
avoid loading the full Init/mathlib graph under the memory constraint.
This start does not prove binary-weight closure for polynomials, the primitive
lemma, the Riccati/source bridge, attainment, or the literal endpoint.

An initial broad PadicVal import failed (nonexistent Mathlib.Tactic.Omega module)
and used 642500 KiB RSS, exceeding the requested 512 MiB ceiling. This was an
actual resource violation, not a successful bounded run. The exact failure is
formal/failed-padics-import.log; its source is BinaryFiltration.initial.txt.
Subsequent hard 480 MiB address-space attempts could not initialize a Lean
thread; formal/failed-address-space.log records the error. Later guarded imports
were stopped below 512 MiB. The final selective prelude run uses about 171 MiB,
with actual observed peak recorded in the receipt, a 470 MiB RSS kill threshold,
and 4 GiB virtual-address limit (virtual address space is not resident memory).
BinaryFiltration.draft.txt is an uncompiled arithmetic draft, explicitly excluded
from the verified inventory. No axiom-free claim is made for failed declarations.

## Intended literal endpoint

Define the source polynomial `sourceKappa r : MvPolynomial (Fin 2) ℚ` by the
finite coefficient extraction of Area's equation (6) and logarithm, evaluated at
x0=(1+i)/2, y0=(1-i)/2, taking coefficientwise imaginary parts and dividing by
2^(2r-1). Define its parameters directly as u,v, replacing every Hankel product
by prod_(j<l)(u-j(j+1))/(2^l*l!), and similarly for v.
A finite Gaussian-rational pair representation can avoid analytic Complex APIs.
Define `TwoLocal q` by oddness of q.den, equivalent to membership in Z_(2).
Define `dyadicExponent r = 2*r + padicValNat 2 ((r-1)!)`.

Final theorem, with no unproved bridge premises:

    ∀ r, 1 ≤ r →
      (∀ m, TwoLocal ((2:ℚ)^(dyadicExponent r) *
                       (sourceKappa r).coeff m)) ∧
      ¬ TwoLocal ((2:ℚ)^(dyadicExponent r - 1) *
                       (sourceKappa r).coeff (Finsupp.single 0 r))

The pure-u witness pins exactness, not merely an unspecified minimum.
Handle r=1 separately in the exponent decrement if needed. This theorem is
explicitly the formal Definition 2.1 object, not an arbitrary Riccati sequence
or a certificate assuming equality with that sequence.

## Remaining modules and exact obligations

1. **Literal finite series.** Define P_l, C_s, inverse-factorial coefficients
   via Stirling numbers, F and formal log coefficients. Prove the agreement
   with the rational-pair definition of sourceKappa. All coefficient sums at
   fixed index are finite; the logarithm sums over compositions of that index.
2. **Source-to-Riccati.** Encode the r3 formal curve calculation, including
   2xy=x+y, the coefficient differential identity for C_s, Z e_s=e_(s-1)+s e_s,
   D²F+2iZ DF-VF=0, and unique Riccati logarithmic derivative. Prove imaginary
   t-oddness and kill constants. Derive equation (1) of PROOF.md for literal
   sourceKappa; do not use analytic phase identification as a hypothesis.
3. **Midpoint normal forms.** Use pairs of polynomials (A,B) representing A+wB,
   with product (AC+(1+x²)BD,AD+BC) and derivation
   (-(1+x²)A', -xB-(1+x²)B'). Equivalently use a monic quadratic AdjoinRoot,
   proving uniqueness of this normal form. Prove the rational Laurent embedding
   x=(t-t^-1)/2,w=(t+t^-1)/2 and its inverse, D=2 partial, V=2P, and homogeneous
   scaling. Record rho/tau separately; establish ideal-(w) and support facts.
4. **Binary filtration.** Define sigma(n)=(Nat.digits 2 n).sum and
   q(i,j)=sigma(i)+sigma(j)-1 for i+j>0. Prove sigma subadditivity, doubling,
   and sigma(2k+1)=sigma(k)+1. Lift the verified scalar divisibility steps to
   finite-support parameter coefficients over the midpoint integral algebra.
   Prove closure under 2fg and f², explicitly pairing unequal monomials in
   the square. Pair unequal spectral indices in the convolution, retain the
   even-index diagonal square, and prove filtration preservation by strong
   induction. Then prove the j-odd weight bound by subadditivity at i+(j-1).
5. **Primitive.** Implement downward finite recursion (13) on polynomial degree
   over the subring TwoLocal. Show every denominator 2k+1 is a unit, prove
   equation (12) and preservation of divisibility by each fixed 2^e. Handle the
   w-even part by odd-denominator polynomial integration and midpoint zero.
   Prove tau-oddness and uniqueness in the rational Laurent ring so the result
   is exactly J_t, without a new normalization premise. Substitute a=u+v,b=u-v
   by an integral polynomial homomorphism only. Conclude degree-specific (3).
6. **Attainment and assembly.** Formalize r3's Catalan top-degree proof and the
   primary's Theorem 1.4 binomial valuation (or a proved library theorem with
   literally equivalent finite sum; no new axiom). The ordinary source theorem
   is a dependency, not an already available Lean certificate. Combine factorial
   valuations with (1), (3), and the pure-u formula to close the endpoint above.

Root must review the complete ordinary proof before major formal investment.
A complete formal development, independent review, manuscript/packet, and root
acceptance remain required. No discovery count is requested for this start.
