# Incomplete P4; zero credit

The literal endpoint `ContactPilot.refutation : ¬ ContactPilot.SourceConjecture`
is absent. This is a partial formalization, not a source conjecture refutation.
No inherited definition was changed or found unworkable.

## Completed in order

1. `SecondBranch.analytic_remainder_three` extracts the actual analytic remainder
   v(x) = -3 + x h(x), with h(0) = 3 - 2 i, using the nonvanishing divided
   difference. `imaginary_order_two` uses real scalar restriction and continuous
   linear maps to prove exact analytic order two. `concrete_orders_six_two`
   constructs both branches of the same exhaustive analytic factorization,
   their remainders and both exact orders, without existence assumptions.
2. `BranchBounds.branch_bounds` gives a simultaneous real neighborhood with
   both roots strictly below the axis for nonzero x, branch distance bounds
   [|x|^6/4, |x|^6] and [|x|^2, 3 |x|^2], and minimum bounds
   [|x|^6/4, |x|^6]. These are estimates for actual analytic roots.
3. `HalfPlane.R_all_roots` transfers exhaustiveness to all w roots, treating
   x = 0 and x ≠ 0 separately. `half_plane_contact_six` proves the precise
   inherited `HasHalfPlaneContact R 6`, including a common radius, all-root
   lower bound, and existence of a small lower-half-plane root for the upper
   bound. It uses c = 1/4, C = 1 and rho = 1.
4. P4 begins in `GraphResolvent`: the actual Fin 5 graph, exact coloring,
   root-to-every-vertex walks, distance one, the actual matrix, its determinant
   and diagonal adjugate, the unconditional total-field identity f = N/Q,
   and the exact clearing identity R(x,w) = x^3 (Q(-1/x,w)-i N(-1/x,w)).

## Next proof obligation

Add a NEW module, leaving the inherited four modules byte-identical. Define
`n q : ContactPilot.Poly₂` by the displayed complex bivariate polynomials

n = (W Z - W - 1) (W Z + W - 1),
q = -W^2 Z^3 + 2 W^2 Z + 4 W Z^2 + 2 W Z - W - 3 Z,

where Z = MvPolynomial.X 0 and W = MvPolynomial.X 1. Prove

`∀ d : Poly₂, d ∣ n → d ∣ q → IsUnit d`.

This is a statement in ℂ[Z,W], not just in the rational function field,
and not a Bezout identity or an `IsCoprime` replacement. The inherited review
suggests irreducibility/primitivity of the two factors and the nonzero
specializations of q at W = 1/(Z-1) and W = 1/(Z+1). Those arguments have
NOT been formalized here. Reduction of the eventual bidisk numerator and
denominator must also be proved after Cayley substitution and clearing;
reducedness of n/q alone does not discharge that obligation.

Remaining P4 obligations, with none silently assumed:

- Explicit bidisk numerator and denominator in Poly₂; no common nonunit
  divisor, denominator nonzero, support degree bounds and reflected-numerator
  identity up to a unit phase.
- Stable denominator on the entire open bidisk and the representation identity
  for beta composed with the actual graphFunction. The graph quotient theorem
  proves a rational identity but supplies no domain/nonvanishing certificate.
- Uniform Cayley zero-set comparison, including conjugation of lower-half-plane
  pole roots to upper-half-plane numerator roots, neighborhood localization,
  and bounds for both coordinate changes and radial distance. No generic
  invariance-of-jets shortcut has been used.
- The inherited `HasZeroSetContact (eval₂ cert.numerator) (-1) 1 6`, and the
  exclusion of contact two. No uniqueness-of-contact theorem is claimed.
- Construct the actual `ReducedCertificate (graphFunction ...)`, combine
  distance one and order six with the universal SourceConjecture, and prove
  `refutation : ¬ SourceConjecture`.

The graph/analytic results do not imply this endpoint without these bridges.
Independent source-fidelity review and root acceptance remain mandatory.
Novelty status is inherited and not newly cleared. Campaign counts are
unchanged at 21/40 beyond the previous 39.
