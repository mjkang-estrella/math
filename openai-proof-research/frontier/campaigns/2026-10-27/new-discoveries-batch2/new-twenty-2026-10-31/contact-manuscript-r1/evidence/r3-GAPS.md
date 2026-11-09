# Partial formalization; zero credit

The literal `ContactPilot.refutation : ¬ ContactPilot.SourceConjecture` is absent.
No source definition or inherited module was changed. Campaign counts remain
21/40 beyond the previous 39. Only root may accept.

## Completed first obligation

`numerator_denominator_reduced` (in namespace ContactPilot) proves
exactly `∀ d : Poly₂, d ∣ n → d ∣ q → IsUnit d` for the assigned polynomials.
Both factors are irreducible in the original complex bivariate ring, using
`finSuccEquiv` and coprime coefficients of a linear polynomial. Evaluating at
(z,w) = (0,-1) and (0,1) rules out their divisibility into q. This is not merely
a rational-function-field computation or a Bezout replacement.

`CayleyPolynomials` defines the explicit cleared pair, proves both clearing
identities, their common boundary zero, denominator nonzeroness as a polynomial,
and representation of beta(n/q) whenever the two coordinate denominators and q
are nonzero. `cleared_pair_reduced` proves reducedness of q ± i n BEFORE the
Cayley transformation. It does not prove reducedness AFTER clearing.

## Transformed reducedness completed

`BidiskReduced.bidisk_pair_reduced` (namespace ContactPilot) proves the exact
common-divisor statement for the existing bidiskNumerator and bidiskDenominator.
The three factors of cayleyN are irreducible; the two bilinear factors use
coprime affine coefficients with determinant 4, and evaluations at (1,-i),
(1,i), and (-1,0) exclude their dividing cayleyQ. Invertible scalar linear
combinations finish reducedness of the bidisk pair itself.

## Exact next required lemma

For the existing polynomial, prove:

```lean
theorem bidisk_denominator_stable : ∀ z w : ℂ,
  ‖z‖ < 1 → ‖w‖ < 1 →
  ContactPilot.eval₂ ContactPilot.bidiskDenominator z w ≠ 0
```

A concrete route is the actual graph resolvent on the upper half-plane:
prove its matrix invertible using the negative definite imaginary part of
A − diag(z,w), and prove Im(f)>0 from its inverse. Then Q and Q−i N are
nonzero at upper-half-plane coordinates. Combine this with the coordinate
Cayley imaginary-part formula and the checked clearing identities. No such
matrix positivity or global nonvanishing theorem is supplied here.

## Remaining ordered obligations

1. Complete the reduced bidisk certificate: denominator
   stability on the ENTIRE open bidisk; bidegree (3,2) support bounds; reflection
   identity with an explicit unit phase; unconditional representation for the
   actual graph function on the bidisk. The present quotient identity retains
   a q-nonzero premise and does not prove stability.
2. Uniform transfer of `HasHalfPlaneContact R 6` to
   `HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6`, with explicit constants,
   coordinate-neighborhood localization and conjugation of pole roots.
3. Exclusion of contact two using the two-sided comparisons.
4. Assemble `ReducedCertificate (graphFunction candidateGraph candidateColors 0)`
   and the literal negation of SourceConjecture. No certificate is constructed
   by this partial packet.
5. Repeat final validation after those additions and obtain independent source
   fidelity review and root acceptance. A replay of the present partial packet
   certifies no missing bridge. Novelty limitations in contact-review-r1 remain.
