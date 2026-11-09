# Bergman finite convolution helper

This is a generic algebraic helper for the full Edholm–Mathew unit-circle argument, not a separately counted result. The source-specific polynomial, residue grouping, nonvanishing and root-allocation statements are owned by the parent and polynomial worker.

`formal/BergmanConvolution.lean` imports only Mathlib. It compiles with pinned Lean4.34.1 and warningAsError. Frozen SHA256:6935d787b9b9454951fc7f3036fa29b6d2d86364ea9245dbbfca79b7c5392e13.

Exact API:

- `triangle m r := if r < m then r+1 else 2*m-1-r`.
- `card_pairFiber` proves this counts ordered p,q<m with p+q=r, by an explicit bijection to the integer interval [r+1−m,min(m,r+1)).
- `triangle_sum` groups any AddCommMonoid-valued function by these exact multiplicities.
- `triangle_sum_two` gives two independent triangular convolutions as the ordered quadruple sum.
- `reflect_quadruple_sum` complements p′ and q′ using the finite range reflection involution.
- `triangle_sum_reflected` combines the two previous steps, directly producing F(p+(m−1−p′),q+(m−1−q′)).

The convolution endpoints assume only0<m. Reflection allowsm0aswell. No commutative-ring structure, cancellation, spectral result or source assumption is required.

Fresh isolated source replay and all7declaration axiom audit: `build/fresh-audit-jxv4gf7_/receipt.json`, SHA2564e8aacb7bbe62be7f15d5cca7bb37fba5e6fa81e6372ec021bed95393c6a27e1. Every audited declaration uses only propext, Classical.choice and Quot.sound (or fewer). No sorry, native_decide, new axiom, unsafe declaration, or linter suppression appears.
