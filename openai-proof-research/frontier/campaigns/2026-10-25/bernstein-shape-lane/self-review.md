# Implementation self-review

This is an implementation self-review, not a substitute for the parent's independent review.

## Result and scope

- The main declaration `BernsteinShape.bernstein_square_sum_convex` has the exact finite sum from MathDB 327180 and type `ConvexOn ℝ (Set.Icc 0 1) ...`, with an unrestricted natural parameter `n`.
- `convexOn_univ` proves the stronger global polynomial statement.
- `antitoneOn_left`, `monotoneOn_right`, `midpoint_minimum`, and `midpoint_value` prove the related shape and sharp minimum conclusions. They are corollaries within one outcome.
- The case `n=0` is included. The only normalizing denominator in the Fourier argument is `n+1`, proved nonzero; no assumption `n>0` is hidden.

## Crucial bridge review

1. `character_orthogonality` sums over `ZMod N` but indexes coefficients by `Fin N`. It proves residue equality is equivalent to equality of the bounded indices. This is the precise no-aliasing condition.
2. `finite_parseval` expands complex conjugates, swaps only finite sums, and cancels off-diagonal terms. Coefficients are arbitrary real numbers, so no unnoticed restriction to x in [0,1] occurs.
3. `binomial_fourier` applies the binomial theorem to the original `basis`, not to a surrogate polynomial.
4. `finite_average_identity` proves the exact identity for `phi`; it is not an assumption or an input hypothesis.
5. `convex_norm_affine_power` handles the zero power and uses norm nonnegativity. Convexity is preserved under finite sums and positive scaling.
6. `phi_eq_expanded` bridges the squared basis definition to the literal binomial-square and even-power formula requested.

## Corollary review

- Reflection of the finite range proves symmetry, with `choose_symm` and bounded natural subtraction discharged explicitly.
- Convexity at the average of x and 1-x proves the midpoint minimum.
- The left monotonicity proof uses convexity between x and the midpoint, including separate equality/end cases; reflection proves the right half-line assertion.
- The exact midpoint constant follows from the standard finite Vandermonde square-sum identity. It is not inferred by evaluation at finitely many n.

## Independent identity derivation

The proposed central-binomial coefficient identity is derived in the paper through an explicitly evaluated trigonometric moment integral. Its beta-moment recurrence and initial value determine all coefficients. The exact integer regression for n=0,...,32 confirms implementation/transcription only. This continuous identity is not formalized and is not used by the Lean theorem; it is therefore not an unpaid bridge.

## Verification evidence

`build/audit.json` reports PASS with Lean 4.34.1, 20 declarations, and only `Classical.choice`, `Quot.sound`, and `propext`. `build/Checks.log` records every declaration's type and axiom list. The verifier is the unmodified campaign verifier, loaded by a wrapper that implements its dependency metadata inspection in pure Python and disables optional index writes. Compilation and source-copy checking are unchanged.

The four-page PDF has been rendered and visually reviewed. The final TeX log has no overfull or underfull box warning. The original source pages carrying Conjectures 3.2-3.4 and Lemma 3.5 were also rendered and inspected.

## Attribution and limits

The convexity theorem is known from Nikolov (2014), and a Parseval-based proof was given by Gavrea and Ivan (2014). Their full article was not retrieved, so only accessible bibliographic and abstract-level claims are made about that proof. The original source itself already proves the minimum with credit to Neuschel. No claim of mathematical novelty or first formalization is made. Parent independent review and campaign integration remain pending.
