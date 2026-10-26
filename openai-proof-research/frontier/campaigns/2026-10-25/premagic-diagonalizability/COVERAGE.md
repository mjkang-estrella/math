# Formal coverage

The main statement is the actual negation of the selected conjecture:
there exists a real premagic matrix which is not diagonalizable, even after
viewing its entries in the complex field. It is not merely a verification of
a numerical example's row sums.

## Definitions and principal proof

`PremagicCounterexample.Diagonalizable A` means that there are matrices
`P`, `Q`, and a diagonal vector `d` such that `P*Q=I`, `Q*P=I`, and
`A=P*(Matrix.diagonal d)*Q`. This is ordinary diagonal similarity with the
inverse made explicit. Equivalently, the columns of `P` form a basis of
eigenvectors: multiply the displayed identity on the right by `P`.

`PremagicCounterexample.Premagic A` means equality of corresponding row and
column sums. It is precisely the source definition.

`square_kernel` proves for an arbitrary finite square matrix over a field
that diagonalizability implies `A*(A*x)=0 -> A*x=0`. `chain_image` and
`kernel_image` prove an explicit nontrivial length-two Jordan chain for `M`.
`not_diagonalizable` deduces non-diagonalizability over every
characteristic-zero field. `row_sum`, `column_sum`, `premagic` and
`positive` check the remaining hypotheses exactly. `main_counterexample`
combines positivity, the premagic property, and non-diagonalizability over
both the real and complex fields.

Two equivalence theorems, `diagonalizable_iff_similarity` and
`diagonalizable_iff_inv`, formally identify the definition with the usual
invertible-similarity formulation using mathlib's matrix inverse.

## Formally checked extensions

`A_t_not_diagonalizable` proves that `M + t I` is not diagonalizable over
every characteristic-zero field, for every scalar `t`.
`A_t_row_sum`, `A_t_column_sum`, `A_t_premagic`, and `A_t_positive` establish
the sums, premagic property and (for real `t >= 0`) strict positivity.

For real `t >= 0`, `B_t_positive`, `B_t_doubly_stochastic`,
`B_t_premagic` and `B_t_not_diagonalizable` certify the normalized matrix's
strict positivity, unit row/column sums, premagic property and failure of
real diagonalization. The complex version of the normalized-family
assertion is proved in the paper by scaling; it is not a separately
formalized theorem. The complex non-diagonalizability of `M` and of every
complex scalar shift is fully formalized.

The existential statements and universal negations appear explicitly as
`exists_premagic_not_diagonalizable`, `not_all_premagic_diagonalizable`,
`exists_positive_premagic_not_diagonalizable`,
`not_all_positive_premagic_diagonalizable`, and
`exists_positive_doubly_stochastic_not_diagonalizable`.

The final file contains 37 audited declarations (8 definitions and 29
theorems), including the conventional-definition equivalences. The detailed
review is in `formal/notes/formal-audit.md`.

## Deliberate distinctions

The paper's minimal-dimension observation uses the real spectral theorem.
The arbitrary-dimension extension follows from a written rank-one
calculation. Neither observation is needed to refute the conjecture, and
neither is claimed to be certified by `main_counterexample`.
The characteristic-polynomial, determinant and Jordan-form formulas also
have complete written proofs and exact-arithmetic checks, but are not
themselves statements certified in this Lean file.

Exact-arithmetic Python computations independently check matrix identities,
ranks, determinants and the Jordan change of basis. Those computations are
diagnostics, not substitutes for universal Lean theorems.

All certified declarations and their exact types are printed by
`formal/Checks.lean`. The formal build checks that their axiom lists use
only Lean's standard logical foundations (`propext`, `Classical.choice`,
`Quot.sound`). The claim is kernel verification in Lean with those
foundations, not an axiom-free foundational theory.
