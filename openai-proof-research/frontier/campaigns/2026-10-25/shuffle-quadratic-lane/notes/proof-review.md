# Mathematical and formal self-review

The implementing agent performed this review. An independent parent/reviewer should inspect it before counting a campaign outcome.

1. Quantifiers: the matrix equation is proved for all natural n (empty matrix included). Nonzeroness and the eigenpair are proved for every n>=3. No unproved equation or moment is an input hypothesis.
2. The scalar field is real and vector entries use real division by 2. Binomial coefficients are the mathlib natural `Nat.choose`, cast to reals.
3. Pascal induction is generalized over all real quadratic coefficients. The exact transformation is `(a,b,c) -> (2a,2a+2b,a+b+2c)`. Base rank zero is included.
4. Terms above the binomial support are removed using `Nat.choose_eq_zero_of_lt`; `r<n` is discharged by the finite row's bound.
5. The reflected term is reindexed by `Finset.sum_range_reflect`. The arithmetic identity `k+1+(n-1-k)=n` is proved under `k<n` before converting it to real arithmetic.
6. The division by `2^(r+1)` uses a nonzero real power. The proof contains the full finite row sum and the sum-to-`Fin n` conversion.
7. `v1=(n-1)(n-2)>0` proves nonzeroness. This excludes the zero-vector artifact at sizes one and two.
8. `Module.End.HasEigenvector` includes both eigenspace membership and nonzeroness. `quarter_hasEigenvalue` and `quarter_eigenspace_dimension` provide standard spectral consequences.
9. One-based indexing theorems establish exact agreement with the paper's formulas, including natural subtractions at both ends of the deck.
10. Universal algebra is kernel-checked. The only reported axioms are propext, Classical.choice, and Quot.sound. No custom axiom, admitted proof, or native decision procedure is used.

## Evidence

`build/audit.json` is a fresh isolated build receipt; `build/Checks.log` prints the types and axiom dependencies of all 16 declarations. `formal/Checks.lean` is the corresponding check source. `build/exact-check.json` records independent rational computations for n=1..80 and complete bottom-draw coin enumeration for n=1..10. `build/mutation-check.json` and the per-mutation logs show that changing the eigenvalue to 1/8, shifting the denominator exponent, or extending nonzeroness to n=2 is rejected by Lean.

The exact arithmetic and negative controls strengthen source/implementation alignment but are not universal proofs. No independent external human/agent review is represented as completed. No remaining formal proof gap is known for the stated target. The paper is supplied as LaTeX source; no PDF build is claimed.
