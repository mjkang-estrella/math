# Local formal and mathematical audit

This is a self-audit by the implementing research agent, not an independent review. Date: 2026-10-25.

## MathDB362146

`PermutationSpectrum.lean` contains four definitions and sixteen theorems. All twenty declarations are compiled and listed with their full types and kernel axiom dependencies in `formal/build/Checks.log`. The final declarations are `main_conjecture` and `exact_mathdb_conclusion`. Their hypotheses are only a field, finite index type with decidable equality, and the exact one-unit-per-column predicate. Their conclusions use mathlib's eigenvalue predicate, not a substitute spectral assumption.

Definition checks:

- `IsPermutationLike` requires a 1 in each column and zero at all distinct row indices. Since a field is nontrivial, the 1 is unique and every entry is zero or one.
- `IsPermutationMatrix` adds the same property on the transpose, meaning one 1 per row as well.
- `IsEigenvalue` is nonzero vector existence plus the ordinary matrix-vector equation. `isEigenvalue_iff_library` formally bridges it to `Module.End.HasEigenvalue A.toLin' μ`.
- A root of unity is stated explicitly as `∃ k : ℕ, 0 < k ∧ μ ^ k = 1`; no primitivity or characteristic-zero assumption is hidden.

Proof checks:

- The finite pigeonhole step is on functions from the finite index type to itself, never on the generally infinite matrix field.
- The composition formula is proved entrywise before being used for matrix powers.
- The two unequal exponents are ordered explicitly, ensuring q−p>0.
- Cancellation uses both μ≠0 and a nonzero coordinate of the eigenvector.
- A collision supplies e_i−e_j. This remains nonzero in characteristic two, because its i-coordinate is 1 when i≠j.
- Injectivity implies bijectivity only because the index type is finite. The constructed inverse is checked by the same composition formula.
- The identity inclusion is proved. The source's redundant exclusion of identity is present in the final theorem.
- Empty and singleton index types cause no proof gap; the theorem is stronger than the source's d>1 restriction.

No spectral classification, Jordan decomposition, characteristic-polynomial assertion or multiplicity statement is claimed.

## MathDB340783

`Discrepancy.lean` contains nine definitions and twenty-one theorems. All thirty declarations are compiled and listed with types and axioms. The proof establishes nonzero and entrywise strictly positive witnesses, row/column squared-energy equality, the actual arithmetic means, and failure of the stated strict tolerance. It proves the negation of the all-dimensional exact-balance universal implication, and then an all-tolerance witness family.

The source's undefined approximate comparison is exposed rather than quietly identified with equality. The theorem `every_reflexive_interpretation_counterexample` quantifies over a relation R and assumes only `∀ x, R x x`. The energy comparison relation and discrepancy tolerance are separate. It therefore refutes propagation under any reflexive interpretation of approximate energy balance. `BalancedWithin` supplies an explicit numerical version as well. No theorem claims to formalize an undefined nonreflexive relation.

## Build and evidence

Both build scripts verify the supplied Lean version, pinned dependency Git revisions, tracked-source cleanliness and manifest agreement. They erase prior local module outputs and the prior success receipt, build in a fresh local output path, and keep the source directory off `LEAN_PATH`. Thus a stale source-adjacent object cannot satisfy the import. They run with warnings as errors, verify complete declaration/type/axiom coverage, and reject proof holes, custom axioms and native evaluation shortcuts.

The only observed kernel axioms are `propext`, `Classical.choice` and `Quot.sound`. The installed Lean compiler and compatible precompiled library objects remain trusted. Git checks of sources do not authenticate the history of compiled objects, and this work does not claim such authentication or rebuild shared dependencies.

Separate rational diagnostics check four scales of the balanced witness and all 288 functions on sets of sizes 1 through 4. A deliberate change to a witness entry fails the energy-equality check. These tests are supporting evidence only; the universal conclusions are Lean theorems.

## Count and provenance

Two questions, not fifty outcomes. The permutation spectral argument completes the all-dimensional assertion but repeats the source's already-known zero-eigenvalue criterion. The balance witness and scaling argument were already posted by Shivam Patel and are explicitly credited. No global priority is claimed. No independent agent review, parent acceptance, submission, or generated paper PDF is asserted.
