# Scoped formal support

Independent formal review is pending. Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 compile 22 support theorems and 13 control theorems; all 43 public declaration types and transitive axioms are recorded. The source interfaces are:

- Recursive words, first-difference edge labels and the head-constant predicate; tournament indegree counting, actual fiber induction and cardinality at most 3^h, hence less than 82 at h=4. The base relation is assumed irreflexive and total on distinct elements.
- Affine differences and preservation of a specified first differing coordinate; row-position maps on function-valued vectors and a subgroup of field units, with injectivity, transitivity, composition, identity and left inverse.
- Conditional finite-depth real scalar recurrence estimates, normalization implications, and strict depth-20 seed arithmetic.

Lean does not identify the base relation with Paley squares, identify recursive words with function vectors, or formalize the nested Boolean predicates, their ordinary/joint sensitivity recurrences, the raw-bit permutation action, prime existence/rounding, disjoint zero blocks, OR balancing, composition, asymptotic ratio or logarithmic exponent. Those remain prose proofs. The recurrence hypotheses are explicit and are not silently treated as formally derived Boolean profiles.

The implementation reports six genuine proof-goal rejection controls and an actual zero-exit printed-failure runner control. Independent reproduction is under way. Compiler, standard library and previously compiled dependency objects remain trust boundaries; fresh task-source compilation is not a source-to-binary audit of the entire toolchain. The exact final review and its limits will be retained when available.
