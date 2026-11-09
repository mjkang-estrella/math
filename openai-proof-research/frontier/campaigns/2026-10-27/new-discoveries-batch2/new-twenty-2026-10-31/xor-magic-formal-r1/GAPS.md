# Exact remaining formal gaps

The completed theorems cover only the printed-statement refutation and corrected existence at powers 4 and 5. No theorem asserting corrected existence for every power appears in these sources. No acceptance or credit is claimed.

To reach the binding endpoint, the following must all be proved, rather than introduced as assumptions:

1. A reusable graph seed structure containing literal regularity, connectedness, a bijective F2 label map, complete perfect-matching decompositions of the graph and its complement, and a distinguished cycle in the first two factors whose length is not divisible by 3. The existing finite graph certificates do not certify the matching decompositions or the cycle. The factor JSONs are hashed inputs, not Lean proofs.
2. The F4 representation with a proved bridge from its two F2 coordinates; the affine edge maps; the graph lift; all degree, simplicity and zero-neighborhood-sum identities.
3. The rank / nullity argument producing c in ker B outside im D, including the two injectivity / rank arguments and the strict dimension comparison. No such maps or existence theorem have been formalized.
4. The holonomy connectivity theorem, including the affine subgroup dichotomy, the transitive-translation case and the forbidden fixed section case.
5. Persistence of both matching decompositions and the distinguished cycle under iteration. The four degree-4 / degree-5 base graphs are present, but are not packaged as full lift seeds.
6. The interpolation construction, its zero sums, exact degree d+2k+4j, and connectivity even when a designated matching is replaced. Then the arithmetic coverage lemma and iteration n → n+2.
7. The high-degree complement connectivity theorem and endpoint coverage for powers at least 6. The proved complement identity assumes total label sum zero; a general proof of that total sum for every power at least 2 remains missing. The existing obstruction refutations only need and prove the power-4 total sum.

There is no residual unproved hypothesis in any theorem actually included in the partial packet. The missing main theorem is absent rather than represented by an axiom or a conditional endpoint. The finite decidable certificates and the ordinary proof are insufficient to infer it inside Lean.
