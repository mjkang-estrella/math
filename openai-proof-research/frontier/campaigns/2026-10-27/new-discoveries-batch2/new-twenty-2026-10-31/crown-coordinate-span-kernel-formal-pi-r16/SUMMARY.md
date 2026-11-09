# SUMMARY — crown-coordinate-span-kernel-formal-pi-r16

Auxiliary MathDB 369163 formalization step. Credit 0; 52/60 campaign status unchanged.

Executed:
1. verify_frozen before: 820/820.
2. src/CrownVCoordSpanKernel.lean — strict compiled (receipt 1794001212035007769, EXIT=0,
   warningAsError clean). Single theorem `CrownV.coordSpan_le_ker`:
   `Ideal.span (coordGens T : Set (PolyRing n K)) ≤ RingHom.ker (coordKill (n:=n) (K:=K) T)`
   for arbitrary `n`, `K : Type*` `[CommRing K]`, `T : Finset (V n)`; K pinned; existing
   definitions and the sealed annihilation lemmas reused verbatim. Per the r15 scope
   correction the kernel side is `Ideal.span (coordGens T)`, NOT general `Pc(T)`.
3. Sealed hashes: source 754af6ea8ef0ac8d17f17b7b41d9d5feda572a2e562ba723d8a570550605ab32,
   olean 2898ba03f51aadfe93d6168f6ef2f202178310e16efa671895d527eb8a603d5f,
   log 5391d0c7e7cd86f7b91028e6e770ae308470833b07275c0b1b28a34f575f46cf.
4. Scoped axiom audit: `#print axioms CrownV.coordSpan_le_ker` →
   `[propext, Classical.choice, Quot.sound]` exactly (receipt 1794001385019952002, EXIT=0).
5. leanchecker kernel recheck of the sealed olean (receipt 1794001400801494419, EXIT=0,
   pinned toolchain PATH); source/olean hashes re-verified MATCH after the checker ran.
6. verify_frozen after: 820/820 (frozen-after.json).

Exclusions (unpaid): reverse inclusion/equality, primality, fullside, families, degree
analysis, deep audits, negative controls, fresh extracted replay, reviews, paper,
acceptance. Helper status: earns 0 credit by task definition.
