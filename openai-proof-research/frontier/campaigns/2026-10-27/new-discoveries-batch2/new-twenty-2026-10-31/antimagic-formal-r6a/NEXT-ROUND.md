# Exact next work

Do not repeat nonbinary construction work. Round6A.nonbinaryHigherConstruction
is unconditional and includes the frozen formula realization. Its axioms are
only propext, Classical.choice and Quot.sound.

BinaryHigherConstruction is still the original Prop in AntimagicFinal3.lean.
The new binary lemmas are helpers, not a substitute for this Prop.

1. Use binary_internal_injective and binary_internal_exists to build the
internalMap permutation on InternalVertex 2 n, following Antimagic5AVertices.
The binary_internal_range lemma covers rows >= 2; row one is {Z,N}.
2. Generalize the parent-derived tuple proof using
internalLabel 2 n (n-1) i = shellEntry Z (patchedIndex 2 (n-1) i).
The inherited tupleParameter_range/injective/cancel lemmas already apply;
compose with patchedIndex_row_bound/involutive. This handles n=3 explicitly
without pretending the patch is absent on the last internal row.
3. Reuse leafEntry_range, leafEntry_injective, leafEntry_sum and largeLabel_leaf
at s=1: these inherited lemmas require only 1 <= s. The round-5A wrappers
leaf_formula, parentParameter_range and the labeling themselves have hs>=2,
so they cannot simply be instantiated at s=1. Prove new wrappers.
4. Combine the internal and leaf permutations into the literal edge equivalence,
retaining higherLabeling_label-style formula equality. The lower incidence
bridge and generic finite-certificate bridge are inherited unchanged.
5. For rows >=2 with children still internal, the patch is absent at child rows
>=3, so the children sum is 2Z. For last parents, use tuple cancellation on
the patched parent index. binary_root_weight and binary_first_weight already
give the exceptional literal weights for any formula realization.
6. Finish adjacency: root separation is done; first row versus second row at
n>=4 uses binary_row_two and Z>=7; n=3 meets the last-parent constant.
All lower middle comparisons use binary_internal_injective. Place all other
weights in the high leaf band and apply lowerBound for exact colour count.
7. Only if BinaryHigherConstruction closes, verify round-4B source.zip hash
01116203a1ed83a81c90684ceb468113f0b4648104446fa3603dd24ce4c933ce,
copy its two bridge/final modules byte-identically, and add the requested
unconditional merged endpoint. No round-4B files were copied in this round.

Preserve the original 37 module hashes. A future round should freeze the entire
round-6A source.zip anew and work in its own lane. Root alone decides acceptance.
