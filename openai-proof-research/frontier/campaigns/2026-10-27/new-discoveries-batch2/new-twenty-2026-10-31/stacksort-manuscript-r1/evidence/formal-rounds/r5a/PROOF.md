# Round 5A proof

The requested common-cut identity is proved without hypotheses in StackSort.Cut5.commonCutCount_proved. This is an implementation packet, not acceptance. The parallel MaximumFinalCount obligation is untouched.

For a tuple F, support F is the finite set of letters in its flattened word. A tuple belongs to labelledTuples A r precisely when its flattening is a permutation of the sorted list of A, it has length r, and its words are nonempty. The new labelled_split theorem retains both pieces, proves their supports disjoint, and identifies the prefix support as the complement of the suffix support. labelled_append proves the converse. Equal sorted outputs imply equal supports by output_perm.

The finite pieces family is indexed by (b,a,c,A): 1 ≤ b < M, 1 ≤ a < r, 1 ≤ c < s, A ⊆ range M, and |A|=b. Its fibre is the product of labelledPairs (range M minus A) (r-a) (s-c) and labelledIrreducibles A a c. glue concatenates the respective tuple components.

The prefix has a positive output length because r-a is positive and its words are nonempty. The final block has positive output length b. Thus their concatenation has a proper internal common cut and is a reducible collision. For injectivity, the frozen irreducible_suffix_unique theorem recovers all four tuples. Their lengths recover a and c; the suffix support recovers A; its cardinality recovers b. This proves equality of the fully tagged sigma elements, not just equality of their unlabelled images.

For surjectivity, take the frozen FinalBlock of an arbitrary reducible collision. Its prefix cannot be empty: collision of the prefixes would make both empty and finalBlock_irreducible_iff would make the original collision irreducible. The block has positive length by its structure. labelled_split on both sides and support_collision identify the two common label sets. These facts supply all the strict index bounds and exact labelled family memberships. Concatenation reconstructs the original pair.

The finite bijection gives pieces_card. XI_partition splits the complete family into irreducibles and their complement. Summing fibre cardinalities using the frozen labelledPairs_card and labelledIrreducibles_card gives choose(M,b) times XI(M-b,r-a,s-c) times II(b,a,c). This proves commonCutCount_raw for every M>0 and arbitrary arities, before pruning.

Clipping requires care only for impossible arities. A tuple of nonempty words has at least as many letters as words. Therefore tuples M r is empty for r>M, so both XI and II vanish whenever either arity exceeds M. On positive indices bounded by 21-M, the literalX and literalI definitions consequently equal XI and II even when the size bound fails. If r,s ≤ bound M, every common-cut dependency has positive arities, and both a,c at size b and r-a,s-c at size M-b remain below the respective 21-size bounds. correction_eq_raw therefore identifies the frozen correction false exactly with the unrestricted sum. Substitution into commonCutCount_raw closes the target.

The proof does not compute any new seed. It neither assumes nor proves MaximumFinalCount. Combining this lane with a future proof of that frozen Prop will discharge AdditiveRecursion using the inherited additiveRecursion_of_counts theorem. The source-reading endpoints remain conditional on that other lane; this packet does not self-accept them.
