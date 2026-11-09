# Round 4 proof content and remaining construction

This is partial implementation, not acceptance. The unrestricted equations CommonCutCount and MaximumFinalCount remain the exact ordinary Lean Prop definitions from frozen StackSortSeeds3. No substitute counting assumption or new environment axiom is introduced.

## Last common cut

A tuple has nonempty words. Therefore a nonempty segment of the tuple has positive output length, since sorting preserves the word multiset. If A++B=C++D and the output prefixes have equal lengths, the list append comparison writes one prefix as the other followed by E. Equal output lengths force E to be empty. This proves split_unique without any distinct-label assumption.

The common boundaries below the total output length form a finite set containing zero. Its maximum is the last proper common cut. Split both tuples there. Equal full outputs and equal prefix lengths imply equal prefix outputs and equal suffix outputs. Any positive internal common boundary of the suffix would lift to a larger proper common boundary of the full tuples, a contradiction.

Conversely, any irreducible suffix starts at the last proper common cut: a larger common boundary would descend to an internal boundary of that suffix. Consequently two final-block decompositions have equal starting positions. split_unique then proves all four component tuples equal. The structure FinalBlock records the actual four tuples and their properties; finalBlock_exists and finalBlock_subsingleton establish existence and uniqueness. finalBlock_irreducible_iff identifies the whole-pair irreducible case with empty prefix tuples.

The convolution in the frozen recurrence uses X(M-b,r-a,s-c) times I(b,a,c). Thus these lemmas deliberately use an arbitrary prefix and an irreducible final block. A first-block version is possible, but the final-block version matches the maximum-constrained correction directly.

## Literal labelled domain

sections_map is proved by structural induction on the section count. The take/drop operations commute with mapping, so every labelled section comes from an unlabelled section; this is not only preservation. Combining this with round 3's exact labelWords image proves labelledTuples_eq_image. Collisions and irreducibility are preserved and reflected by the inherited order-embedding invariance. Thus labelledPairs_card and labelledIrreducibles_card identify prescribed-label counts with the literal XI and II counts, including all degenerate indices.

These lemmas close the separate tuple-standardization surjectivity gap listed in the round-3 results. They do not yet identify concatenated labelled families with the entire reducible tuple-pair domain.

## Maximum and deletion

The maximum terminates the sorted word containing it. Splitting the tuple around that word expresses its common output as prefix ++ maximum :: suffix. Nodup excludes an earlier occurrence of the maximum. If the maximum's index plus one is the total length, the suffix output has length zero. Nonempty tuple words force that suffix tuple to be empty. This proves maximum_in_last_word, and inherited T2 supplies its hypotheses for both sides of literal irreducible collisions.

childrenTuple drops empty children and retains the nonempty children in order. Its length is childrenArity, which is 0, 1 or 2. The inherited Children type retains the Boolean choice in the unary case, so it retains the multiplicity two. delete_last_output proves that a tuple with its last maximum-root word sorts to the reduced tuple output followed by that maximum. Cancellation gives delete_last_collision_iff. delete_last_length gives r-1+t exactly.

Deletion does not in general preserve irreducibility: for example, deleting the maximum from a single binary-root word can leave two words on both sides with a common boundary. The correct object counted by deletion is all maximum-final collisions. It is this cardinality that must be equated with II plus the fixed-maximum common-cut correction. No theorem here asserts an irreducible-to-arbitrary-reduced-pair bijection.

## Still required

1. Define the finite disjoint union indexed by suffix size b, suffix tuple lengths a,c, and the suffix label subset A. The prefix and suffix families are now literal via StackSortLabels4. Concatenate their two components. Use irreducible_suffix_unique to recover both parts, then recover A as the suffix's flattened label set. Prove surjectivity using finalBlock_exists and membership/label-partition lemmas. Sum cards with tupleShuffle_card and reindex to correction false.
2. Repeat the same decomposition for the maximum-final subfamily. T2 puts the maximum in the irreducible suffix; the prescribed label condition produces choose(M-1,b-1) using fixedTupleShuffle_card.
3. Construct the finite arity-tagged deletion bijection on all maximum-final pairs. The last-word location, collision equation and length equation are now available. Still prove exact reduced tuple membership, inverse reconstruction from the last t words, and the nine arity-pair cardinalities with unary Boolean choices.
4. Prove clipping compatibility: terms exceeding a size bound vanish by impossibility, while the 21-M bound retains all dependencies of supported indices. Then close commonCutCount_proved and maximumFinalCount_proved, in that order, and supply both to additiveRecursion_of_counts. Only then add the requested unconditional seeds, lower bound and source endpoints.

No new numerical seed evaluation is necessary. The packet does not claim the missing bijections or either general counting identity.
