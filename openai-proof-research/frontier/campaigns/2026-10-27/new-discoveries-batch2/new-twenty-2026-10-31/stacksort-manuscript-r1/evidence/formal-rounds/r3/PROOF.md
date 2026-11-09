# Proof content

The finite-set label function uses the increasing enumeration below A.card, then a strictly increasing tail above A.sup id. Its strict monotonicity is proved by the four cases relative to A.card. Mapping range(A.card) is exactly A.sort, by equality of list entries. Commutation of mapping with the complete permutation enumerator proves that labelWords A is exactly the image of words(A.card), not a restricted family. The frozen order-equivariance theorem proves preservation of collisions; injectivity of list mapping proves reflection. Therefore labelPairs A has cardinal P(A.card).

shuffleDomain n i is the dependent finite union over every i-element subset A of range n of labelPairs A times labelPairs(range n minus A). Finset.card_sigma, complementary cardinality and card_powersetCard give choose(n,i) P(i) P(n-i), including empty blocks.

Root insertion maps its four words to (L n R,L' n R'). The two sides use complementary label sets, so every image is a literal permutation word. The frozen split equation proves collision preservation. Maximum splitting recovers L,R,L',R'. The finite set of L recovers A, proving injectivity even across distinct label subsets.

For RootSplit, the image families at i=1 through n-1 have distinct maximum-left lengths i. Hence their union has the sum of their choose-weighted cardinalities. The four independent end-choice families have cardinal 4 P(n). Their maximum-left lengths are 0 or n, disjoint from every interior family. The union embeds in the literal collision finset at n+1. Reindexing gives exactly frozen RootSplit. This is stronger than separately proving each summand is bounded by P(n+1).

For DoublingInjection, specialize choose_split_bound to n=2a and i=a. The already-proved factorial cancellation doubling_of_injection then yields Doubling. Both are unconditional.

The tuple extension proves output commutation for any increasing relabelling, reflection of collisions, reflection of boundaries via List.map_eq_append_iff, and invariance of irreducibility. For arbitrary finite standardized tuple-pair families F,G, tupleShuffle_card gives choose(n,i) card(F) card(G). Requiring a prescribed set S of labels in the chosen block changes the coefficient to choose(n-card(S),i-card(S)). Taking S to be the singleton maximum gives the desired fixed-maximum binomial coefficient. These are finite family bijections/counts, not a proof of how every tuple collision decomposes into such families.

# Remaining proof work

CommonCutCount is the exact common-cut convolution identity on the clipped literal XI/II domain. MaximumFinalCount is the exact identity equating the maximum-final block decomposition with deletion, using the 1,2,1 arity weights. StackSortSeeds3 proves their conjunction equivalent to the inherited AdditiveRecursion. Both identities remain unproved.

Next: choose the last internal common boundary; prove uniqueness of the prefix and irreducible suffix and recover their label sets. Use tupleShuffle_card for unconstrained labels and fixedTupleShuffle_card for the singleton maximum. Then lift childrenEquiv to the last words of literal tuples, proving the full counted deletion bijection with nine arity pairs. Establish clipping compatibility with the existing bound. This supplies AdditiveRecursion, at which point all four source endpoints in StackSortFinal3 lose their final hypothesis.

No additional arithmetic table computation is needed. No unconditional source refutation, exact seed identification through 20 or Lower130 is claimed in this packet.
