# Round 7A proof

The binary parent coordinate is the round-5A tuple parameter composed with
`patchedIndex 2 (n-1)`. The row patch is an involution, so the inherited shell
coordinate permutation remains a permutation. This includes n = 3: the patch
acts on the last internal row in that case. The tuple displacement identity
cancels the parent label exactly. Specializing the inherited leaf-block
permutation at s = 1 gives the complete leaf row. Internal labels and leaf
labels occupy disjoint intervals, so together they induce a literal edge
labeling realizing the frozen formula.

Put N = internalEdges 2 n, Z = center 2 n, q = 2^(n-1). The inherited binary
identities give N = 2Z and q = Z+1. Every row of children below row 1 and above
the leaves sums to 2Z. Every last parent has color
C = 2N+2q+1+Z, exceeding N+2^n. The root has color 3Z, and the first row has
colors 3Z+1 and 4Z-1. All other middle colors are incomingLabel+2Z.

The root separates from row 1 by Z >= 3. If row 2 is the last parent row,
its color C separates it from row 1. Otherwise its four colors are
2Z+2, 4Z-1, 2Z+1, 4Z-2, respectively. Comparing each with its own parent
uses Z >= 3. Lower middle adjacencies separate by internal-label injectivity;
the last parent color exceeds every other color and every leaf label.

Every color except C lies in the high interval [N+1,N+2^n], all of which is
attained at the leaves. Thus the number of colors is at most 2^n+1.
The inherited lowerBound supplies the reverse inequality. The resulting
BinaryHigherConstruction retains the exact formula-realization clause.

The final merge instantiates round 6A with this binary construction
and the round-4B ModelBridge. The final statements retain all inherited graph,
finiteness, FullTree, parity and depth hypotheses. Root decides acceptance.

Attribution: the symmetric-shell construction and binary patch are from the
reviewed r142 proof. The binary depth-two labeling is source Figure 5; the
nonbinary depth-two construction uses published Lemmas 2.2 and 2.9. The final
claim is published Conjecture 6.1, the even case. No novelty or acceptance is
inferred from numerical diagnostics or kernel checking alone.
