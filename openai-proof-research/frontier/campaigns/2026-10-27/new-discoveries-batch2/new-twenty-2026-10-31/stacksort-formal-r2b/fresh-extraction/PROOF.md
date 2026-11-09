# Exact seeds lane 2B: proved content and open bridge

This packet is partial and is not self-accepted. It does not prove
`exactSeeds20_proved : ExactSeeds20`.

The frozen round-1 sources are imported unchanged. Their literal `P n` counts all
pairs of permutation words of [0,n) with equal max-split output. No declaration
from round 1 is renamed, shadowed or edited.

`StackSortSeeds2Words` proves inverse maximum splitting and reconstruction,
injectivity of root insertion, the source sorting equation on inserted roots,
and equivalence of root collisions with collisions of concatenated sorted children.
Its `childrenEquiv` is an actual equivalence between two ordered children (either
may be empty) and the disjoint alternatives leaf, unary with a Boolean left/right
choice, and binary with two nonempty words. These alternatives give 1, 2, 1.
This is the word-level T3 ingredient, not the complete counted tuple deletion identity.

`StackSortSeeds2Tuples` enumerates all decompositions of each permutation word into
r nonempty consecutive words. The enumerator uses explicit structural `Nat.rec`.
`mem_sections` proves exact membership, with no restrictions besides length,
concatenation and nonempty words. `XI_one` proves XI(M,1,1)=P(M) for M>0.

`StackSortSeeds2Maximum` proves T2. Sorting each word preserves its multiset.
A global maximum terminates the sorted word containing it, so its output position
is a tuple boundary. In a collision the position agrees in both tuples. If it is
not final, it is a forbidden common internal boundary. The resulting theorem is
`irreducible_maximum_last`, expressed as idxOf(max)+1=output.length.

`StackSortSeeds2Recursion` gives the top-max recurrence, its dependency congruence,
and uniqueness by strong induction in M. The recurrence is only used for the
pruned domain r,s<=min(M,21-M). Values outside it are zero; these clipped values
are not asserted to equal the unrestricted literal tuple count. M=0 has X(0,0,0)=1.
The dependency induction is a proof, not a kernel-evaluated well-founded program.

`StackSortSeeds2Data`, the twenty `StackSortSeeds2RowNN` modules and
`StackSortSeeds2Checked` kernel-check a literal table against the recurrence.
Independent reduction proofs are split by the first tuple index to stay within
-M3500. The table contains 20 exact numerical seeds matching the frozen seed20.
This is a proved arithmetic recurrence certificate, not a combinatorial count theorem.

The final module defines literal II by filtering the finite tuple-pair domain
for collisions with no common internal boundary. It clips XI and II to the exact
pruned support. `AdditiveRecursion` is the precise remaining proposition:

    II + sum_b choose(M-1,b-1) conv(XI,II) = deletion(XI)
    XI = II + sum_b choose(M,b) conv(XI,II)

for positive indices in the pruned support. Both equations are additive natural
identities, so no nonnegativity of a subtracted count is assumed silently.
`literal_recursion_of_additive` derives the executable recurrence from these
identities. `exactSeeds20_of_additiveRecursion` then proves ExactSeeds20 with
exactly this explicit argument. `exactSeeds4` is unconditional.

Remaining work: prove the common-cut decomposition, labelled subset shuffle count,
and tuple-level maximum deletion bijection with its arity weights. Combine these
with the proved T2 to discharge AdditiveRecursion. This requires actual finite
bijections and standardisation of arbitrary subsets, not another numerical check.
No work on DoublingInjection, RootSplit or the lower130 linkage was undertaken.

`StackSortSeeds2Domain` additionally characterizes tuple membership as exactly a
permutation concatenation, the specified tuple length, and nonempty words. It
specializes T2 to the actual tuple domain with maximum M in [0,M+1), giving final
position M+1. This avoids leaving a separate fidelity bridge for T2's hypotheses.

Concrete next-round sequence:

1. Construct the order-preserving relabelling of [0,k) onto an arbitrary k-element
   subset and connect it to the frozen global order-embedding theorem.
2. Choose the last proper common output boundary. Prove its prefix/suffix
   decomposition is unique and its suffix is irreducible. This gives the
   convolution with choose(M,b) after counting the suffix label subset.
3. Repeat with the maximum constrained to the last output position. T2 forces
   the last irreducible block to contain it, changing the subset factor to
   choose(M-1,b-1).
4. Prove that maximum-final output places the maximum in each tuple's last
   word. Apply rootParts/rootWord and childrenEquiv there. Establish the exact
   finite bijection and count its nine arity pairs with weights mu(t)mu(u).
5. Derive the two additive identities for the unpruned counts, then show pruning
   removes only impossible dependency terms. Supply AdditiveRecursion to the
   existing conditional endpoint. No new numerical algorithm is needed.
