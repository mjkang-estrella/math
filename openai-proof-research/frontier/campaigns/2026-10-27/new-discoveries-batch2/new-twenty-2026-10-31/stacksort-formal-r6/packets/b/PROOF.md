# Round 5B proof content and remaining work

This is an implementation packet, not acceptance. The requested unconditional theorem `maximumFinalCount_proved : StackSort.Round3.MaximumFinalCount` is not closed and is not declared. No work on CommonCutCount was undertaken.

The new deletion construction acts on all maximum-final collisions. Deletion does not preserve irreducibility, so a direct equivalence between irreducible collisions and arbitrary reduced collisions would be false. The frozen correction true term accounts for the reducible maximum-final pairs.

`StackSortDel5Core` proves that replacing the final maximum-root word by its nonempty children changes the literal label set from range (m+1) to range m, in both directions. This uses an actual list permutation moving the maximum to the head and cancelling it; it includes the empty reduced tuple. The tuple lengths have exactly the required shift. Literal reduced membership supplies strict upper bounds on every child label, so the frozen output cancellation theorem applies without additional label assumptions.

`StackSortDel5Inverse` defines the finite set childChoices F of all oriented roots with childrenTuple equal to a specified suffix F. Membership is equivalent to that equality. For a suffix of at most two nonempty words its cardinality is mu F.length, hence 1, 2, 1. The two unary orientations are distinct constructors. The final t reduced words are recovered using drop k, and the prefix using take k; their concatenation is the original reduced tuple. The prefix/suffix split is unique for a fixed prefix length.

`StackSortDel5Representation` proves every maximum-final literal tuple has such a representation, by locating the maximum in the last word and applying rootParts. Conversely every literal reduced representation reconstructs a maximum-final tuple. Insertion recovers the prefix and both oriented children uniquely: the original tuple fixes its last word and prefix, and rootParts recovers the two ordered child words.

`StackSortDel5Bijection` packages this as the actual equivalence deletionEquiv between ReducedPairs m r s and MaximumPairs m r s. ReducedPairs retains the two literal prefixes and Children constructors, with exact lengths, literal reduced membership, and the reduced output collision. MaximumPairs consists of literal tuple pairs on range (m+1), with the prescribed arities, collision, and final maximum position. No counting assumption is used in this equivalence.

`StackSortDel5Bounds` proves literal tuple support, handles size zero exactly, and identifies literalX with raw XI throughout the retained diagonal r,s <= 21-M. It follows that deletion literalX equals deletion XI at every supported positive input. The positivity hypotheses are needed: at r=0 the shift r-1+t is truncated and the claimed diagonal bound would fail at the upper end.

`StackSortDel5Final` proves equality of Nat.card for the two domains, and provides the endpoint conditional on two explicit ordinary Prop definitions:

1. FixedMaximumDecomposition: the card of MaximumPairs (M-1) r s equals literalI M r s plus correction true literalX literalI M r s.
2. TaggedDeletionCount: the card of ReducedPairs (M-1) r s equals deletion XI M r s.

These are not added axioms. The conditional theorem is maximumFinalCount_of_bridges. Neither remaining Prop is asserted unconditionally.

Next round: enumerate ReducedPairs by child arities t,u and reduced tuple pairs, using take (r-1), drop (r-1), childChoices, and their product cardinality. Prove disjointness by arity and insertion_injective, and sum using XI; deletion_eq_raw already removes clipping. Separately use the frozen last-proper-common-cut decomposition on MaximumPairs, restricting the suffix label subset to contain the maximum. The required shuffle factor is choose (M-1) (b-1); recover the subset from the literal suffix labels and use uniqueness of FinalBlock. This is the fixed-maximum count, not a proof of CommonCutCount. Then apply maximumFinalCount_of_bridges to obtain the requested unconditional endpoint.
