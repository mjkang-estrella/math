# Proof notes for the certified components

All conclusions below refer literally to Concentration.lean, rather than the source's more general cell relation.

For arbitrary R and selection E, list induction shows the expanded length is the original length plus the sum of membership indicators over range R.length: selected positions contribute two instead of one. If finite T is contained in markedSlots, marked_lt puts T in that range, and the indicator sum is T.card. This includes empty R and empty T.

Induct on actual Executes a R c to bound slotB. At a marked head, marked_zero gives C2 and two copies of index 2. diamond_expand constructs the actual legal S2,C1 path. Consequently the board immediately after S2 has at least the C1 legal move, so its natural legal-type count is at least one. step_value preserves the upper bound value<F(n+1) and legalTypes_le_two_n gives the upper bound 2*n. At a tail mark, step_deterministic identifies the actual next board and the induction hypothesis applies. Taking reciprocals of positive 1+slotB proves the parameter interval. actual_length_bernoulli combines these independently established objects with actual_conditional_bernoulli and actual_cell_mass_pos.

The actual cell is exactly the image of the powerset of markedSlots under expand. expand_injective and Finset.coe_injective justify a sum over that image with no multiplicities. Replacing each actual normalized point weight by actual_conditional_bernoulli and each length by actual_expanded_length proves both pushforwards, for arbitrary test functions. The real version uses the cast of the rational conditional identity, with Rat.cast_div explicit. Summing the lower parameter bound yields sum p >= marks/(2*n+1) >= M/(2*n+1), with positive denominator; multiplication by two proves the real mean lower bound. No independence premise appears in this deduction.

The map compress on actual completeDomain gives a finite fiber decomposition. Each fiber is definitionally cellDomain. A represented R is compress w for a complete actual w, hence is complete and reduced by inherited theorems. Its cell mass is positive. Multiplying each conditional weight by cell mass cancels its actual denominator term by term; this proves the real mixture for arbitrary f. A direct rational fiber sum and P_normalized prove the real cell weights sum to one. Zero-mark cells use the inherited singleton identity and exact ratio one, with no mean denominator.

For finite thinning, fix S and output T subset S. The product factors for selected U indices are (2p_i)*(1/2); their V bit is forced either way. For unselected U indices, the factors are (1-2p_i)*0 if i is in T, otherwise (1-2p_i)*1; in the latter case both fair V outcomes are summed. Finset.prod_add sums these products over ALL U subsets exactly. The resulting coordinate factor is p_i for i in T and p_i+1-2p_i=1-p_i otherwise. Thus this is the full output-vector law, not an argument from matching marginals. Formal statement is algebraic for rational p, with no positivity premise needed for the equality.

The pinned primary library proves Nat.succ_mul_centralBinom_succ from ordinary choose identities; the source file's proof was read. After dividing by 4^l it gives (2l+2)c_(l+1)=(2l+1)c_l. Squaring and using

    (2l+1)^2(l+2) <= (2l+2)^2(l+1)

proves (l+1)c_l^2<=1 by induction, base c_0=1. The difference in that displayed inequality is 3l+2. Even fair-binomial atoms are bounded by c_l by Nat.choose_le_centralBinom, which derives from proved choose_le_middle. For odd rows, Pascal writes each nonzero-index atom as half the sum of two neighboring even-row atoms; the zero-index atom is half the even zero-index atom. Thus both even and odd atoms are <=c_l and nonnegative. Multiplying their squared bound by k+1 proves fairAtom_squared for k=2l and k=2l+1. No central bound or variance formula is assumed.

These proofs do not assemble a Poisson-binomial concentration inequality. The exact remaining proof obligations are listed in SUMMARY.md; no axiom, abstract source bridge, assumed variance, assumed concentration theorem, or generated partial declaration substitutes for them.
