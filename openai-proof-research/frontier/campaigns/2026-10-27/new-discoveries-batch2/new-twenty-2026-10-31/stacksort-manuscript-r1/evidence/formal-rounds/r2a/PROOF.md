# Proofs and exact remaining work

The fixed-label injection sends two equal-output pairs (L,L') and (R,R') to
(L m shift(R), L' m shift(R')), with m=a+b and shift(x)=a+x. Its membership proof permutes the root to the final position, combines the two range permutations, and uses range(a+b)=range(a)++map(a+·)(range(b)). The source split equation and proved standardisation establish equal sorted outputs. Maximum split recovers each left word and shifted right word; injectivity of shift recovers the original right words. Finset.card_le_card_of_injOn yields P(a)P(b)≤P(a+b+1). It does not yield the missing choose factor.

The end-family injection takes a pair of Bool choices and an equal-output pair on n letters. Each Bool independently places n at the front or back of one word. The sorted output is always s(w)++[n]. For n>0, a word with n at the front cannot equal an old permutation followed by n, since the old permutation is nonempty and its first letter is <n. Hence all four families are disjoint. This gives the entire 4P(n) term, but not the interior terms in RootSplit.

For factorial conversion, choose(2a,a)*(a!)²=(2a)! and (2a+1)!=(2a+1)*(2a)!. Cast the integer injection inequality to R, multiply by the positive factorial square, and clear the positive denominators. This proves Doubling from DoublingInjection; no combinatorial assumption is hidden.

lowerFold k is a structural Nat.rec storing the first k values in a function. G(n)=lowerFold(n+1)(n). A stored index below k is unchanged by the next stage. Induction gives lowerFold k i=G i for i<k. Thus G(n)=seed20[n]! for n≤20 and G(n)=rootRhs G n for n>20. This holds for all n, not only through 130. Every recurrence index is strictly smaller than n. Products and finite sums of naturals are monotone, so strong induction using RootSplit and ExactSeeds20 proves G(n)≤P(n) for every n. The n=0 case uses the frozen theorem P_zero, since ExactSeeds20 only starts at 1.

The numeric table is generated independently with Python integers, but Python is not trusted for the proof. Each of its 110 non-seed rows is proved by `decide` in Lean, using factorial quotients for binomials to avoid exponential Pascal reduction. A general theorem identifies that executable RHS with rootRhs. All 21 seed table entries are also kernel checked against the frozen seed20 list. Strong induction proves G agrees with this table through 130. The final table entry is definitionally lower130. Consequently RootSplit and ExactSeeds20 imply Lower130.

## Remaining Props, unchanged from round 1

`DoublingInjection := ∀ a : ℕ, Nat.choose (2*a) a * P a ^ 2 ≤ P (2*a+1)`.

`RootSplit := ∀ n : ℕ, 2 ≤ n → 4*P(n-1) + ∑ i ∈ Finset.Icc 1 (n-2), Nat.choose (n-1) i * P i * P(n-1-i) ≤ P n`.

`ExactSeeds20 := ∀ n : ℕ, 1 ≤ n → n ≤ 20 → P n = seed20[n]!` is reserved to lane 2B.

No new residual Prop definition is needed. None of these three Props is proved by this lane. Doubling and Lower130 are now consequences of these Props rather than independent numerical/analytic obligations.

## Next round

Generalize the fixed-label construction from contiguous ranges to arbitrary complementary finite subsets. Establish the standardized-word equivalence for each subset, count subsets of cardinality i by choose(n-1,i), and recover the subset from the left word. Sum the disjoint equal-left-size families. For doubling, use i=a in size 2a+1. For RootSplit, use every i=0..n-1 and adjoin the two cross-end families already proved disjoint. Then instantiate doubling_of_injection and lower130_of_seeds. Merge only the theorem ExactSeeds20 from lane 2B; do not alter any frozen declaration.
