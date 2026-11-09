# Sustained route 381870

The actual source definition (Section3.3) is combinatorial, despite the cohomological title. With the centered highest weight a=(a₁,...,aₙ), C' is the largest Coxeter length q for which every permutation of length exactly q has all proper prefix sums positive. The conjecture says C'=min(number of strictly positive coordinates, number of strictly negative coordinates)-1. Zero coordinates are counted in neither side. The entries are strictly decreasing since the highest weight is weakly decreasing and rho drops by one.

The endpoint obstruction is immediate: moving the first nonpositive entry to the first position or the last nonnegative entry to the last position gives the upper bound in the conjecture. The lower bound requires control of EVERY interior prefix, and that is where an unproved bridge remains.

For a k-element subset S={s₁<...<sₖ}, the smallest inversion cost to bring it into the first k positions is c(S)=sum(sⱼ-j). Thus a sufficient purely combinatorial lemma is:

For every strictly decreasing real vector a with sum zero, with r positive and t negative entries, every nonempty proper subset S satisfying c(S)<min(r,t) has sum_{i in S}aᵢ>0.

This lemma was not proved. One cannot silently replace strict ordering by weak ordering: a=(3,3,3,-3,-3,-3), S={1,4} has cost2<3 and zero sum. The source's strict rho gaps are therefore material. The lemma's validity for every strictly decreasing vector is stronger than the source weight family and is not asserted here. A possible route is to express decreasing centered vectors as nonnegative combinations of centered step vectors, keeping enough strictness to rule out equality; the relevant subset-cost inequality is still needed.

Exact search coverage: source bipartitions of size at most4 EACH, admissible total length<=n, n2..6; all n! permutations, evaluated on exact integer weights multiplied by2n; literal maximum of good exact-length layers, not a substituted first-failure definition. Coverage is in outputs/weyl-small.json. No discrepancies. No Lean claim or credit.
