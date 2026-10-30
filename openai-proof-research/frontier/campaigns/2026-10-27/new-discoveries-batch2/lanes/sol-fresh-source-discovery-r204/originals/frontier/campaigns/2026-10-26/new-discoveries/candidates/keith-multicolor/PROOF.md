# Mathematical proof and formal scope

Let a_r count partitions of 325 in the 25×25 box with r distinct sizes. Setting the third color variable to one gives F(x,y)=Σ a_r(1+x+y)^r, literally Keith Theorem 3 and its direct coloring definition.

The unique partition using all 25 sizes is the staircase, so a25=1. If a partition used 24 sizes and omitted b, its present sizes would sum to325−b. At most one extra part is allowed. It would have to have size b, contradicting omission. Thus a24=0. Both statements are proved about actual Nat.Partition objects in PartitionSource.lean.

For each triple 1≤u<v<w≤25 set d=u+w−v. If v≤d, remove u,w from the staircase and add v,d. Otherwise remove d,v and add u,w. The partition has 25 parts, sum325 and 23 distinct sizes. The missing pair and the two extra parts recover the triple: if the smaller missing size is below the smaller extra size, missing sizes are u,w and the smaller extra is v; otherwise extras are u,w and the larger missing size is v. Hence there are at least choose(25,3)=2300 such partitions. The kernel checks each actual multiset and a decoding left inverse. It then proves injectivity and the size of the resulting finite family; no disjointness/counting hypothesis remains.

For a partition with r sizes, its coefficient at (i,j) is choose(r,i)choose(r−i,j). PartitionPolynomial proves this from the literal bivariate polynomial and the binomial theorem. Only the staircase contributes at(20,5), giving53130. Only r24 or25 can contribute at(21,3); r24 is absent, so the result is choose(25,21)choose(4,3)=50600. At(22,1), the 2300 constructed partitions each contribute23, giving at least52900. Other contributions are nonnegative.

These three points are consecutive on the full nonnegative-lattice line y45−2x, x0,...,22. A strict valley cannot occur in a weakly unimodal sequence. PartitionFinal proves the nonunimodality of that exact polynomial cut with no residual premises.

The independent standard-library Python enumerator additionally finds the exact third coefficient63112 by counting all missing/repeated-size cases. That stronger exact value is not needed or claimed as the formal source endpoint; the Lean proof uses the proved lower bound52900. Helpers, individual coefficients and witnesses are not discoveries. The result would be one substantive conjecture refutation after all gates pass.
