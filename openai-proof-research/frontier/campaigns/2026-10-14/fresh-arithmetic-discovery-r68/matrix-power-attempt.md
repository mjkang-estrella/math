# Third route: matrix powers; the two-map compatibility remains unpaid

This is a standard matrix-power/type-reduction idea, not a new nominee. McKenzie1984 pp35–36 explicitly uses matrix powers to reduce type while preserving congruence lattices. The elementary full transformation-monoid generators below are classical. We spell out the attempted unary version to locate the exact remaining issue.

Start with a finite unary algebra (A;f_1,...,f_t), n=|A|. Form a list g_0,...,g_(k-1) containing identity, each f_i, and every constant map A→A; pad so k>=3. On X=A^k take four unary maps:

- C rotates coordinates;
- S interchanges coordinates0 and1;
- D replaces coordinate0 with coordinate1, leaving other coordinates alone;
- U(x)=(g_0(x_0),...,g_(k-1)(x_0)).

C,S,D generate every coordinate-selection map V_h(x)_j=x_(h(j)), since a cycle and a transposition generate all coordinate permutations and conjugates of D identify arbitrary pairs; permutations together with elementary identifications generate every map h of the coordinate set.

The full congruence lattice is exactly {theta^k: theta∈Con(A)}. Here is the complete argument, useful for checking what would be lost by deleting a generator. Given a congruence alpha of X, let theta relate a,b precisely when the constant tuples a^k,b^k are alpha-related. Applying U and a constant coordinate-selection map shows theta is invariant under every f_i. For any x alpha y, selecting coordinate i constantly shows x_i theta y_i, hence alpha⊆theta^k. Conversely, from a^k alpha b^k, apply U. Its outputs contain one matching position with values a,b, and for each c∈A a matching position with values c,c. An arbitrary coordinate-selection map therefore produces any pair differing only in one desired coordinate with values a,b and having arbitrary prescribed common entries elsewhere. Changing coordinates one at a time gives theta^k⊆alpha. All theta^k plainly preserve C,S,D,U.

Thus the full original lattice is preserved with FOUR unary maps. This is not the selected TWO-map full-preservation operation, and is not offered as a weakened substitute.

## Why the naive two-map simplification fails

Keep just C and a single coordinate-identification D (overwriting0 from1) as coordinate-control generators. They cannot produce all coordinate-selection maps. Every word containing D has a nontrivial kernel containing a cyclically adjacent pair (consider the earliest singular factor in the corresponding composed index map; prior factors are powers of the cycle). Therefore any desired selection map with no equal labels on cyclically adjacent coordinates is unavailable. Such maps exist: for an even coordinate count, an alternating two-label map is an example. Powers of C are bijections and do not produce it either.

This refutes the proposed replacement of the three coordinate-control maps by C,D in the inflation step; it is not a theorem that two arbitrary unary maps cannot work. One would need a combined decoder/control operation whose generated words implement enough coordinate inflations while preserving all theta^k, or an entirely different carrier construction. Neither has been constructed here.
