# Proof implemented in r2a

Fix t >= 1 and m = 2t+1. Every independent subset A of the cyclic rim is disjoint from its translate A+1. Translation preserves cardinality, so 2|A| <= m and |A| <= t.

For a nonempty deleted set A, choose a in A. On the cycle, translated so a is zero, pair residues 1 with 2, 3 with 4, ..., 2t-1 with 2t; fix zero. This is an involution with only a fixed and every other pair an actual rim edge. Delete A by fixing both endpoints of any pair meeting A. On the complement of A it remains an involution. Every fixed point x in the complement has its original partner p(x) in A minus {a}; injectivity of p gives at most |A|-1 fixed points. This argument does not require A to be independent.

For nonempty A and B, on A-complement times B-complement first pair within the second coordinate whenever its deletion involution does not fix it. In a fixed second-coordinate column, use the first-coordinate deletion involution. The resulting involution preserves the rectangle, has only graph edges as nonfixed pairs, and has fixed set equal to the product of the two individual fixed sets. Thus it has at most (|A|-1)(|B|-1) fixed points.

For any finite region S with such an involution p, an independent I contained in S satisfies I intersect p(I) contained in Fix(p). Since p is injective, union/intersection cardinality gives 2|I| <= |S|+|Fix(p)|. Applied to the deletion product, this gives the required simultaneous deletion bound directly.

For an independent wheel-square set s, let A and B be its two mixed layers and R its rim part. Graph adjacency shows A and B are independent on the cyclic rims and R avoids their rows and columns. The exact weight is 2 times the hub indicator, plus (t+1)(|A|+|B|), plus 2|R|. If the hub is present, both mixed layers are empty and the t-per-row bound gives the result. If either mixed layer is empty, use the surviving cyclic fibres to bound R by t(m-|A|) or t(m-|B|). If both are nonempty, use the deletion product bound. The remaining arithmetic is exactly r1's two_sided_arithmetic on 1 <= |A|,|B| <= t. In every case the weight is at most 2(2t²+t+1).

Finally apply r1's weighted_lower_inf with its nonnegative vertexWeight and total weight 2(6t²+7t+3), cancel the positive denominator factor 2, and obtain the literal fractional-chromatic lower bound. No finite parameter enumeration or unproved combinatorial bridge is used.
