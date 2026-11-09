# 356833: routine full-scope reduction, zero credit

Source attack definition: distinct integer positions attack iff every nonzero coordinate difference has the same absolute value. A full box has no obstructing holes, so this exactly matches multiples of vectors in{-1,0,1}^d.

Partition{0,1,2,3}^d by floor(x_i/2). Each of2^d cells is a side2 cube: every pair in it attacks with step1. Therefore an independent placement has at most2^d points.

If S and T are independent placements in dimensions a,b, then S×T is independent in dimension a+b. For two distinct product points, at least one component pair is distinct. That pair has two different nonzero difference magnitudes; those magnitudes remain in the full concatenated difference. Thus it cannot be a queen move. Cardinalities multiply.

In dimension2 use(0,1),(1,3),(2,0),(3,2). In dimension5 the source Table4 already reports32 points. The32 coordinates in `queens5-witness.json` were recovered locally by a capped MILP; its stdout records successful termination, and the script independently checks each of496 pairs using integer differences. Consequently products give2^d for every even d>=4 by dimension2 products, and for every odd d>=5 by dimension5 times dimension2 products. The side2 partition proves optimality.

This argument simply assembles a known computational base with elementary product and partition operations. It is excluded as routine under the campaign standard; no Lean endpoint or novelty claim is needed. The MILP and checker are diagnostics, not a kernel proof; no unproved computational oracle enters an accepted theorem.
