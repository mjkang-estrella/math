# H007 disposition: close scalar-normalized transfer blocks

Verified new factoring complexity improvement: **NONE**. The coordinator read
and checked the [independent construction report](H007-coefficient-extractor.md),
including its pole argument, nonunit example and total batching cost.

The rejection is valid for the specified representation. At every root -j of
D_L(x)=(x+1)...(x+L), the matrix product contains either U(-1), or the adjacent
nonzero product U(0)U(-1), surrounded by invertible factors. Hence no root of
D_L cancels from all four numerator entries over Q. The leading coefficient
matrix V^L is invertible even modulo N, so the dense matrix degree also stays L.
Neither fact is a lower bound for different representations or for action on
the particular canonical initial vector.

The equal-residue integral-lift example correctly shows why arbitrary nonunit
division cannot be defined from the two residue inputs alone. Returning a
proper factor instead is legitimate, including descent when the initial gcd
equals N. But the cheap factor-return route is the known consecutive-product
search with N^(1/4) scale under fast polynomial arithmetic. This loses to the
checked N^(1/5) deterministic comparison and to heuristic GNFS asymptotically.

Scope clarification: the report's horizon-m matrix batching is a
**factor-or-action** algorithm. Its cost bound does not promise the canonical
coefficient after it returns a factor. This does not affect the negative cost
comparison. Exact quotient lifting remains correct but uses the large modulus
N*D; it cannot treat the additional precision as free.

The series-Newton revision uses only division by 2, which is valid for odd N,
and doubles precision correctly. It retains dense coefficient storage through
the target index. Keep it as a correctness reference, not a faster extractor.
All 33 frozen diagnostic cases completed, including six ambiguity controls
and four initial gcd=N cases; their full evidence is linked in the report.

Do not benchmark the same normalization again without a genuinely different
transition formula and a bound on its total state. The composite Hasse identity
remains a scoped conditional reduction with the efficient extractor missing.
