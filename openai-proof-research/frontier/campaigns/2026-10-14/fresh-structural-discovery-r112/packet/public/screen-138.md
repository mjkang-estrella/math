# 138: ranged optimization is already compatible

Pre-freeze feasibility screen; no candidate or independent judgment.

Source `Subset-Sum-in-Time-2-power-0-49n-October-4-2026`, introduction `thm:main`, counts the **items**, permits repetitions, and gives every-execution ordinary O(2^(0.49 n)) word time under each fixed polynomial input-bit bound. Its operative implementation `eq:all-history-time` is stronger: K0 2^(0.489995 n)(n+b+2)^K on the guarded branch. The guard eventually holds for each fixed polynomial bit convention. These facts, including the error contract and guard, are stipulated.

The tempting extension is exact optimization of nonnegative binary knapsack, or feasibility of any fixed number r of subset-weight interval constraints on the same n items, with polynomial-bit weights. The strongest existing reduction is **not** adding a separate binary slack item for every capacity bit. Nederlof–van Leeuwen–van der Zwaan, [1208.4225v1](https://arxiv.org/pdf/1208.4225v1), Theorem1/Algorithm1 and Theorem2/Corollary1, keep the item set unchanged. Their proof halves weights after exposing narrow boundary intervals; the rounding error of a subset is at most n/2. Its guarantee is pointwise for every subset, so the same subset survives all r independently reduced constraints.

For completeness, the compatibility accounting is as follows. Clip each nonnegative interval to the possible total-weight range. Empty intervals reject; singleton intervals need one query. For each constraint the primary returns polynomially many exact-target pairs. Take their Cartesian product. For a chosen r-tuple choose an integer base B strictly larger than every possible coordinate sum and every retained target (discard impossible targets first). Set

    a_i = sum_(j=0)^(r-1) B^j w_(j,i),
    t   = sum_(j=0)^(r-1) B^j t_j.

No carry is possible, so sum_(i in S) a_i=t is equivalent to all selected exact equalities. The bit length is O(r(b+log n)), and there are still at most n positive items. All-zero packed items can be omitted for feasibility and restored arbitrarily in a witness. Thus for fixed r the number Q of calls, their construction, and their word-simulation overhead are polynomial in the original input length.

Source138 has two-sided error. Amplify each call independently to error at most 1/(20Q), including any subsequent binary-search and witness-recovery calls in a polynomial upper bound for Q. Conditional on every adaptive query's past, the source guarantee applies to that fixed query, so a union bound is legitimate. Binary search on the objective followed by deciding whether to exclude each successive item returns a witness when all answers are correct; a final exact check prevents returning an invalid witness. This uses neither an exact sampler nor a multiplicity estimate.

A reduced query may have m<n items and a bit length polynomial in n rather than m. On a guarded query its time is bounded by 2^(0.489995 m) poly(n+b), hence by 2^(0.489995 n) poly(n+b). On a failed bit guard, b'^(100000)>2^m implies m<100000 log2 b'=O(log n) under the fixed polynomial-bit hypothesis. Its exact meet-in-the-middle fallback is then polynomial in n. The fixed small-m cutoff is harmless for the same reason. Consequently all calls fit

    2^(0.489995 n) poly(n+b) + poly(n+b) = O_c,r(2^(0.49 n)).

This is ordinary O, not an unexplained O-star removal. Larger source-word arithmetic can be simulated by polynomially many original-word operations; the strict slack absorbs that too.

The low-space companion `A-Low-Space-Algorithm-for-Worst-Case-Subset-Sum-September-26-2026`, `thm:main` and `cor:target`, separately gives poly(n)2^(n/2) time and (n+b+2)^15 2^(0.199n) writable words. Sequential exact-query reductions retain its usual time/space transfer with polynomial overhead. They do **not** give both its space bound and the other paper's improved time bound in one run. No simultaneous-resource claim is made.

I17's phase-energy relative-variance obstruction, and r108's actual inventory, concern counting rather than this ranged decision/optimization reduction. They are not reused as a proof that all new algorithms fail. Here the positive compatible primary reduction itself removes the putative contribution. No full counting or improved simultaneous time/space target was selected.
