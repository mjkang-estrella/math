# Scope fixed at the start of round r2

Author: Myeongjin Kang, no affiliation. Original prose: CC BY 4.0.

This round continues the round-4 target unchanged. The round-4 scope is
bound in this package as `inputs/private/context/r4/original-scope.md`
(SHA256 `63bc73a23d5dc0a87bb74e1cfcb7dedada01d4e3761ca169830e668b5cf5c986`),
and its text remains binding.

Research target T2: there is a finite absolute constant C such that for every
integer d,N >= 1, every family v_1,...,v_N in R^d with ||v_i||_2 <= 1,
and every two permutations pi,rho of [N], there is ONE epsilon in {-1,1}^N
such that

    max_{sigma in {pi,rho}, 0 <= k <= N}
        || sum_{j=1}^k epsilon_{sigma(j)} v_{sigma(j)} ||_2 <= C sqrt(d).

The constant must not depend on N, d, the orders or the vectors. No
restriction is placed on the orders, the coordinate signs, the dimension,
direction palettes, zero sums or norms. Both orders use the same signs. This is
an existence statement, not an online or algorithmic one.

Success means one of the following:

* a complete proof of T2 over all quantifiers; or
* a family with unbounded normalized two-order discrepancy, refuting T2.

The following do not count as success and will not be presented as such: a
bound that grows with N, a result for restricted orders, a fixed dimension
(including d=1 alone, which is necessary but not sufficient), a new method
obstruction, or a literature identification. If neither outcome is reached,
the round reports T2 as UNRESOLVED and states the exact unpaid step.

Starting state: the r4 package (seal SHA256
`e1cda9940e5020d9e47fe6e8a8e2124e7a643b8bc3e8560beee55c55f9c0ab2d`) proves
three method obstructions and no counterexample. Those obstructions are not
evidence against T2 and are not repeated as such here.
