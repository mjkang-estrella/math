# Simultaneous coordinate blocks: a paid algebraic extension

This elementary extension of source `alg:shift-table` was investigated as a possible intermediate step. It is not a height-two theorem and is not nominated as a new substantial result.

Let A be a finite nonempty set of size a, S a finite vector space of size q, and k>=1 a fixed number of coordinate blocks. There is an integer r>=1, depending only on a,q,k, with this property. For every table

    f:A^(kr) -> End_lin(S)

there is beta:A^(kr)->S such that for every tuple u, state x, and block t, some coordinate i in that block has

    c -> x f(u[i:=c]) + beta(u[i:=c])

constant on A. Thus one correction works for all blocks, while the omitted coordinate may depend on u,x,t. No particular coordinate must work simultaneously for all states.

If a=1 or q=1, the assertion is immediate. Otherwise choose all beta values independently and uniformly. For fixed u,x,t, condition on beta(u). The r coordinate lines through u inside block t meet only at u. The other a-1 random values on each line are independent, and the probability that one line is constant is p=q^(1-a), irrespective of f and the conditioned central value. Hence the bad-event probability is exactly (1-p)^r.

An event depends only on beta at tuples at Hamming distance at most one from u, and only along its own block. Two event supports can intersect only when their centers are at Hamming distance at most two in the entire kr-coordinate cube. A valid upper bound on the number of dependent events, plus one, is

    D+1 <= k q [1 + kr(a-1) + binom(kr,2)(a-1)^2].

Each potential center has kq possible block/state labels. The symmetric local lemma therefore applies as soon as

    e (1-q^(1-a))^r kq [1+kr(a-1)+binom(kr,2)(a-1)^2] <= 1.

For fixed a,q,k, the exponential factor tends to zero faster than the displayed polynomial grows, so some r works uniformly over f. This is exactly the source's local-lemma mechanism with an extra finite block label, and is credited accordingly.

The more conservative rational condition 4 C (1-q^(1-a))^r <= 1, with C equal to the displayed upper bound for D+1, also suffices directly by the source's choice u=1/(2C) and Bernoulli's inequality. checks.py uses this latter sufficient condition, so its arithmetic involves no floating-point approximation to e.

Why this does not solve the target: the actual early and outer data are not merely two coordinate blocks of one fixed table with one common alphabet factorization. The early table includes an entire later-context function psi; varying an outer product may change that table and its chosen correction. Outer mismatched tags prescribe a particular translation, and the early decoder uses the exceptional-origin promise. The lemma imposes none of those compatibility conditions. No inference from this abstract grid statement to one sound complete episode split has been established.
