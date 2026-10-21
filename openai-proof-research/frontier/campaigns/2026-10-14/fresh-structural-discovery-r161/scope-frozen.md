# Frozen author target: uniform smoothing of prescribed block-type averages

Frozen only after prefreeze closure and the source/primary/history reads recorded in notes. This is an author target, not a correctness, contribution or acceptance grade.

For integers q>=3 and ell>=1 define

    m(q,s) = binomial(q+s-1,s-1),
    C(q,ell) = ell^q + 1 + q*ell
               + q*(m(q,ell^2)+ell^2+1) + 2*q*(m(q,ell)+1).

For a positive integer N divisible by q, let X be the uniform set of partitions of [N] into N/q unordered blocks, each of size q. For positive integers s_1,...,s_ell with sum N, let Z be the uniform set of ordered vertex partitions with these cell sizes. Put A(q,ell)={alpha in Z_{≥0}^ell: sum alpha_u=q}. A block has type alpha at Z when it has alpha_u vertices in cell u. A table is a family of nonnegative integers t=(t_alpha) satisfying

    sum_alpha t_alpha=N/q,
    sum_alpha alpha_u*t_alpha=s_u for every u.

For every such table, define T_t:L2(X)->L2(Z) by uniform conditional averaging over block partitions having exactly this table at Z. Let P_d be the span, on X, of products of at most d indicators 1_{e in M}, where e is a q-subset of [N]; include the constant. Let Pi_d be its orthogonal projection for uniform probability. Adjoints, norms and traces use these uniform inner products; trace is the ordinary (unnormalized) operator trace.

The claimed full conclusions are:

1. For EVERY q,ell,N,s,t above, the conditional sets are nonempty and

       tr((T_t^* T_t)^q) <= exp(C(q,ell))*(N+1)^{C(q,ell)}.

2. For EVERY real K>0 set C=C(q,ell) and

       d = ceil(2*C + 4*q*K + 2),
       N0 = ceil(max(4*d^2, q*d+1, exp(C)*2^{C+d}*d!)).

   For EVERY N>=N0 divisible by q, EVERY positive cell-size vector summing to N, and EVERY admissible table,

       ||T_t (I-Pi_d)||_{L2(X)->L2(Z)} <= N^{-K}.

3. For EVERY integer d>=0, EVERY allowed N,s, EVERY fixed vertex partition Z, and EVERY real function f on X, there exists a SINGLE real polynomial p_{Z,f,d} in the variables (t_alpha)_{alpha in A(q,ell)}, of total degree at most d, such that

       (T_t Pi_d f)(Z)=p_{Z,f,d}(t)

   for ALL admissible tables t simultaneously.

All tables include zero entries, rare events and arbitrarily unbalanced positive cell sizes. No symmetry restriction is imposed on f. No PSD-rank, approximation-complexity, quantum, other-cone, Foulkes-injectivity or growing-q/ell conclusion is part of this statement. The q=2 source theorem is an antecedent, not a newly nominated special case. No old target is replaced or changed.
