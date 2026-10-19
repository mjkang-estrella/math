# A root-list collision floor at every fixed moment order

This is a proved obstruction to one proof mechanism. It does not refute T188U and is not a substantiality nomination. The previous r29 fixed-vertex deduction remains paid.

Fix any good source188 prefix G, any vertex v, and let d=deg_G(v), L=G[N_G(v)]. Draw k>=2 root edges (v,X_i) independently and uniformly from the star, with replacement. Execute ALL k source root queries, regardless of earlier answers, exposing their complete initial candidate lists. In the independent unfolding let C_k mean that some triangle type is exposed at least twice anywhere in those executions.

**Exact identity.** For any finite simple G and v with d>0,

    P[X_1 != X_2 and X_1 X_2 in E(G)] = 2 e(L)/d^2.

Both initial root lists contain the triangle {v,X_1,X_2} on this event, so

    P(C_k) >= 2 e(L)/d^2.                                      (1)

This is deterministic at the list level: no priority order, recursion depth or success event enters it. If d>=2 and roots are instead sampled without replacement, the lower bound is 2e(L)/(d(d-1)). Thus removing repeated sampled edges does not remove the obstruction.

For a good prefix the degree of X in L is the codegree of v,X in G, which is (1+O(n^-c))D uniformly. Hence

    2e(L)=sum_{X in N(v)}deg_L(X)=(1+O(n^-c))d D,
    2e(L)/d^2=(1+O(n^-c))D/d=(1+O(n^-c))p,                    (2)

using d=(1+O(n^-c))np and D=np^2. The source has p~n^(-1/2+epsilon), D~n^(2epsilon), epsilon=1/2000.

Now write Z_v=deg_{H_n}(v), conditional on G. Let qbar_v=d^-1 sum_{e incident v}q_e(1), where q_e is the exact independent-unfolding survival probability. The source gives qbar_v=(1+o(1))q, q=(1+2D)^(-1/2), uniformly in v,G. Conditional on the actual terminal graph, the k sampled finite answers are independent Bernoulli variables of parameter Z_v/d; the independent-unfolding answers are independent Bernoulli variables of parameter qbar_v after averaging the independently sampled roots. Therefore, for every even k,

    E[(Z_v/d-qbar_v)^k | G]
      = E product_{i=1}^k (X_i^fin-qbar_v),
    E product_{i=1}^k (X_i^ind-qbar_v)=0.                       (3)

These identities include repeated sampled edges, as required for ordinary powers. The source's first-exposed-type coupling has identical answer vectors off C_k, and the products in (3) have absolute value at most one. Consequently its raw estimate is

    E[(Z_v/d-qbar_v)^k | G] <= 2 P(C_k).                       (4)

An application of Markov followed by a union bound over v gives only the bound

    sum_v 2 P(C_k(v))/(eta^k qbar_v^k).                        (5)

Even if the EXACT collision probabilities were known, every summand is bounded below, as a numerical right-hand side, by a positive constant times p/q^k. Thus (5) is at least a positive constant times

    n p D^(k/2) ~ n^(1/2+(k+1)epsilon),                       (6)

which diverges. Taking the minimum with the trivial probability bound one supplies no decay. Increasing B in the long-witness count, increasing fixed k, or choosing any other fixed positive epsilon cannot make this particular inequality establish T188U. The same calculation applies to ordered distinct roots, after converting factorial moments separately; the adjacency event persists.

This is NOT a lower bound on total variation between the answer vectors, on the centered moment itself, or on the probability of a bad terminal degree. In particular, outcomes can agree on C_k and signed centered products can cancel across collision histories. Formula (6) diagnoses the cost of THROWING AWAY those histories. A successful high-moment proof must exploit such cancellation or a stronger survival-weighted analysis, rather than just improve the probability of no collision.
