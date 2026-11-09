# DRAFT ordinary proof for MathDB 365710

Zero accepted credit. This current presentation extracts the complete argument from the frozen historical candidate. Its historical status text is preserved only in sources/. Zhou 2004, Theorem 5 and Eq.1, already supplies the deficit identity; no novelty is claimed for it. The manuscript gives the actual Lean walk/twin structural proof.

## Endpoint

For every finite simple connected triangle-free graph G with n >= 2 vertices,

    sigma_t(G) <= max_{1 <= a <= n-1} a(n-a)(n-2a)^2.

Every maximum is achieved by a complete bipartite graph. In fact any maximizing graph is complete bipartite. The n = 1 case has value zero. This settles the full extremal assertion in the MathDB record in ordinary mathematics, subject to independent review. It does not identify which of the two source Proposition 11 rounded part sizes wins; the finite maximum formulation already matches Conjecture 24.

Write m = |E(G)|, M = sum_v d(v)^2, and D = nm - M. Expanding the sum over unordered vertex pairs gives

    sigma_t(G) = nM - 4m^2 = m(n^2 - 4m) - nD.                  (1)

The handshake identity sum_v d(v) = 2m proves the first equality. Also M = sum_{uv in E}(d(u)+d(v)). For each edge uv of a triangle-free graph, N(u) and N(v) are disjoint, so the number of vertices adjacent to neither endpoint is n-d(u)-d(v). Consequently D is exactly the number of three-element vertex sets inducing precisely one edge. In particular D >= 0.

## Gap lemma

If a connected triangle-free graph on n vertices is not complete bipartite, then

    D >= n-2.                                                 (2)

First such a graph contains an induced P4. Here is a proof avoiding an imported cograph characterization. If there is no induced P4, fix v and set A=N(v), B=V\A. Every shortest path is induced, so every vertex of B other than v has distance two from v. Given b in B\{v}, choose a in A adjacent to b. For any a' in A not adjacent to b, b,a,v,a' would be an induced P4: A is independent by triangle-freeness and b is not adjacent to v. Thus b is adjacent to every element of A. Since G is connected and n >= 2, A is nonempty. Any edge within B would now make a triangle with any a in A. Thus A and B are independent and all cross edges exist, a contradiction.

Fix an induced path a-b-c-d. It has exactly two induced one-edge triples, namely {a,b,d} and {a,c,d}. Every vertex x outside this path contributes at least one further such triple using x and two path vertices. To prove this, suppose it contributes none. The neighbors S of x in the path are independent, since otherwise there is a triangle. Also S meets every path edge, since an edge with neither endpoint in S would itself give a one-edge triple with x. An independent vertex cover of the connected path is one of its two bipartition classes, {a,c} or {b,d}. In either case {x,a,d} induces exactly one edge (a and d are not adjacent and exactly one is in S), contradiction. The selected triples for distinct x are distinct and none lies wholly in the fixed path. This proves (2). No extension induction or probabilistic assumption is involved.

## Integer bracketing

For n >= 7, there is an integer 1 <= a <= n-1 with

    a(n-a)(n-2a)^2 >= n^4/16 - (n-3)^2.                       (3)

Set h(t)=t(n-t), 1 <= t <= floor(n/2). These values increase. The first value n-1 is at most n^2/8 for n >= 7: n^2-8n+8 is 1 at 7 and increases thereafter. The last value floor(n^2/4) is at least n^2/8. Thus either one value equals n^2/8, or two consecutive values bracket it. For consecutive parameters t and t+1, with t >= 1, the gap is n-2t-1 <= n-3. At least one endpoint of a bracketing interval is within half its length of n^2/8. For this endpoint a,

    |h(a)-n^2/8| <= (n-3)/2.

Now use the exact polynomial identity

    h(a)(n^2-4h(a)) = n^4/16 - 4(h(a)-n^2/8)^2,

and n^2-4a(n-a)=(n-2a)^2. This proves (3). It uses rational arithmetic only, with no square roots or continuous optimization assumption.

## Conclusion

Let G be connected, triangle-free and not complete bipartite. Necessarily n >= 4. For n >= 7, equations (1) and (2) imply

    sigma_t(G) <= n^4/16 - n(n-2)
               < n^4/16 - (n-3)^2
               <= max_{1 <= a <= n-1} a(n-a)(n-2a)^2,

where the strict inequality is n(n-2)-(n-3)^2=4n-9>0. The first bound follows by completing the square in m. For n = 4,5,6 the same upper bound is respectively 8, 385/16, 57, strictly smaller than the star values 12,36,80. For n <= 3, every connected triangle-free graph is complete bipartite (or the singleton). Finally K_{a,n-a} is connected and triangle-free for 1 <= a <= n-1 and its irregularity is exactly a(n-a)(n-2a)^2. This proves the endpoint and the stronger maximizing-graph characterization.

