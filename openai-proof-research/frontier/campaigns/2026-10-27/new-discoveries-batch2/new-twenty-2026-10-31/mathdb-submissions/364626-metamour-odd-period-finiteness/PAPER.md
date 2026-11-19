# Finiteness at each odd metamour period

## Abstract

For each positive odd integer \(k\), a finite connected simple graph that returns to its original labeled graph after \(k\) iterations of the distance-two operation has uniformly bounded order. We give an explicit bound and deduce finiteness up to isomorphism at each exact odd period. The main step shows that among the neighbors of a vertex, no triangle of pairs can share a common temporal adjacency word. A finite triangle Ramsey bound then bounds the degree, and a geodesic argument bounds the diameter.

## 1. Statement and conventions

Let \(G\) be a finite simple graph on a fixed vertex set \(V\). Distances are lengths of shortest paths, with distance \(\infty\) between different components. Its metamour \(M(G)\) is the simple graph on \(V\) in which \(xy\) is an edge exactly when \(d_G(x,y)=2\). Equivalently, \(x\) and \(y\) are distinct, are nonadjacent in \(G\), and share a neighbor in \(G\). Put \(G_t=M^t(G)\), beginning with \(G_0=G\). A return at \(k>0\) is the equality \(G_k=G\) on \(V\). The exact metamour period is the least such \(k\). The minimum step for an isomorphism \(G_k\cong G\) is the pseudo-metamour period. Eventual periodicity permits a transient before a return occurs. The theorem uses equality on \(V\) at the initial graph.

**Theorem.** Define \(r_0=2\) and \(r_{q+1}=(q+1)(r_q-1)+2\) for \(q\ge 0\). For \(k>0\), put \(D(k)=r_{2^k}-1\) and \(R(k)=2^k-1\). If \(k\) is odd, \(G\) is connected and \(G_k=G\), then
\[
\Delta(G)\le D(k),\qquad
\operatorname{diam}(G)\le R(k),\qquad
|V|\le B(k):=\sum_{j=0}^{R(k)} D(k)^j .
\]
Consequently, at each positive odd \(k\) there are finitely many isomorphism classes of finite connected simple graphs whose exact metamour period is \(k\).

This answers Conjecture 7.7 of Erickson, Herden, Meddaugh, Sepanski, Minyard and Rosengartner for the finite simple graphs in their paper. In that conjecture \(k\) is fixed before counting graphs. The proof of the bounds needs a return at \(k\), and the resulting finite collection can be restricted to graphs of least period \(k\). [Native source, arXiv:2409.02306v1](https://arxiv.org/abs/2409.02306v1)

## 2. Connected phases and a two-step obstruction

Assume \(G_k=G\) for \(k>0\). Iteration gives \(G_{t+k}=G_t\) for every \(t\ge 0\). Each edge of \(M(H)\) can be replaced by a length-two walk in \(H\), so reachability in \(M(H)\) implies reachability in \(H\). If \(G\) is connected, choose a multiple of \(k\) at least \(t\). The phase at that multiple is \(G\), so tracing reachability back to time \(t\) shows \(G_t\) is connected. Every phase has a predecessor under \(M\), for instance \(G_{t+k-1}\) is a predecessor of \(G_t\).

Suppose \(H=M(J)\) and every pair of distinct nonadjacent vertices in \(H\) has a common neighbor in \(H\). Write \(\bar H\) for the simple complement of \(H\). The distance-two rule gives \(M(H)=\bar H\). We claim \(M(\bar H)=H\). Every edge of \(M(\bar H)\) belongs to \(H\) because it is absent from \(\bar H\). Conversely, an edge \(xy\) in \(H\) has a witness \(z\) adjacent to \(x\) and \(y\) in \(J\). Each edge of \(J\) is absent from \(H=M(J)\), so \(xz\) and \(yz\) are edges of \(\bar H\). Together with \(xy\notin E(\bar H)\), this gives \(xy\in E(M(\bar H))\). Hence \(M^2(H)=H\).

If \(H=G_t\) and \(k=2m+1\), the phase satisfies \(M^k(H)=H\). A two-step return would give \(M^{2m}(H)=H\) and then \(M(H)=H\). Since \(H\) and \(M(H)\) have disjoint edge sets, \(H\) would be edgeless. Therefore a phase containing an edge cannot have the common-neighbor property of the previous paragraph.

## 3. The triangle obstruction

**Lemma.** Let \(H\) be connected, and let \(T=\{a,b,c\}\) be a triangle in \(H\) whose three vertices form an independent set in both \(M(H)\) and \(M^2(H)\). Then every two distinct nonadjacent vertices of \(H\) have a common neighbor in \(H\).

**Proof.** No vertex can be adjacent in \(M(H)\) to two distinct vertices \(s,t\) of \(T\). Those two vertices are nonadjacent in \(M(H)\), so such a vertex would witness their adjacency in \(M^2(H)\).

Every vertex adjacent in \(H\) to some vertex of \(T\) is adjacent to at least two vertices of \(T\). This holds for the vertices of \(T\) by its triangle edges. For a vertex outside \(T\), if its only neighbor in \(T\) were \(s\), the two other vertices of \(T\) would both be at distance two from it via \(s\). That would give two forbidden adjacencies in \(M(H)\).

Let \(A\) be the set of vertices adjacent in \(H\) to at least two vertices of \(T\). It contains \(T\). If \(x\) is adjacent to \(y\in A\), then either \(x\) has a neighbor in \(T\), and the previous paragraph gives \(x\in A\), or \(x\) has no neighbor in \(T\). In the latter case \(x\notin T\), and two distinct neighbors of \(y\) in \(T\) would both be at distance two from \(x\) via \(y\). This is impossible. Hence \(A\) contains each neighbor of each of its vertices. A walk to \(T\) now shows \(A=V(H)\). The neighborhoods in \(T\) of any two vertices of \(H\) intersect, since each has size at least two. A vertex in the intersection is the required common neighbor. \(\square\)

## 4. Temporal adjacency and the degree bound

Assume a positive odd return at \(k=2m+1\). Assign each unordered pair of distinct vertices the length-\(k\) Boolean word of its adjacencies in \(G_0,\ldots,G_{k-1}\). The return identity shows that equal words give equal adjacency at every time \(t\ge 0\).

Suppose all three pairs on \(a,b,c\) have the same word, and that the word is nonzero. At some time \(t\) these vertices form a triangle. Whenever they form a triangle at time \(i\) they form an independent triple at time \(i+1\), since consecutive phases have disjoint edge sets. If all three pairs were absent at time \(i+2\), the triangle lemma and the existence of a predecessor would give the forbidden two-step return of an edged phase. Thus at least one pair is present at \(i+2\), and their equal words imply all three are present. Repeating this implication \(m+1\) times gives the triangle at \(t+2(m+1)=t+k+1\), and therefore at \(t+1\). This contradicts independence at \(t+1\).

We use the following finite Ramsey bound. For \(q\ge 0\), every coloring of the pairs of a set of size at least \(r_q\) with \(q\) colors has a monochromatic triangle. With \(q=0\) the hypotheses are impossible because there are at least two vertices. For the induction step from \(q\) to \(q+1\), choose a pivot \(v\). At least \((q+1)(r_q-1)+1\) other vertices are partitioned by the color of their edge to \(v\). A class has at least \(r_q\) vertices, because otherwise the total would be at most \((q+1)(r_q-1)\). If this class contains an edge of its pivot color, that edge and \(v\) give the triangle. Otherwise its pairs use only the other \(q\) colors, and induction applies. In particular \(r_1=3\).

Fix a vertex \(v\) of \(G\). Each pair of distinct neighbors \(a,b\) of \(v\) has a nonzero word. If \(ab\) is an edge of \(G\), the word is nonzero at time zero. If \(ab\) is absent from \(G\), then \(ab\) is an edge of \(G_1\) via \(v\), and time one is read modulo \(k\). With at most \(2^k\) colors, a neighborhood of size at least \(r_{2^k}\) would have a monochromatic triangle of nonzero color, already excluded. Thus every vertex has degree at most \(D(k)\).

## 5. Geodesics and the order bound

For every \(i\ge 0\), an edge \(xy\) of \(G_i\) satisfies \(d_G(x,y)\le 2^i\). At \(i=0\) this is the definition of adjacency. An edge at \(i+1\) has a common-neighbor witness in \(G_i\). Applying the bound twice and concatenating walks proves the next bound.

Conversely, \(d_G(x,y)=2^i\) forces \(xy\) to be an edge of \(G_i\). The case \(i=0\) is adjacency at distance one. For the step, split a shortest \(x\)–\(y\) path of length \(2^{i+1}\) at its midpoint \(z\). Each half has distance \(2^i\), because replacing either by a shorter path would shorten the original walk. Induction gives both edges \(xz,yz\) in \(G_i\). The distance bound for \(G_i\)-edges excludes \(xy\) from \(G_i\), and \(x\ne y\) because their distance is positive. Thus \(xy\) is an edge of \(G_{i+1}\). If any pair has distance at least \(2^k\), its geodesic includes a pair at distance exactly \(2^k\). That pair belongs to \(E(G_k)=E(G)\), contrary to \(2^k>1\). Hence the diameter bound holds for every positive return.

For \(d\ge 0\), set \(B_d(0)=1\) and \(B_d(n+1)=1+d B_d(n)\). A ball of radius \(n+1\) around \(v\) is covered by \(\{v\}\) and the radius-\(n\) balls around its neighbors, by taking the first edge of a shortest walk. In any graph of maximum degree at most \(d\), induction therefore bounds every radius-\(n\) ball by \(B_d(n)=\sum_{j=0}^n d^j\), with \(d^0=1\). For nonempty connected \(G\), the ball of radius \(R(k)\) around any vertex contains every vertex. Substituting \(d=D(k)\) proves the order bound. If the empty graph is allowed by a vacuous connectivity convention, its order is zero and its exact period is one.

## 6. Finiteness and small periods

For each \(0\le n\le B(k)\), there are \(2^{\binom n2}\) simple graphs on the fixed set \(\{0,\ldots,n-1\}\). Retain those that are connected and have least labeled return \(k\). Every graph in the theorem can be transported to one of these labeled sets by a bijection. Bijections preserve distances and commute with all metamour iterations, so equality at each step and the minimal return step are both preserved. The transported graph is in the finite collection. The collection can include several labelings of the same isomorphism class, which still proves finiteness of the classes.

For \(k=1\), equality \(M(G)=G\) forces an empty edge set, so the unique nonempty connected example is the one-vertex graph. If permitted, the empty graph gives one additional class at \(k=1\). For \(k=3\), the native Theorem 7.5 gives the sharper classification \(C_7\) and \(C_9\). Their returns can also be seen directly on cyclic labels. An undirected cycle with steps \(\pm s\) changes to steps \(\pm 2s\) on these vertex sets. The first two doubled step sizes are neither \(1\) nor \(-1\) modulo \(7\) or \(9\), and \(2^3\) equals \(1\) modulo \(7\) and \(-1\) modulo \(9\). The general finiteness argument gives a bound and a finite covering collection. A structural classification at other odd periods lies beyond its scope.

## 7. Attribution and formal certificate

William Q. Erickson, Daniel Herden, Jonathan Meddaugh, Mark R. Sepanski, Mitchell Minyard and Kyle Rosengartner posed Conjecture 7.7 in *Limits and Periodicity of Metamour 2-Distance Graphs*, arXiv:2409.02306v1, 2024. Definitions 2.1–2.3 specify the operation and three period conventions. The diameter-two and image/coimage facts in §3 and the dyadic walk ideas in Lemma 8.3 and Theorem 8.4 are precedents for Sections 2 and 5 here. The finite Ramsey recurrence and ball counts are standard combinatorial arguments. The contribution under review is the two-phase triangle obstruction used with nonzero temporal words to control degrees in every odd-return orbit. This paper establishes the bound and finiteness. Priority and substantive novelty remain subject to separate source and registry review. [Native source](https://arxiv.org/abs/2409.02306v1)

The [exact Lean appendix](LEAN-SOURCE-APPENDIX.md) contains the eight canonical modules. The [crosswalk](CROSSWALK.md) relates the paper to these modules and to the independent statement check.
