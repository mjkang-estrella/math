# Unbounded mean fragment size in an unlabelled bridge-addable graph class

**Abstract.** We construct one isomorphism-invariant, decomposable, bridge-addable class of finite simple graphs that has members at every order. The mean fragment size under uniform sampling of its unlabelled members tends to infinity along a sequence of orders. The construction answers MathDB 345190, Conjecture 3 of Colin McDiarmid's *Connectivity for an unlabelled bridge-addable graph class*.

## Statements and definitions

McDiarmid's Conjecture 3 reads as follows, with mathematical notation transcribed from the source. [McDiarmid, arXiv:2001.05256v2, p. 3](https://arxiv.org/pdf/2001.05256v2)

> **Conjecture 3.** For each graph class $\mathcal A$ which is bridge-addable and decomposable, there is a constant $c_A$ such that, for each positive integer $n$, if $\tilde R_n \in_u \tilde{\mathcal A}$ then
>
> $$\mathbb E[\operatorname{frag}(\tilde R_n)] \le c_A.$$

The MathDB 345190 record reads as follows. [MathDB 345190](https://mathdb.com/p/345190/the-unlabelled-bridge-addable-fragment-size-conjecture)

> Let $\mathcal A$ be a class of graphs that is **bridge-addable**, meaning that adding an edge between vertices in distinct components preserves membership, and **decomposable**, meaning that a graph belongs to $\mathcal A$ if and only if each of its components does. For a graph $G$, define its **fragment size** by
>
> $$
> \operatorname{frag}(G)=|V(G)|-\max\{|V(C)|:C\text{ is a component of }G\}.
> $$
>
> Let $\tilde{R}_n \in_u\tilde{\mathcal A}$ be sampled uniformly from the unlabelled graphs in $\mathcal A$ on $n$ vertices. **Unlabelled bridge-addable fragment-size conjecture.** For each such graph class $\mathcal A$, there is a constant $c_{\mathcal A}$ such that, for each positive integer $n$,
>
> $$
> \mathbb E[\operatorname{frag}(\tilde{R}_n)]\leq c_{\mathcal A}.
> $$
>
> The labelled analogue has a uniform expectation bound, while the source gives an unlabelled example showing that the expectation can grow linearly for a particular class; the conjectured bound remains open in general.

The source's cycle example gives a large mean at the single order $2k$ for a class defined by choosing a minimum cycle length $k$. The construction below supplies one class and infinitely many orders.

The source definitions and their Lean counterparts are as follows. The citations give page numbers in arXiv v2.

| Source wording | Lean representation |
| --- | --- |
| “Call a class $\mathcal A$ of graphs bridge-addable if, whenever a graph $G$ in $\mathcal A$ has vertices $u$ and $v$ in distinct components, then the graph $G+uv$ (obtained by adding the edge $uv$) is also in $\mathcal A$.” [p. 1](https://arxiv.org/pdf/2001.05256v2#page=1) | `BridgeAddable A` requires `A.mem (G ⊔ edge u v)` when `A.mem G` and `¬ G.Reachable u v`. |
| “Call the class $\mathcal A$ of graphs decomposable when a graph is in the class if and only if each component is.” [p. 2](https://arxiv.org/pdf/2001.05256v2#page=2) | `Decomposable A` is the equivalence between `A.mem G` and `∀ c : G.ConnectedComponent, A.mem (G.induce c.supp)`. |
| “The fragment size $\operatorname{frag}(G)$ of a graph $G$ is the number of vertices of $G$ less the maximum number of vertices in a component.” [p. 2](https://arxiv.org/pdf/2001.05256v2#page=2) | `frag G` is `n - largestComponent G`, where `largestComponent` takes the finite supremum of `Nat.card c.supp` over connected components. |
| “Let $\tilde{\mathcal A}_n$ be the set of unlabelled graphs in $\mathcal A_n$, and similarly for other graph classes. We may identify an unlabelled graph as an isomorphism class of labelled graphs. We use the notation $\tilde R_n \in_u \tilde{\mathcal A}$ to indicate that the random unlabelled graph $\tilde R_n$ is sampled uniformly from $\tilde{\mathcal A}_n$.” [p. 2](https://arxiv.org/pdf/2001.05256v2#page=2) | `UnlabelledMembers A n` is the graph-isomorphism quotient of the subtype of members on `Fin n`. `fragType` is the induced function on that quotient. `meanFragReal` sums it in $\mathbb R$ and divides by the cardinality of the quotient. |

A graph is finite, simple, and undirected. In Lean the class predicate `GClass.mem` is defined on every finite vertex type, and `GClass.iso` expresses invariance under graph isomorphisms. Every graph of order $n$ can be labelled on `Fin n`. The quotient assigns one outcome to each isomorphism class. An isomorphism bijects connected components and their supports, so fragment size is independent of the representative. With a nonempty outcome set, the finite average is the expectation because each outcome has probability $1/|\tilde{\mathcal A}_n|$.

## Theorem

There exists one isomorphism-invariant, decomposable, bridge-addable class $\mathcal A$ that is nonempty at every positive order and for which $\sup_{n\ge1}\mathbb E[\operatorname{frag}(\tilde R_n)]=+\infty$.

### Bridge-deleted pieces

Delete all bridges of a graph $G$ and call the connected components of the resulting spanning graph its *pieces*. A surviving edge lies on a cycle of $G$. Every edge on that cycle is a nonbridge, so the whole cycle survives in the same piece. A bridge has endpoints in different pieces, since a path internal to a piece bypasses it. There is at most one edge between any two distinct pieces. A second such edge, together with paths in the pieces between the corresponding endpoints, would bypass the first. The bridges themselves form an acyclic spanning subgraph: any cycle in it would be a cycle of $G$ through a bridge, and no bridge lies on a cycle. Thus a graph of positive order $n$ has at most $n-1$ bridges.

Fix any collection of allowed isomorphism types of connected bridgeless graphs. Let $\mathcal A$ be the graphs whose pieces are all allowed. Isomorphisms preserve bridges and pieces. Deleting bridges in each connected component separately gives the same pieces as deleting them in the full graph. Indeed, every walk starting in a connected component stays in it, including walks that avoid a specified edge. This gives decomposability. Adding an edge between two connected components makes that edge a bridge, and cannot create a cycle. The old bridge status of every edge therefore persists, giving bridge-addability.

### Cyclic layers with many independent choices

Take integers $t\ge 1$ and $m\ge 3$. Use $t$ left layers and $t$ right layers, each with vertex coordinates in $\mathbb Z/m\mathbb Z$. Join every two distinct vertices in each layer. Between every two distinct layers include the zero-offset matching, which joins vertices with equal coordinates. For every ordered choice of one left layer $i$ and one right layer $j$, choose an arbitrary subset $D_{ij}$ of the nonzero residues. Add the undirected edges from $(i,a)$ to $(j,a+d)$ for all $a$ and all $d\in D_{ij}$.

The layer cliques and the matchings make each graph connected. A within-layer edge has a bypass through a third vertex of the layer. A cross-layer edge has a bypass made of its translate by $1$ and two within-layer edges. Consequently every graph in the family is bridgeless. Translation by any common residue in all layers is an automorphism. It carries each vertex in a given layer to the vertex of coordinate zero in that layer, so the number of vertex orbits is at most $2t$.

Let $k=2tm$ be the order, and let $T$ be the number of isomorphism types in the family. There are exactly $2^{t^2(m-1)}$ distinct graphs produced on this labelled vertex set: the neighbors of $(i,0)$ in right layer $j$ at nonzero coordinates recover $D_{ij}$. The fibre of any one isomorphism type has at most $k!$ labelled graphs. Choose a representative of the type and, for each graph in the fibre, an isomorphism to that representative, regarded as a permutation of the common vertex set. A permutation cannot send two different labelled graphs to the same representative. Thus
$$
2^{t^2(m-1)}\le T k!.
\tag{1}
$$

### One class at all stages

Put $k_0=1$. At stage $j\ge0$, set
$$
 M=k_j,\qquad s=M+20,\qquad
 t=2^s,\qquad m=t^3,\qquad k_{j+1}=2tm.
$$
Allow every cyclic-layer type at every stage, and allow the one-vertex graph. This determines a single class by the piece construction. It contains all edgeless graphs. The inequality $2^M\ge M+1$ gives $t\ge M+4$, so $m\ge3$ and $k_{j+1}>2k_j$. The sequence $k_j$ is strictly increasing and $k_j\ge j+1$.

Fix a stage $j$ and abbreviate $k=k_{j+1}$, $n=2k$, with $M,t,m,T$ evaluated at this stage. Each earlier piece has at most $M$ vertices. Each current piece has $k$ vertices. The next piece size is greater than $2k$, so no later piece occurs at order $n$.

### Counting competitors

We bound the number of unlabelled members of order $n$ with at most one current piece by counting their labelled versions on a fixed $n$-element set. For each such graph choose the following data.

1. Assign every vertex of a small piece the label of a representative vertex of that piece. Give the vertices of the unique current piece, if present, a separate marker. The tags identify the pieces and have at most $(n+1)^n$ possibilities.
2. Assign the vertices of each small piece distinct slots in an $M$-element set. Off the small pieces use any default slot. The slot function has at most $M^n$ possibilities. Record from each vertex a Boolean adjacency row of length $M$ giving its neighbors inside its own small piece. There are at most $2^{Mn}$ possible arrays of rows.
3. Choose one current isomorphism type and a fixed representative for that type. If there is a current piece, record an isomorphism of it to the representative by specifying one representative coordinate per vertex of the piece. Use arbitrary defaults for the remaining entries and also for the type when the piece is absent. There are at most $Tk^n$ possibilities.
4. Record the bridges in an array of length $n$, with a sentinel for unused entries. An entry is an unordered vertex pair or the sentinel. There are at most $(n^2+1)^n$ possible arrays.

The first three items recover the internal adjacency within each piece, and the fourth recovers all edges between pieces. Thus each code decodes to at most one graph. Since $M,k\le n$, $n+1\le n^2$, and $n^2+1\le n^3$, the number of competitors is at most $TU$, where
$$
U=n^{7n}2^{Mn}.
\tag{2}
$$

Here $k=2^{4s+1}$ and $n=2^{4s+2}$. Put $L=4s+1$ and $B_0=7(4s+2)+M$. Since $k!\le k^k$,
$$
U k!\le 2^{nB_0+Lk}.
$$
The exponent $nB_0+Lk=k(L+2B_0)$ is at most $kt/4$. Indeed,
$$
L+2B_0=62M+1229\le 2^{18}(M+1)\le 2^{M+18}=t/4.
$$
And $kt/4=t^2m/2\le t^2(m-1)$ because $m\ge2$. Combining this with (1) proves $T\ge U$. In particular the number of competitors is at most $T^2$.

### Counting two current pieces

If a member has two current pieces, their $2k$ vertices exhaust its vertex set. The graph is their disjoint union or a join by one bridge. Fix one representative per current isomorphism type, taken to be a cyclic-layer graph on the standard vertex set, so that translations are automorphisms of it. Encode the two pieces by an ordered pair of these representatives. For a join, record the layer of the endpoint in each representative. Independent translations in the two representatives move the endpoints to coordinate zero, so the choice of those two layers is sufficient. Include one extra code for the disjoint union. There are at most $T^2((2t)^2+1)$ codes, and hence at most that many unlabelled members with two current pieces.

The unlabelled disjoint unions of two current pieces form a set of cardinality $D\ge T^2/2$. Each of the $T^2$ ordered pairs yields a union, and an isomorphism of unions carries connected components to connected components. So at most an ordered pair and its swap can give the same type. Each such graph has fragment size $k$. All other graphs have nonnegative fragment size. Combining the two upper counts for the denominator gives
$$
\mathbb E[\operatorname{frag}(\tilde R_{2k})]
\ge \frac{kD}{T^2((2t)^2+2)}
\ge \frac{k}{2((2t)^2+2)}
\ge \frac{t^2}{6}.
$$
The last inequality uses $k=2t^4$ and $2((2t)^2+2)\le12t^2$. Since $k_j\ge j+1$, the values $t=2^{k_j+20}$ diverge along the observation orders $2k_{j+1}$. This proves the theorem. The same class consequently has infinite limsup of the mean fragment size, which also violates Conjecture 4 (MathDB 345191).

## Significance and prior work

McDiarmid's single-order example shows that a bound independent of the class fails when it is required at all orders. Conjecture 3 allows the constant to depend on the class. The construction above addresses that distinction by making the number of new piece types large enough to dominate the contribution of all earlier stages, while keeping the possible attachments per ordered pair small.

The independent review traced Conjecture 3 to the June 2020 arXiv version of the workshop note. The 2014 Oberwolfach announcement (Oberwolfach Report 12/2014, pp. 708–709) posed a universal-constant variant: one constant $c$ for all decomposable bridge-addable classes and all $n$. McDiarmid's 2024 paper on pendant appearances and components in structured classes still referred readers to the workshop note for unlabelled conjectures. McDiarmid and Saller's papers on order-dependent surfaces are mainly about labelled graphs. Their brief unlabelled results concern class sizes and the probability of connectivity, not the expected fragment size, and the first of them cites the workshop note for the unlabelled analogues as conjectures. The review and discovery lane's bounded searches of indexed literature and public proof registries found no matching construction. The closest approach they identified was the workshop note's cycle example. [Oberwolfach report](https://publications.mfo.de/bitstream/handle/mfo/3402/OWR_2014_12.pdf?sequence=1) · [McDiarmid, arXiv:2108.07051](https://arxiv.org/abs/2108.07051) · [McDiarmid–Saller, arXiv:2106.06775](https://arxiv.org/abs/2106.06775) · [McDiarmid–Saller, arXiv:2108.07666](https://arxiv.org/abs/2108.07666)

## Formal certificate

The Lean source appendix gives the finite-graph definitions, quotient constructions, and proof. `BridgeFragment.mathdb_345190` establishes the counterexample for the exact rational average of the integer fragment sizes. `BridgeFragment.meanFragReal_eq` identifies the real average with the cast of that rational average. `BridgeFragment.mathdb_345190_real` establishes the endpoint with a real bound. The packet treats the observation about Conjecture 4 as a consequence of the written proof for the same class.
