# A linear threshold for connected size Ramsey numbers of star matchings

Let $K_{1,p}$ be the star with $p$ edges. We prove that the connected size Ramsey number of a red $nK_{1,p}$ versus a blue $K_{1,m}$ is $n(m+p)-1$ whenever the positive integers $m,n,p$ satisfy $m\ge 5(n+p)$. This proves Conjecture 1 of Guo, Zhang and Zhang.

## MathDB 362603

The record states the definitions and conjecture as follows.

> Let $nK_{1,p}$ be the disjoint union of $n$ copies of the star $K_{1,p}$, and let $K_{1,m}$ be the star with $m$ edges. The connected size Ramsey number $\hat r_c(G_1,G_2)$ is the minimum number of edges in a connected graph $G$ such that $G\to (G_1,G_2)$. **Linear-threshold conjecture.** There exists a positive constant $c$ such that for all positive integers $m$, $n$, and $p$ with $m\geq c(n+p)$, we have
>
> $$
> \hat r_c(nK_{1,p},K_{1,m})=n(m+p)-1.
> $$

## Source definitions and Lean representation

Graphs are finite and simple. In the source's definition of $G\to(G_1,G_2)$, every red-blue edge-coloring must produce “a red subgraph isomorphic to $G_1$, or a blue subgraph isomorphic to $G_2$.” Its $K_{1,m}$ is “a tree with $m$ edges sharing a common endpoint.” The MathDB definitions of the star matching and the connected minimum are quoted above. [Guo, Zhang and Zhang, §1](https://arxiv.org/html/2404.03175v1#S1)

| Source object | Lean definition |
|---|---|
| The disjoint union $nK_{1,p}$ and the single star $K_{1,m}$ | `starForest n p` on `Fin n × Option (Fin p)`, with adjacency between the center `(i, none)` and each leaf `(i, some j)`. The blue pattern is `starForest 1 m`. |
| A subgraph isomorphic to the pattern | `HasCopy H G` requires an injective graph homomorphism from the pattern to its host. The map preserves all pattern edges and allows extra edges in the host. The Lean theorem `hasCopy_iff_subgraph` proves equivalence to an isomorphism onto a subgraph. |
| $G\to(G_1,G_2)$ | `Arrows G n p m` quantifies over every red graph `R ≤ G` and uses `G ⊓ Rᶜ` for the blue graph. The Lean theorem `arrows_iff_edge_partition` proves equivalence to quantifying over red and blue graphs whose disjoint union of edge sets is the full host edge set. |
| The minimum edge count over connected hosts | `ConnectedRamseyHost n p m e` requires a connected arrowing graph with exactly $e$ edges. The conclusion is `IsLeast` for the set of those counts, so it requires both an attaining host and a lower bound; no convention for the infimum of an empty set is involved. Mathlib's `Connected` includes nonemptiness, so the empty graph is not a host, and the endpoint assumes $n,p,m\ge1$, so $n(m+p)-1\ge1$ involves no truncated subtraction. Hosts can be enumerated on `Fin v`. The Lean transport lemma `connectedRamseyHost_of_graph` preserves connectivity, edge count, and arrowing under an enumeration of the vertices. |

## Theorem and proof

**Theorem.** For positive integers $n,p,m$ with $m\ge 5(n+p)$, the connected size Ramsey number $\hat r_c(nK_{1,p},K_{1,m})$ is $n(m+p)-1$.

**Upper bound.** Write $M=m+p-1$. Start with $n$ disjoint copies of $K_{1,M}$. Join the center of the first star to each of the other $n-1$ centers. The resulting host is connected and has $nM+n-1=n(m+p)-1$ edges. In a coloring with no blue $K_{1,m}$, each of the original stars has at most $m-1$ blue edges and hence at least $p$ red edges. Taking $p$ red edges in each original star gives the required disjoint red stars.

**Lower bound.** Let $G$ be a connected graph with $e\le n(m+p)-2$ edges. Put

$$
 U=\{u:\deg_G(u)\ge m\},\qquad V=V(G)\setminus U,\qquad t=|U|.
$$

For $u\in U$ write $d_V(u)=|N_G(u)\cap V|$. Call $u$ strong when $d_V(u)\ge M$. Let $s$ be the number of strong vertices and $w=t-s$ the number of weak vertices.

Color every edge inside $U$ red and every edge inside $V$ blue. For each $u\in U$, choose exactly

$$
 r_u=\max\{0,d_V(u)-(m-1)\}
$$

red edges from $u$ to $V$, and color the other edges from $u$ to $V$ blue. These choices concern disjoint sets of edges. The blue degree of $u\in U$ is at most $m-1$, and the full degree of every vertex in $V$ is at most $m-1$. Thus every coloring of this form avoids a blue $K_{1,m}$.

Every red star uses a vertex of $U$ because it has at least one edge and every red edge meets $U$. If it uses exactly one vertex $u\in U$, all its $p$ edges are incident with $u$ and have their other ends in $V$. This includes a single red edge even if the chosen copy designates its $V$-vertex as the center. In this situation $r_u\ge p$, so $u$ is strong. Consequently a packing of $n$ red stars requires

$$
 t\ge n,\qquad t+s\ge 2n.
$$

Indeed at most $s$ stars can use one vertex of $U$, and the others each use at least two.

### More than $n$ high-degree vertices

Suppose $t>n$ and both necessary packing inequalities hold. Put $a=t-n$. Then $a\ge1$, $s\ge n-a$, and $w\le2a$. The degree sum gives $tm\le2e<2n(m+p)$. Therefore

$$
 a<n+\frac{2np}{m}\le n+\frac p2,
$$

where $m\ge 5(n+p)$ implies $m\ge4n$.

The strong vertices contribute at least $sM$ edges to $V$. Separately, count edges from weak vertices to vertices outside the weak set. Each weak vertex has at least $m$ neighbors, of which at most $w$ are weak. This gives at least $wm-w^2$ distinct edges, each counted at its weak end. The two collections are disjoint, since an edge of the first has no weak end. Hence

$$
\begin{aligned}
 e &\ge sM+wm-w^2\\
   &=tm+s(p-1)-w^2\\
   &\ge (n+a)m+(n-a)(p-1)-4a^2\\
   &=nM+a(m-p+1-4a).
\end{aligned}
$$

Using $4a\le4n+2p$, the last factor is at least $n+2p+1$. Together with $a\ge1$, this contradicts $e\le nM+n-2$. If $t<n$, or if $t=n$ and $s<n$, the packing inequalities already fail. Thus only $t=s=n$ requires a specific choice of the red edges to $V$.

### Exactly $n$ high-degree vertices, all strong

Put $b_u=d_V(u)-M\ge0$ for $u\in U$, so that $r_u=p+b_u$. Let $H$ be the spanning subgraph of $G$ with precisely the edges between $U$ and $V$. Put $f=|E(G)\setminus E(H)|$. Counting the edges of $H$ at their ends in $U$ gives

$$
 e=nM+\sum_{u\in U}b_u+f,\qquad
 \sum_{u\in U}b_u+f\le n-2.
$$

Let $q$ be the number of components of $H$, including isolated vertices. Contract each component to a vertex, discard loops, and collapse parallel edges. The resulting simple graph is connected because paths in $G$ project to walks after consecutive equal vertices are removed. Every edge of the contracted graph is the image of an edge of $G$ outside $H$. Thus $f\ge q-1$, since the contracted graph has a spanning tree with $q-1$ edges.

Assign weight $\omega(u)=1-b_u$ to $u\in U$ and weight zero to vertices in $V$. The total weight is $n-\sum_{u\in U}b_u\ge q+1$. It follows that some component has weight at least two. Among all vertex sets with weight at least two that induce a connected subgraph of $H$, choose one $W$ of minimum cardinality. Let $T$ be a spanning tree on $W$ in $H[W]$. Every vertex weight is at most one, so $W$ has at least two vertices.

Consider a vertex $u\in W$. Each component of $T-u$ has exactly one neighbor of $u$ in $T$. There is one because $T$ is connected, and two would create a cycle. Let $D$ be one such component's vertex set. The sets $D$ and $W\setminus D$ are both proper and nonempty. The latter consists of $u$ together with the other components of $T-u$, so each set induces a connected subgraph in $H$. By minimality of $W$ each set has weight at most one. Their weights sum to at least two, making each weight exactly one and the total weight exactly two. Summing the weights of the components of $T-u$ gives

$$
 \deg_T(u)=2-\omega(u).
$$

In particular, for $u\in S:=U\cap W$ this degree is $b_u+1\le p+b_u=r_u$.

Let $L=V\cap W$. When choosing the $r_u$ red edges to $V$ from $u\in S$, include every edge of $T$ at $u$. The degree bound and $r_u\le d_V(u)$ allow this. For $u\in U\setminus S$, make any choice of $r_u$ such edges. All tree edges have their ends in $S$ and $L$. The union $N_R(S)\cap V$ of the red neighborhoods of the vertices in $S$ on the $V$ side therefore satisfies

$$
\begin{aligned}
 |N_R(S)\cap V|
 &\le |L|+\sum_{u\in S} r_u - |E(T)|\\
 &=p|S|+\sum_{u\in S}b_u-|S|+1\\
 &\le p|S|-1.
\end{aligned}
$$

Here each red edge outside $T$ contributes at most one additional vertex, $T$ has $|S|+|L|-1$ edges, and the weight of $W$ is at least two.

If there were $n$ disjoint red stars, each would contain a vertex of $U$, and since $|U|=n$ each star would contain exactly one vertex of $U$ and each vertex of $U$ would lie in exactly one star. By the observation before the case analysis, the star containing $u\in S$ has all its $p$ edges at $u$ with other ends in $V$, so it uses $p$ distinct red neighbors of $u$ in $V$, with disjoint neighbor sets across the stars. This would require at least $p|S|$ vertices in $N_R(S)\cap V$, contrary to the bound. The coloring also avoids the blue star, proving the lower bound for every connected host with fewer than $n(m+p)-1$ edges. Together with the upper witness this proves the theorem and gives $c=5$. $\square$

## Relation to the source and prior work

The source's lower-bound proof splits on $t=|U|$. Its quadratic threshold enters directly only in its Case 2 ($t\ge n+1$), where the proof uses $e\ge tm-\binom{t}{2}$. Its Case 1 ($t\le n-1$) uses a vertex-cover coloring. Its Case 3 ($t=n$) uses induction on $n$, a minimal counterexample, and tree peeling, and needs the threshold only through the induction hypothesis for smaller $n$. Our argument for $t>n$ couples the coloring with the number of red stars that can use a single high-degree vertex. The edge count can then charge strong-to-low edges in full and bound the correction using only weak vertices. The direct weighted-tree argument above also gives a self-contained treatment of the exceptional case. This proves the exact Ramsey value under a threshold linear in $n+p$. We have not tried to optimise the constant $5$. Some lower bound on it is necessary: by exhaustive search, $\hat r_c(2K_2,K_{1,2})=4<5$, as $C_4\to(2K_2,K_{1,2})$, so no constant $c\le 2/3$ works. [arXiv v1](https://arxiv.org/abs/2404.03175) · [Journal version](https://doi.org/10.61091/jcmcc126-05)

The preprint has a single arXiv version (4 April 2024). The journal version still states the linear threshold as open (Conjecture 1.3). As of November 2026 we found no work citing the source that addresses the conjecture, and no resolution in the public formalization archives and literature searches we checked. The closest results we know concern the unrestricted (not necessarily connected) size Ramsey number of star forests. [Unrestricted star-forest problem](https://arxiv.org/abs/2111.02065)

## Formal verification

`StarRamsey.connectedRamsey_upper` constructs an attaining connected host and `StarRamsey.connectedRamsey_lower` rules out all smaller connected hosts. `StarRamsey.connectedRamsey_eq_five` combines these facts, and `StarRamsey.mathdb_362603` supplies the real-valued existential witness. The finite neighborhood counts, component contraction, weighted tree lemma, and cardinality obstruction all occur in Lean. The appendix contains the complete source in import order. The modules compile with Lean 4.34.1 and Mathlib, pass the standalone kernel checker, and the endpoint depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Reference

Fanghua Guo, Yanbo Zhang, and Yunqing Zhang. *Matching-star size Ramsey numbers under connectivity constraint*. Journal of Combinatorial Mathematics and Combinatorial Computing 126 (2025), 93–100. [Preprint](https://arxiv.org/abs/2404.03175) · [Journal article](https://doi.org/10.61091/jcmcc126-05)
