# A 34-vertex counterexample to Yancey's tree conjecture for variance-optimal functions

A tree on 34 vertices admits a function satisfying the unit edge constraints whose uniform variance is $14892/34^2$. Every feasible function whose absolute differences from a vertex equal the corresponding graph distances has variance at most $14888/34^2$. A maximum exists, so no variance-optimal function on this tree has a centre. This refutes Conjecture 1.4 of Yancey (MathDB 336183) and the uniform-distribution specialization of Lemma 19 of Farhadi, Louis, Singh and Tetali.

## 1. Source definitions and conjecture

Yancey defines the optimization on “uniform probabilities over the vertex set of a graph $G$ equipped with functions $X : V(G) \to \mathbb R$ that are Lipschitz with respect to the standard graph distance in $G$.” The source then states:

> We use the notation from [6] that $c(G)=\max_X\sqrt{\operatorname{Var}(X)}$, where $X$ is taken over Lipschitz functions on $V(G)$. This notation is not consistent with [2, 35]. We will call a function $X$ variance-optimal if $X$ is Lipschitz and $\operatorname{Var}(X)=c^2(G)$.

[Matthew P. Yancey, *Probabilistic and Geometrical Applications to Graph Theory*, §1.1, p. 3](https://arxiv.org/pdf/1705.09725#page=3)

Here the graph distance $d_G(u,v)$ is the minimum number of edges of a walk from $u$ to $v$. On a connected graph, the graph-metric constraint $|X(u)-X(v)|\le d_G(u,v)$ is equivalent to $|X(u)-X(v)|\le 1$ on each edge. One direction uses distance one on edges. The other sums the inequalities along a shortest walk. With $n=|V(G)|$, the uniform variance is
$$
\operatorname{Var}(X)=\frac{1}{n}\sum_u X(u)^2-
   \left(\frac{1}{n}\sum_u X(u)\right)^2.
$$
In Lean, the maximum is expressed by feasibility and comparison with every feasible function. The following definitions from the appendix instantiate the source definitions above. The proof `EdgeLipschitz.metric` and its converse `LipschitzOn.edge` relate the two forms of feasibility.

```lean
def LipschitzOn {V : Type} (G : SimpleGraph V) (X : V → ℝ) : Prop :=
  ∀ u v, |X u - X v| ≤ (G.dist u v : ℝ)

def EdgeLipschitz {V : Type} (G : SimpleGraph V) (X : V → ℝ) : Prop :=
  ∀ u v, G.Adj u v → |X u - X v| ≤ 1

noncomputable def variance {V : Type} [Fintype V] (X : V → ℝ) : ℝ :=
  (∑ v, X v ^ 2) / (Fintype.card V : ℝ) -
    ((∑ v, X v) / (Fintype.card V : ℝ)) ^ 2

def VarianceOptimal {V : Type} [Fintype V] (G : SimpleGraph V) (X : V → ℝ) : Prop :=
  LipschitzOn G X ∧ ∀ Y, LipschitzOn G Y → variance Y ≤ variance X

def IsPathGraph {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.pathGraph (Fintype.card V))

def CentredAt {V : Type} (G : SimpleGraph V) (X : V → ℝ) (r : V) : Prop :=
  ∀ u, |X u - X r| = (G.dist u r : ℝ)

def YanceyConj14 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → ∀ X, VarianceOptimal T X →
      ∃ r, CentredAt T X r ∧ (¬ IsPathGraph T → 3 ≤ T.degree r)

theorem mathdb336183 : ¬ YanceyConj14
```

The single-witness form `∃ r, CentredAt T X r ∧ (¬IsPathGraph T → 3 ≤ T.degree r)` is logically equivalent to the source's two clauses.

The conjecture reads, verbatim:

> **Conjecture 1.4.** Let $X$ be a variance-optimal function over a tree $T$. There exists a vertex $r$ such that for all vertices $u\in V(T)$, we have that $|X(u)-X(r)|=d(u,r)$. Moreover, if $T$ is not a path, then we may choose $r$ such that $d(r)\geq 3$.

[Conjecture 1.4, p. 5](https://arxiv.org/pdf/1705.09725#page=5)

Here $d(r)$ denotes the degree, as elsewhere in the source (e.g. "because $d(v)\ge3$" in the proof of Theorem 3.20). A tree is a connected acyclic simple graph, and a path graph has exactly the edges between consecutive vertices in some ordering. Call $X$ *centred* at $r$ when the displayed equality holds for all $u$. The conjecture asserts a centre for every optimum and, for a non-path tree, a centre of degree at least three. The latter clause still requires the same centring equality.

## 2. The tree and a feasible score

The vertices are $0,1,\ldots,33$. For each $i>0$, join $i$ to its parent $p_i$ in the following list, which starts at vertex 1.

```text
0 0 2 0 1 5 2 4 7 3 7 8 7 11 14 8 10 17 9 9 1 18 16 15 17 21 20 22 15 25 24 30 26
```

These are all the edges. Each parent has a smaller label, so every vertex is connected to 0 by its parent chain. In a simple cycle the largest label would have two distinct neighbours with smaller labels. Its parent is its only neighbour with smaller label, so the graph is a tree.

For a real function $g$ on this tree set
$$
E(g)=34\sum_u g(u)^2-\left(\sum_u g(u)\right)^2
    =34^2\operatorname{Var}(g).
$$
Expanding gives the translation-invariant expression $E(g)=\sum_{u<v}(g(u)-g(v))^2$. Take the following function $f$, with entries from vertex 0 to vertex 33.

```text
0 1 -1 -2 1 2 3 -2 2 -3 -3 -3 3 -1 -4 -5 3 -4 -5 -4 -4 2 -6 4 -6 -5 3 -5 -7 -6 -6 -7 -7 4
```

Each difference $f(i)-f(p_i)$ has absolute value one. The sum of the entries is $-68$ and the sum of their squares is $574$. Thus $f$ is feasible and $E(f)=34\cdot574-68^2=14892$.

## 3. Bounding all centred functions

Fix a vertex $r$ and a feasible function $g$ centred at $r$. Translate $g$ to have $g(r)=0$. Then $g(u)=\pm d_T(u,r)$ for each $u\ne r$. Orient the tree away from $r$, so every edge joins a vertex to a vertex one step farther from $r$. The distances on an edge disjoint from $r$ are both positive. Opposite signs on the two endpoints would make their absolute difference at least three, contradicting feasibility. The sign is therefore constant on each component $B$ after deleting $r$.

Put $s_B=\sum_{u\in B}d_T(u,r)$, $Q_r=\sum_u d_T(u,r)^2$, and $L_r=\min_{\varepsilon_B\in\{-1,1\}}|\sum_B\varepsilon_Bs_B|$. The square sum of $g$ is $Q_r$ and its sum is one of the signed sums used to define $L_r$. Consequently $E(g)\le 34Q_r-L_r^2$.

To reproduce a row, start a traversal from each neighbour of $r$ at depth 1. Process a vertex at depth $h$ by adding $h$ to its component's sum and $h^2$ to $Q_r$. Visit all neighbours other than the predecessor at depth $h+1$. Starting with $S=\{0\}$, replace $S$ by $\{t+s_B,t-s_B:t\in S\}$ for each component, then take $L_r=\min_{t\in S}|t|$. For example, the three component sums at $r=2$ are $40,40,36$. The first two contribute $-80$, $0$, or $80$ to the signed sum, so adjoining $\pm36$ gives $L_2=36$ and $34\cdot476-36^2=14888$.

| Root | Component distance sums | Square sum $Q_r$ | Least absolute sum $L_r$ | Score bound |
|---:|:---|---:|---:|---:|
| 0 | 98, 15, 13 | 582 | 70 | 14888 |
| 1 | 139, 6, 3 | 808 | 130 | 10572 |
| 2 | 40, 40, 36 | 476 | 36 | 14888 |
| 3 | 105, 27 | 598 | 78 | 14248 |
| 4 | 142, 8 | 816 | 134 | 9788 |
| 5 | 177, 1 | 1126 | 176 | 7308 |
| 6 | 210 | 1512 | 210 | 7308 |
| 7 | 98, 19, 8, 1 | 582 | 70 | 14888 |
| 8 | 172, 3, 1 | 1118 | 168 | 9788 |
| 9 | 148, 3, 1 | 836 | 144 | 7688 |
| 10 | 131, 19 | 788 | 112 | 14248 |
| 11 | 135, 13 | 792 | 122 | 12044 |
| 12 | 208 | 1500 | 208 | 7736 |
| 13 | 158 | 864 | 158 | 4412 |
| 14 | 164, 8 | 1070 | 156 | 12044 |
| 15 | 194, 3, 1 | 1416 | 190 | 12044 |
| 16 | 205, 1 | 1492 | 204 | 9112 |
| 17 | 158, 6, 6 | 1046 | 146 | 14248 |
| 18 | 195, 3 | 1396 | 192 | 10600 |
| 19 | 184 | 1170 | 184 | 5924 |
| 20 | 181, 1 | 1162 | 180 | 7108 |
| 21 | 173, 3 | 1114 | 170 | 8976 |
| 22 | 227, 1 | 1814 | 226 | 10600 |
| 23 | 238 | 1934 | 238 | 9112 |
| 24 | 227, 1 | 1834 | 226 | 11280 |
| 25 | 195, 3 | 1396 | 192 | 10600 |
| 26 | 205, 1 | 1488 | 204 | 8976 |
| 27 | 214 | 1556 | 214 | 7108 |
| 28 | 260 | 2300 | 260 | 10600 |
| 29 | 230 | 1842 | 230 | 9728 |
| 30 | 227, 1 | 1814 | 226 | 10600 |
| 31 | 260 | 2320 | 260 | 11280 |
| 32 | 260 | 2300 | 260 | 10600 |
| 33 | 238 | 1930 | 238 | 8976 |

The largest bound is $14888$, at roots 0, 2 and 7. Every feasible centred function therefore has score strictly below the feasible score $14892$.

To see that a variance-optimal function exists, restrict to feasible functions with $g(0)=0$. Their coordinate bounds follow from $|g(u)|\le d_T(u,0)\le33$. This set is nonempty, since it contains zero, and is closed in $[-33,33]^{34}$, since it is defined by finitely many continuous inequalities and one equality. The continuous score attains a maximum there. Every feasible function can be translated into this set without changing its score, so this gives a global variance optimum. Every optimizer has score at least $14892$, and hence none can be centred at any vertex.

Thus the first clause of Conjecture 1.4 fails on this tree. Since the conjecture is the conjunction of that clause with the degree-three refinement on non-paths, the failure of the first clause refutes the entire conjecture.

## 4. The error in Lemma 19

In Lemma 19, Farhadi, Louis, Singh and Tetali claim that an optimum for the spread constant on a tree has a vertex $v$ with $|y_w-y_v|=d_G(w,v)$ for all $w$. For unit edges and the uniform vertex distribution, the spread objective and feasibility coincide with those in §1. The counterexample above therefore disproves Lemma 19 as stated. The proof of their Theorem 18 uses Lemma 19. That proof is therefore incomplete as written. We do not claim that Theorem 18 is false. The same argument appears in arXiv v2 (Lemma 19, p. 12) and as Lemma 5.3.7 (pp. 173–175) of Farhadi's thesis, where it is used for Theorem 5.3.6. [Farhadi–Louis–Singh–Tetali, *λ∞ & Maximum Variance Embedding: Measuring and Optimizing Connectivity of A Graph Metric*, §3.2, Lemma 19 and Theorem 18, pp. 17–18](https://arxiv.org/pdf/2003.05582v3#page=18) [Farhadi's thesis](https://repository.gatech.edu/bitstreams/c32ae6cf-ee29-4a46-8d3b-d974cb104576/download)

The final step of the lemma's proof first computes the change in variance from mirroring both subtrees, then says that one can “reverse the effect of either by simply negating $\alpha$ or $\beta$ in the resulting formula.” In its notation the initial means of $A,B,C$ are $-\alpha,-d+\beta,\mu_C$, and the masses are $\pi_A,\pi_B,\pi_C$. Reflection exchanges $-\alpha$ with $\alpha$ in $A$ and exchanges $-d+\beta$ with $-d-\beta$ in $B$. Within-part variances are unchanged by either reflection. For each pair of parts $I,J$, the contribution of the means to the overall variance is $\pi_I\pi_J(\mu_I-\mu_J)^2$, as follows by grouping terms in the weighted pairwise squared-difference formula.

Write
$$
A_0=4\pi_A\pi_Bd-4\pi_A\pi_C\mu_C,
\qquad
B_0=4\pi_A\pi_Bd+4\pi_B\pi_C(d+\mu_C).
$$
For the pair $A,B$, the squared difference initially is $(d-\alpha-\beta)^2$. Mirroring both gives $(d+\alpha+\beta)^2$, while mirroring $A$ alone gives $(d+\alpha-\beta)^2$ and mirroring $B$ alone gives $(d-\alpha+\beta)^2$. Including the pairs $A,C$ and $B,C$, the gains are therefore
$$
\begin{array}{c|c}
\text{Reflection} & \Delta\operatorname{Var}\\ \hline
\text{both} & \alpha A_0+\beta B_0\\
A\text{ alone} & \alpha A_0-4\pi_A\pi_B\alpha\beta\\
B\text{ alone} & \beta B_0-4\pi_A\pi_B\alpha\beta
\end{array}
$$
Leaving both subtrees in place gives zero. The mixed term in the single-reflection gains is absent from the proof's independent sign choice. In particular, declining a reflection does not realize the negative of a term in the double-reflection formula.

For the explicit $f$, take the path $3,2,7,13$, where the values are $-2,-1,-2,-1$. In the proof's notation this is $R_1,\dots,R_4$ with $i=1$, $j=2$, so $A$ is the component of $R_i=3$ after removing $R_{i+1}=2$ and $B$ is the component of $R_{j+2}=13$ after removing $R_{j+1}=7$. All edges are stretched, and $\alpha,\beta>0$ as the proof's first step asserts, so every hypothesis used before the final step holds. The peak is 2 and the valley is 7. Translate the peak to zero, making the valley $-1$, so $d=1$. Take $A=\{3,10,17,18,22,25,28,30,32\}$ on the 3 side of the edge $3\!-\!2$, $B=\{13\}$ on the 13 side of $7\!-\!13$, and $C$ their complement. With uniform weights, the masses are $9/34,1/34,24/34$. The translated sums on $A,B,C$ are $-36,0,2$, giving $\alpha=4$, $\beta=1$, and $\mu_C=1/12$. Hence $A_0=-9/289$, $B_0=35/289$, and $4\pi_A\pi_B\alpha\beta=36/289$. The proof claims the gain $|\alpha A_0|+|\beta B_0|=71/289$. The actual gains are $-1/289$ for both reflections, $-72/289$ for $A$ alone, and $-1/289$ for $B$ alone. These are changes in variance.

## 5. Exact computations and prior art

The support code below can also check the exact global optimum by integer dynamic programming. Fix $f(0)=0$ and use the edge increments as coordinates. The feasible domain is the cube $[-1,1]^{33}$. The pairwise formula makes $E$ strictly convex on normalized functions, because the sum of squared differences of a nonzero normalized perturbation is strictly positive. The edge increments determine the normalized function linearly and injectively. Every maximizer is therefore a vertex of the cube and uses only increments $\pm1$.

For each subtree with its root fixed at zero, retain the maximum square sum $Q$ for each attainable sum $S$. At a leaf initialize the table with $S=Q=0$. Attaching a child subtree of size $k$ at relative increment $\sigma\in\{-1,1\}$ sends its moments to $(S+\sigma k,Q+2\sigma S+k)$. Add the resulting child moments to the current moments, keeping the largest square sum at each total. At the tree root take the maximum of $34Q-S^2$, which is $14892$. This calculation confirms that the displayed $f$ is itself optimal, in addition to certifying the failure of the gain step on $f$.

```python
# p is the parent list from §2, with a dummy entry at index 0.
n = len(p)
size, tables = [1] * n, [{0: 0} for _ in p]
for i in range(n - 1, 0, -1):
    j, k = p[i], size[i]
    merged = {}
    for S0, Q0 in tables[j].items():
        for S, Q in tables[i].items():
            for sign in (-1, 1):
                total = S0 + S + sign * k
                squares = Q0 + Q + 2 * sign * S + k
                merged[total] = max(merged.get(total, 0), squares)
    size[j] += k
    tables[j] = merged
assert max(n * Q - S**2 for S, Q in tables[0].items()) == 14892
```

An exact exhaustive computation by the referee (unpublished), separate from the Lean certificate, covers every tree through order 18. Every optimum on those trees satisfies both clauses, counting functions up to translation. The sweep generates unlabelled trees by leaf attachment and deduplicates them by canonical rooted encodings at their tree centres. It counts optimal edge-sign assignments by keeping counts of ties in the moment recurrence. Separately, it enumerates the centred sign assignments and deduplicates their normalized functions, also counting those with a centre of degree at least three. The order-18 sweep covered 123,867 trees. The one-vertex case is immediate. The result leaves orders 19 through 33 open for the minimum counterexample.

The closest prior results concern different structural conclusions or assert an affirmative answer. The Alon–Boppana–Spencer result quoted as Yancey's Theorem 1.3 gives signed distances to a set at the central level. Yancey's Lemma 2.10 gives unimodality on hairs. The affirmative claim in Farhadi–Louis–Singh–Tetali is addressed in §4. We checked the arXiv version histories, the thesis, citing work (Semantic Scholar, November 2026), searches for errata, and public problem and solution registries. This bounded search found no matching public refutation or erratum. [Yancey, §1.1 and Lemma 2.10](https://arxiv.org/abs/1705.09725) [Farhadi–Louis–Singh–Tetali, arXiv version history](https://arxiv.org/abs/2003.05582)

## 6. Formal certificate

The accompanying Lean sources use `SimpleGraph.IsTree`, `SimpleGraph.dist`, `SimpleGraph.degree`, and isomorphism with the Mathlib path graph. The branch and depth tables are finite data. For each root, Lean verifies a descending neighbour for each other vertex and checks that depth changes by at most one on each edge. The first check constructs a walk of the recorded length. The second bounds that depth by the length of every walk joining the vertex to the root. Together they identify every table entry with the graph distance. Connectedness follows from the same walks, and the certified degree sum $66$ gives the edge count $33$ and the tree property.

Lean verifies the branch labels along those descending walks and enumerates the 16 sign choices for the four slots, with unused slots allowed at roots of smaller degree. It checks the two moment tables against the certified depths, then checks each resulting integer score bound, transfers the bound to real-valued centred functions, and proves existence by compactness. The main endpoint is `Yancey.mathdb336183 : ¬ Yancey.YanceyConj14`. The exhaustive sweep through order 18 and the supplementary exact optimum computation are reported separately from the Lean theorem.
