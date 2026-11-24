# A counterexample to the minimum-fort-size conjecture for marginal observance

**Abstract.** We construct a connected graph on 25 vertices with minimum fort size 4 and power domination number at least 3. The largest observed sets with one and two sensors have sizes 11 and 14, respectively. The marginal observance at the second sensor is therefore 3, refuting Conjecture 4.1 of Bjorkman, English and Koch (MathDB 372803). The graph uses two copies of a five-line subconfiguration of the Fano plane and a common hub. No claim of minimum counterexample order is made.

## Statement and definitions

Bjorkman, English and Koch state Conjecture 4.1 as follows, with $\underline f$ denoting the minimum fort size. [*Cost-Benefit Analysis for PMU Placement in Power Grids*, arXiv:2601.19775v1, §4](https://arxiv.org/pdf/2601.19775v1#page=22)

> **Conjecture 4.1.** Let $G$ be a graph. If $\underline f(G)\geq 4$, then $\mathrm{MObs}(G;i)\geq 4$ for all $i\in[\gamma_P(G)]$.

The MathDB record reads as follows.

Let $G$ be a graph. Write $\underline{f}(G)$ for the minimum fort size of $G$, let $\mathrm{MObs}(G;i)$ denote the marginal observance at step $i$, and let $\gamma_P(G)$ denote the power domination number. For a positive integer $k$, write $[k]=\{1,\ldots,k\}$. **Minimum-fort-size conjecture.** If

$$
\underline{f}(G)\geq 4,
$$

then

$$
\mathrm{MObs}(G;i)\geq 4
$$

for all $i\in[\gamma_P(G)]$. This asks whether the relationship between minimum fort size and marginal observances established for smaller minimum fort sizes extends to minimum fort size at least four; its status is not resolved in the source.

The source definitions are quoted below with mathematical notation typeset. The corresponding declarations are in [the Lean source appendix](LEAN-SOURCE-APPENDIX.md).

**Observed set.** Section 1.1 defines the process and its output.

> 1. (Domination Step) Given the initial placement $S$, let $B := N[S]$.
> 2. (Zero Forcing Step) If there exists a vertex $x\in B$ with a single neighbor $y\in V(G)\setminus B$, then add $y$ to $B$. In this manner, the vertex $x$ forces $y$. Repeat this step until no such vertex $x\in B$ with a single neighbor $y\in V(G)\setminus B$ exists.
>
> We call the final set $B$ after performing the power domination process, starting from initial sensor placement $S$, the observed set and denote it with $\mathrm{Obs}(G;S)$.

Lean uses `initial G S = S ∪ S.biUnion (fun x => G.neighborFinset x)` for $N[S]$. The rule `CanForce G B x y` means `x ∈ B ∧ G.neighborFinset x \ B = {y}`. The set `obsClosure G S` is the intersection of all `Closed G` supersets of `initial G S`. Here `Closed` means every observed vertex has a number of unobserved neighbors different from one. The equivalence with the sequential definition is proved below and in Lean.

**Maximum observance and power domination number.** Section 1.1 gives the formula and then the minimum.

> $\displaystyle \operatorname{maxObs}(G;k):=\max_{S\in\binom{V(G)}k}|\mathrm{Obs}(G;S)|.$
>
> If $\mathrm{Obs}(G;S)=V(G)$, then $S$ a power dominating set. The size of a minimum power dominating set is the power domination number and is denoted by $\gamma_P(G)$.
>
> The power domination number $\gamma_P(G)$ is the smallest $k$ such that $\operatorname{maxObs}(G;k)=|V(G)|$.

Lean takes the supremum of `(obsClosure G S).card` over `Finset.univ.powersetCard k` in `maxObs G k`. The placement family is nonempty for $0\le k\le |V(G)|$, so the supremum is attained by `maxObs_attained`. The definition `IsPowerDominatingSet G S` is `obsClosure G S = Finset.univ`. Lean proves `maxObs_eq_order_iff` for admissible $k$ and uses `Nat.find` in `γP G`. The full vertex set supplies a placement attaining the graph order.

**Marginal observance.** Section 3.1 gives the following formula.

> $\displaystyle \mathrm{MObs}(G;k):=\operatorname{maxObs}(G;k)-\operatorname{maxObs}(G;k-1).$

Lean defines `MObs G i` as this difference with the two counts cast to integers. The quantified index bounds in the endpoint are `1 ≤ i` and `i ≤ γP G`.

**Fort and minimum fort size.** Section 1.2 gives the following definitions.

> A fort in a graph $G$ is a subset $F\subseteq V(G)$ with the property that there does not exist a vertex $x\in V(G)\setminus F$ with a exactly one neighbor in $F$.
>
> We define the minimum fort number of the graph $G$, $\underline f(G)$ to be the size of the smallest fort in $G$.

The source uses forts as nonempty sets, as is implicit in its minimum-size discussion and in Lemma 3.4. Lean makes this condition explicit in `IsFort G F := F.Nonempty ∧ ∀ x ∉ F, (G.neighborFinset x ∩ F).card ≠ 1`. The definition `minFort G` takes the infimum of the cardinalities of all forts. It is attained on every nonempty graph by `minFort_attained`. The empty graph uses $+\infty$ for the empty infimum and has $\gamma_P=0$, so it has no index in the conjecture. [Bjorkman, English and Koch, §§1.1–1.2, 3.1–3.2](https://arxiv.org/pdf/2601.19775v1)

## Construction

**Theorem.** There is a connected simple graph $G$ of order 25 with
$$
\underline f(G)=4,\qquad
\operatorname{maxObs}(G;1)=11,\qquad
\operatorname{maxObs}(G;2)=14,\qquad
\gamma_P(G)\ge 3.
$$
In particular, $\mathrm{MObs}(G;2)=3$.

**Proof.** Start with the Fano plane whose points are the residues modulo 7 and whose lines are $j+\{0,1,3\}$ for $j\in\{0,\ldots,6\}$. Retain the lines with $0\le j\le 4$. Use the incidence graph of this configuration as one copy. Label the points $1,\ldots,7$ by adding one to their residues and label the retained lines $8,\ldots,12$ in increasing order of $j$. This gives the incidence table below.

| Line | Points |
|---:|:---|
| 8 | 1, 2, 4 |
| 9 | 2, 3, 5 |
| 10 | 3, 4, 6 |
| 11 | 4, 5, 7 |
| 12 | 1, 5, 6 |

Take two disjoint copies of this incidence graph and add a vertex $h$ adjacent to the ten line vertices. These are all the edges. The Lean graph labels the hub by 0, and the second copy adds 12 to each nonzero label. The graph is simple and connected because each point is on a retained line and every line is adjacent to $h$.

Two distinct lines share at most one point. Indeed, the six ordered differences of distinct elements of $\{0,1,3\}$ are all distinct modulo 7. It follows also that two distinct points lie together on at most one retained line.

### Minimum fort size

Suppose $F$ is nonempty with $|F|\le 3$. If $F$ contains a line $L$, write $t$ for the total number of selected lines in both copies. Each of the other $t-1$ lines shares at most one point with $L$, so at least $4-t$ points of $L$ have exactly one neighbor in $F$, namely $L$. A fort would have to contain all these points. The number of selected vertices available for points is at most $3-t$, which rules this out.

If $F$ contains the hub and no lines, it contains at most two points. Each point lies on at most three of the ten lines, so some unselected line has just the hub as a neighbor in $F$.

It remains to consider sets consisting only of points. Consider a copy containing at least one selected point. If point 4 or point 5 is selected in that copy, its three lines cannot all meet other selected points. Each of the at most two other selected points shares at most one of its lines. The line that has no other selected point violates the fort condition. With points 4 and 5 excluded, point 7 cannot be selected either, since line 11 would then contain just that point of $F$.

In the copy under consideration the selected points are now a nonempty subset of $\{1,2,3,6\}$. These four points can be read as the four edges of the cycle on line labels $8,9,10,12,8$. Point 2 joins lines 8 and 9, point 3 joins 9 and 10, point 6 joins 10 and 12, and point 1 joins 12 and 8. A nonempty proper subset of the edges of a cycle has a vertex incident to exactly one selected edge, where a selected and an unselected edge meet. Since at most three points are selected, that vertex is an unselected line with just one neighbor in $F$.

Thus every fort has size at least four. Taking the four points $\{1,2,3,6\}$ in the first copy gives a fort, since lines 8, 9, 10 and 12 have exactly two selected neighbors each and all other outside vertices have zero. This establishes $\underline f(G)=4$.

### A closed-superset bound

Call $C$ closed if no vertex of $C$ has exactly one neighbor outside it. If the current observation set $B$ is contained in $C$ and a force from $x\in B$ adds $y\notin C$, then $x\in C$ and $y$ is the only neighbor of $x$ outside $C$. That violates closedness. Consequently any closed superset of $N[S]$ contains all vertices observed starting with $S$.

Each force adds a vertex, so the process terminates in a closed set. Each terminal set contains $N[S]$ and is contained in every closed superset of $N[S]$. It therefore equals their intersection, independently of the order of the forces.

### One sensor

A sensor at the hub immediately observes 11 vertices, the hub and all ten lines. This set is closed because each line has three unobserved point neighbors.

For a sensor $a$ in a copy, take the set $T(a)$ of local vertices given below and add the hub. Each resulting set includes the sensor and its neighbors. The last column counts the unobserved neighbors of the listed local vertices in order, using the incidence table with the hub observed. At most three lines in a row are observed, so the hub has at least seven unobserved neighbors. Thus $T(a)\cup\{h\}$ is closed and has size at most seven.

| Sensor $a$ | $T(a)$ | Numbers of unobserved neighbors |
|---:|:---|:---|
| 1 | 1, 8, 12 | 0, 2, 2 |
| 2 | 2, 8, 9 | 0, 2, 2 |
| 3 | 3, 9, 10 | 0, 2, 2 |
| 4 | 4, 8, 10, 11 | 0, 2, 2, 2 |
| 5 | 5, 9, 11, 12 | 0, 2, 2, 2 |
| 6 | 6, 10, 12 | 0, 2, 2 |
| 7 | 7, 11 | 0, 2 |
| 8 | 1, 2, 4, 8, 9, 12 | 0, 0, 2, 0, 2, 2 |
| 9 | 2, 3, 5, 8, 9, 10 | 0, 0, 2, 2, 0, 2 |
| 10 | 3, 4, 6, 9, 10, 12 | 0, 2, 0, 2, 0, 2 |
| 11 | 4, 5, 7, 11 | 2, 2, 0, 0 |
| 12 | 1, 5, 6, 8, 10, 12 | 0, 2, 0, 2, 2, 0 |

These bounds for all one-sensor placements give $\operatorname{maxObs}(G;1)=11$.

### Two sensors

If one sensor is the hub, the second sensor adds either one point or the three points of a line to the initial 11 vertices. All observed points and the hub have only observed neighbors. Every line has at least two unobserved point neighbors, except a line used as the second sensor, which has none. This follows from the intersection bound for distinct lines. The initial observation set is thus closed and its largest size is 14, attained at the hub and line 8 of the first copy.

If both sensors belong to the same copy, the whole copy together with the hub is a closed superset of their initial observation set. The hub has five neighbors outside it and no vertex of the copy has a neighbor outside. This bounds the count by 13.

If the sensors $a,b$ lie in different copies, take $C=T(a)\cup T(b)\cup\{h\}$, using each table row in its own copy. The unobserved-neighbor counts of nonhub vertices are unchanged by adding the other row. The hub has at most six observed line neighbors, hence at least four unobserved ones. Thus $C$ is closed, contains the initial observation set, and has size at most $6+6+1=13$.

These cases exhaust all two-sensor placements and give $\operatorname{maxObs}(G;2)=14$. With zero sensors the observed set is empty. The maxima for zero, one, and two sensors are therefore all strictly less than 25, and using all vertices as sensors observes the whole graph. It follows that $\gamma_P(G)\ge 3$, so $2\in[\gamma_P(G)]$ and $\mathrm{MObs}(G;2)=14-11=3$. This proves the theorem. $\square$

## Significance and prior work

The example separates the minimum fort size from an intermediate marginal observance. The last step still has the lower bound of Observation 3.7 in the source. The construction uses the intersection property of the retained lines to limit propagation after adding a line sensor to the hub. The two copies control alternative placements of the same cardinality, which must be included in the maximum. The source's square-grid example concerns the stronger bound by $\underline f(G)$ and has first marginal observance 6. [Bjorkman, English and Koch, Observation 3.7 and §4](https://arxiv.org/pdf/2601.19775v1)

The independent review on 19 November 2026 reported no matching resolution in the Principia trees, mio-qwq, the omega repository, or the OpenAI math registry. One accepted result on uniqueness for $K_{A,B}$ via fort duality concerns a different question. The arXiv record showed only v1 (27 January 2026), and Semantic Scholar displayed no citers. Web searching returned the source and talk abstracts, with the FAU abstract URLs returning 404. The related work *On fragile power domination* does not address Conjecture 4.1. A GitHub exact-ID search found RSS mirrors and a formal database record for the source's Theorem 2.7 under the key `theorem-every-set-realizable`. This was a bounded search. [Source version record](https://arxiv.org/abs/2601.19775v1), [*On fragile power domination*](https://arxiv.org/abs/2507.14620), [Formal database](https://github.com/AlexenderSokolov/cross-theory-formal-database)

## Lean certificate

The endpoint `FortObservance.minimumFort_marginalObs_refuted` is the negation of the conjecture over finite simple graphs on `Fin n` with decidable adjacency. The graph is instantiated on `Fin 25` at index 2. The declarations `terminal_run_eq_obsClosure` and `obsClosure_run` prove the sequential-forcing interpretation of `obsClosure`.

The Lean proof checks one-, two-, and three-element fort candidates by allowing repetitions in sorted triples. For each such triple the Boolean certificate finds an outside vertex whose neighbor count in the triple is one. Lean proves that this implies failure of the fort condition. For observance, every singleton and sorted pair is checked against a closed superset given by the placement cases above. The pair certificate checks the cardinality bound, containment of the initial observation set, and closedness. The placements achieving the lower bounds have initial sets of sizes 11 and 14. These finite checks use kernel reduction with `decide`, and the written proof above establishes the same quantities directly. [Lean source appendix](LEAN-SOURCE-APPENDIX.md)
