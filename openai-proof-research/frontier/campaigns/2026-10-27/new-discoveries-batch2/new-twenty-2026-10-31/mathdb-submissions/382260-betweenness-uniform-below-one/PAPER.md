# An averaging obstruction for low-betweenness uniform graphs

## Abstract and certification status

We give a written proof of Conjecture 2 of Ghanbari, Hartman, Jelínek, Pokorná,
Šámal and Valtr: a finite connected betweenness-uniform graph of common
betweenness below one has a complement consisting of equally sized stars.
The proof replaces an exact uniformity calculation by finite rational Jensen
averaging, after proving a uniform lower bound for the number of close edges.
The Lean development supplied with this manuscript proves the literal
classification theorem, including the shortest-walk and graph-structural bridges.
Its endpoint is `Betweenness.lowBUG_complement_equal_stars`; its only axioms are
`propext`, `Classical.choice`, and `Quot.sound`. No published graph lemma is
assumed as an axiom. The numerical modules use rational arithmetic throughout.

## Source, attribution, and literal statement

The primary source is B. Ghanbari, D. Hartman, V. Jelínek, A. Pokorná, R. Šámal
and P. Valtr, *Structure of betweenness uniform graphs with low values of
betweenness centrality*, arXiv:2401.00347v1, dated 30 December 2023,
[primary manuscript](https://arxiv.org/abs/2401.00347v1).
The source text read in this lane is retained in `sources/2401.00347v1.txt`.
Conjecture 2 appears on page 2; §§2.1 and 2.4 contain the definitions below.

The conjecture, with the complement overbar restored from the PDF notation, is:

> If \(G\) is a low-betweenness BUG, then its complement \(\overline G\) is a disjoint union of stars of the same size.

**The MathDB record's title is wrong.** It attributes this conjecture to
Gago–Coroničová-Hurajová–Madaras. In the source, their conjecture is the different
Former Conjecture 1 about which rational betweenness values are realizable;
the source disproves that older conjecture. The equal-star classification is
Conjecture 2 of the six authors listed above. The MathDB body has the intended
classification, so this is an attribution correction, not a change of target.
The local record was obtained by running `python3 -I ../root-intake-r60/corpus_row.py
382260` from this lane; see `sources/mathdb-382260.txt`.

## Source definitions beside the Lean definitions

The following quotations transcribe the source definitions (§2.1 and §2.4),
with mathematical notation typeset and PDF line wrapping removed:

> The betweenness centrality (or just betweenness) of a vertex \(x\in V(G)\) is defined as
> \[
> B_G(x)=\sum_{\{v,w\}\subseteq V(G)}\frac{\sigma_{vw}(x)}{\sigma_{vw}},
> \]
> where \(\sigma_{vw}\) denotes the number of shortest paths between \(v\) and \(w\) and \(\sigma_{vw}(x)\) is the number of such paths containing \(x\) as an internal vertex [3]. In particular, \(\sigma_{vw}(x)=0\) whenever \(x=v\) or \(x=w\).

> We say that a graph \(G\) is a betweenness-uniform graph (or shortly a BUG), if all its vertices have the same betweenness, that is, \(B(x)=B(y)\) for all \(x,y\in V(G)\).

> In this text, we will focus on betweenness-uniform graphs with values of betweenness smaller than 1. We call such graphs low-betweenness BUGs.

> Let \(H=(V,E)\) be a graph. We say that a vertex \(v\in V\) is close to an edge \(e=xy\in E\), if \(v\) is adjacent to at least one endpoint of \(e\); in particular, the two endpoints \(x\) and \(y\) of \(e\) are close to \(e\).

The source calls the vertex and edge closeness sets \(C_H(e)\) and \(C_H(v)\),
and explicitly identifies \(C_H(xy)=N_H(x)\cup N_H(y)\). Its weight and
co-betweenness definitions are
\[
 w_H(e)=\frac1{n-|C_H(e)|},\qquad
 \operatorname{co}B_H(x)=\sum_{e\in C_H(x)}w_H(e).
\]
It explicitly leaves the weight undefined when the edge is close to every
vertex. Lean's rational expression is total; `pole_lt_of_diameterTwo` proves
that this exceptional denominator never occurs in the classification proof.
The guard `full_close_edge_guard` checks the exceptional case separately.

Here are the corresponding literal Lean definitions (namespace `Betweenness`):

```lean
noncomputable def sigma (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) : ℕ := (G.finsetWalkLength (G.dist v w) v w).card
noncomputable def sigmaThrough (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w x : Fin n) : ℕ :=
  ((G.finsetWalkLength (G.dist v w) v w).filter
    (fun p => x ∈ p.support ∧ x ≠ v ∧ x ≠ w)).card
noncomputable def betweenness (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n) : ℚ :=
  ∑ v, ∑ w, if v < w then (sigmaThrough G v w x : ℚ) / sigma G v w else 0
def LowBUG (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ (∀ x y, betweenness G x = betweenness G y) ∧
    (∀ x, betweenness G x < 1)
def close (F : SimpleGraph (Fin n)) (x a b : Fin n) : Prop :=
  F.Adj x a ∨ F.Adj x b
```

The complement quantities use the following finite sets and rational weights:

```lean
def closeVertices (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (a b : Fin n) :
    Finset (Fin n) := Finset.univ.filter (fun x => close F x a b)
def pole (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (a b : Fin n) : ℕ :=
  (closeVertices F a b).card

def pairs (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ F.Adj e.1 e.2)
def closeEdges (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (x : Fin n) :=
  (pairs F).filter (fun e => close F x e.1 e.2)
def componentEdges (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) : Finset (Fin n × Fin n) := by
  classical
  exact (pairs F).filter (fun e => e.1 ∈ K.supp)

def weight (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (a b : Fin n) : ℚ :=
  1 / ((n : ℚ) - pole F a b)
def coBetweenness (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (x : Fin n) : ℚ :=
  ∑ e ∈ closeEdges F x, weight F e.1 e.2
```

Shortest walks are automatically paths; `shortest_isPath` proves that fact, so
no graph model or path-count equivalence is left outside the certificate.
`Connected` both matches the source's intended BUG convention and ensures every
shortest-walk denominator is positive (`sigma_pos`). No disconnected graph is
made low by Lean's default rational division by zero. The source's Theorem 7
explicitly concerns connected BUGs. Its assertion that zero-betweenness BUGs are
complete also forces this connected reading.

The literal conclusion retains one common existential star size:

```lean
def StarComponent (F : SimpleGraph (Fin n)) (l : ℕ) (K : F.ConnectedComponent) : Prop :=
  ∃ c ∈ K.supp, K.supp.ncard = l + 1 ∧
    ∀ u ∈ K.supp, ∀ v ∈ K.supp,
      (F.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c))
def EqualStarUnion (F : SimpleGraph (Fin n)) : Prop :=
  ∃ l : ℕ, ∀ K : F.ConnectedComponent, StarComponent F l K
```

This is an explicit description of \(K_{1,l}\) on each component, including the
isolated-vertex case \(l=0\). The proved endpoint is:

```lean
theorem lowBUG_complement_equal_stars (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : LowBUG G) : EqualStarUnion Gᶜ
```

No a priori bound on \(n\) or \(l\) is imposed. `Connected` excludes the empty
input; the singleton input and common value zero remain in the target.

## General reductions and their proofs

For clarity we give the proofs of the source reductions that matter for the
formal endpoint. The subsequent argument also cites the numbered source results
where they originally occur.

**Shortest-walk double count and sparseness (Lemma 4 and Corollary 5).**
For each shortest \(v\)-\(w\) path of length \(d\), the number of internal vertices
is \(d-1\), since its support has no repetitions. Counting pairs of a geodesic and
an internal vertex gives
\(\sum_x\sigma_{vw}(x)=(d(v,w)-1)\sigma_{vw}\).
For a connected graph the denominator is positive, so reversing the finite sums
gives \(\sum_x B_G(x)=\sum_{v<w}(d(v,w)-1)\).
Every complement edge has distance at least two and contributes at least one.
Thus \(|E(\overline G)|\leq\sum_xB_G(x)<n\) for a low BUG. These steps, including
the general geodesic double count, are proved in `BetweennessTotal.lean`.
The stronger equality characterization in the published Lemma 4 is unnecessary.

**Diameter at most two (Theorem 7).** If distinct \(a,b\) are neither adjacent
nor have a common neighbour in \(G\), then \(ab\in E(\overline G)\) and every
vertex other than \(a,b\) is adjacent in \(\overline G\) to at least one of them.
The edges incident to the two centres contain a connected spanning graph.
Consequently \(\overline G\) is connected. Sparseness makes it a tree; its
minimally connected property implies that every edge is incident to one of
\(a,b\). The neighbours of \(a\) in \(G\) therefore form a clique.
A geodesic cannot pass internally through a vertex with a clique neighbourhood:
replacing its two incident steps by the edge between its predecessor and
successor would shorten it. Hence \(B_G(a)=0\), so uniformity gives zero at every
vertex. The complement-edge bound then says that the complement has no edges,
contradicting \(ab\). This argument is fully formalized in
`BetweennessSimplicial.lean` and `BetweennessLowDiameter.lean`.

**Complement formula (Lemma 8 and Corollary 9).** In diameter at most two, a
nonedge \(ab\) has exactly one geodesic for each common neighbour. A vertex
\(x\) is internal to one of them exactly when it is adjacent to both \(a,b\).
In \(F=\overline G\), these are precisely the vertices not close to \(ab\).
Thus the geodesic count is \(n-|C_F(ab)|>0\), and
\[
 B_G(x)=\sum_{e\in E(F)}w_F(e)-\operatorname{co}B_F(x),
 \qquad w_F(e)=\frac1{n-|C_F(e)|}.
\]
All equalities and strict denominator bounds are proved in
`BetweennessCounting.lean`, `BetweennessDiameterTwo.lean`, and
`BetweennessComplement.lean`. In particular no edge receives a zero weight
through an unguarded division by zero in this application.

**Stars (Lemma 14).** Sparseness and the handshaking identity give a vertex of
degree at most one in \(F\). An isolated vertex is a singleton star component.
For a leaf \(x\) with neighbour \(y\), every edge close to \(x\) is close to
\(y\). Strict inclusion would give strictly different co-betweenness because
all weights are positive. Thus these sets are equal. Any edge close to \(y\)
then meets \(y\), since \(x\) has only that neighbour. Starting at \(y\) and
following a walk shows that its component consists of \(y\) and its neighbours,
with no edge between two of the latter. This is a star.
In a star \(K_{1,l}\), every edge is close to every vertex in that component and
to no vertex outside it. Every vertex therefore has co-betweenness
\(l/(n-l-1)\). Equality of these values forces the same \(l\) in every star
component. The singleton-graph case is handled separately. All these assertions
are proved in `BetweennessCloseOrder.lean`, `BetweennessLeaf.lean`,
`BetweennessStarExistence.lean`, `BetweennessStarValue.lean`, and
`BetweennessStarReduction.lean`.

**Component counts and the forbidden triangle.** We use a narrower
argument than the source's general uniform-component Theorem 17. Let \(H\)
be a non-star component, with \(t\) vertices and \(m\) edges. Every vertex
has degree at least two by the proved leaf reduction, so \(m\geq t\).
Partition all components into stars and non-stars, and let \(S\) be the number
of stars. Their vertex/edge counts are \(l+1,l\); all other components have
nonnegative excess. The total edge count is less than \(n\), so
\(S\geq m-t+1\). Consequently
\[
 n\geq t+(m-t+1)(l+1).
\]
This is `exotic_star_count`, proved from the component sums and handshaking.

Suppose every vertex of \(H\) is close to every edge of \(H\), and every
edge is close to every vertex. Its common co-betweenness is \(m/(n-t)\).
Equality with the star value gives
\[
 (m-l)n=m+l(m-t)>0.
\]
Hence the integer \(m-l\) is at least one, and
\(n\leq m+l(m-t)=t+(l+1)(m-t)\), contradicting the preceding count.
This is `uniform_component_impossible`, which excludes only the exact
complete-close configuration needed here.

Now let a degree-two vertex \(x\) have adjacent neighbours \(y,z\).
Its close-edge set is contained in each of theirs. Positivity and uniformity
force both inclusions to be equalities. Thus an edge incident with a neighbour
of \(y\) or \(z\) must meet \(y\) or \(z\). There are no leaves.
Following any walk from \(y\) shows that every other vertex is either
\(z\) or adjacent to both \(y,z\), and every edge meets \(y\) or \(z\).
This includes the triangle case. Every vertex is therefore close to every
edge, so the just-proved obstruction applies. This proves
`exotic_no_degree_two_triangle`, without assuming the general Theorem 17.

## Notation and published reductions

Write F for the complement of G, and n for its number of vertices. For an edge a b of F put

    p_ab = |N_F(a) ∪ N_F(b)|,        w_ab = 1/(n-p_ab).

A vertex v is close to a b when it is adjacent to at least one of its endpoints. Write C(v) for the set of such edges, and c_v=|C(v)|. For a connected component H of F, its neighborhoods and closeness sets agree with those computed in F. Its excess is

    e(H)=|E(H)|-|V(H)|.

We use the following general reductions from the source, with their hypotheses unchanged:

1. **Lemma 4, Corollary 5 and Theorem 7:** a low BUG has diameter at most two, and |E(F)|<n.
2. **Lemma 8 and Corollary 9:** all vertices of F have the same co-betweenness, namely the sum of w_ab over their close edges.
3. **Lemma 14:** F contains a star component, every component containing a vertex of degree at most one is a star, and all its star components are isomorphic to one K_(1,l).
4. **Lemma 18, first two items:** if a low BUG is a counterexample to the proposed classification, every non-star component has minimum degree at least two and has no triangle containing a vertex of degree two. These items follow in the source from Lemma 10 and Theorem 17; the latter excludes non-star uniform components.

Each reduction used here has been proved in the accompanying Lean sources; the numbered references identify its source provenance. The remainder below proves that their simultaneous consequences are impossible for a counterexample. The source's exclusions of individual star sizes (Lemmas 27–33) are **not used**.

For completeness, two elementary consequences of item 4 are worth making explicit. First p_ab>=4 for every edge of a non-star component. If both endpoints have degree two, a union of size three would give a forbidden triangle. If one has degree two and the other larger degree, a shared neighbor would again give a forbidden triangle. If both degrees are at least three, the union has size at least four, since each endpoint belongs only to the other's neighborhood.

Second,

    c_v >= 2 deg_H(v).                                      (A)

Here is the counting proof, also source Lemma 25. Assign each close edge equally among its endpoints that lie in N_H(v). For each u∈N_H(v), the edge uv contributes one to u. If deg(u)=2, its other incident edge has its other endpoint outside N_H(v), by the forbidden-triangle property, so it contributes another one. If deg(u)>=3, either some other incident edge leaves N_H(v), contributing one, or at least two other incident edges lie inside N_H(v), contributing at least one half each. Thus every u receives at least two, proving (A). This assignment counts every close edge exactly once.

## Proof

Suppose for a contradiction that G is a counterexample. Fix a non-star component H of F. Write

    t=|V(H)|,  m=|E(H)|,  e=m-t,
    c=max_(v∈H) c_v,      Δ=max_(v∈H) deg_H(v).

Then e>=0 and c>=2Δ by (A), and t>=1 because a connected component is nonempty. Any edge has pole at least four and strictly less than n, so n>4. The star-count inequality below implies n>t, and the positive-denominator star formula gives l+1<n. These are the precise bounds used in Lean.

Let l be the common number of leaves of its star components. Every vertex in a star component has co-betweenness l/(n-l-1). Therefore, by uniformity, every v in H satisfies

    q := l/(n-l-1) = ∑_(ab∈C(v)) 1/(n-p_ab).                (1)

Because p_ab>=4 and c_v>=2deg(v)>=4, the right side of (1) is at least 4/(n-4). If l<=3, its left side is at most 3/(n-4), a contradiction. Thus

    l>=4.                                                   (2)

Let S be the number of star components of F. Every such component has excess -1, while every non-star component has nonnegative excess, by its minimum degree. Since |E(F)|-n<0, integrality gives S>=e+1. Consequently

    n >= t+(e+1)(l+1).                                     (3)

We also have c>l. Indeed, if c<=l, then for every edge ab of H,

    p_ab <= deg(a)+deg(b) <= 2Δ <= c <= l.

Equation (1) would then give q<=c/(n-c)<=l/(n-l), strictly less than l/(n-l-1). This is impossible. At a vertex attaining c, the bound p_ab>=4 gives

    c/(n-4) <= l/(n-l-1).

Since c>l, this rearranges to

    n <= l+1 + l(l-3)/(c-l).                               (4)

### Uniform lower bound on each vertex's closeness

We claim that

    c_v >= l+1  for every v∈V(H).                           (5)

Suppose instead that c_v<=l for some v. If all edges close to v had p_ab<=l, (1) would give q<=l/(n-l)<l/(n-l-1). Thus there is an edge ab in H with p_ab>=l+1. In particular deg(a)+deg(b)>=l+1. The handshaking identity and minimum degree at least two yield

    2e = ∑_(u∈H)(deg(u)-2) >= deg(a)+deg(b)-4 >= l-3.       (6)

If c>=l+2, then (2),(4) imply

    2n <= l²-l+2.

On the other hand, (3),(6) give

    2n >= l²-1+2t.

Together these would imply l+2t<=3, contrary to l>=4 and t>=1. Hence c=l+1, because c and l are integers and c>l.

It follows that every edge ab of H has

    p_ab <= deg(a)+deg(b) <= 2Δ <= c=l+1.                   (7)

In (1) for the selected vertex v, there are at most l terms, each at most 1/(n-l-1). Equality with q therefore forces c_v=l and forces p_ab=l+1 for **every** edge close to v. Choose an edge vu incident with v, which exists by minimum degree. It is close to v, so

    l+1=p_vu <= deg(v)+deg(u) <= 2Δ <= l+1.

All inequalities are equalities. Since each degree is at most Δ, both degrees equal Δ=(l+1)/2. But then (A) gives c_v>=2deg(v)=l+1, contrary to c_v=l. This proves (5), including the possible equality case of (7).

### Global averaging obstruction

Put

    C=(1/t) ∑_(v∈H) c_v.

By (5), C>=l+1. Also C<=m, since a vertex is close to at most all the edges of H. Double counting pairs consisting of a vertex and an edge close to it gives

    ∑_(ab∈E(H)) p_ab = t C.                               (8)

Averaging (1) over the vertices of H and reversing the finite sums gives

    q=(1/t) ∑_(ab∈E(H)) p_ab/(n-p_ab).                      (9)

The function f(x)=x/(n-x) is convex on x<n. Apply the finite equal-weight convexity inequality to the m numbers p_ab. By (8),(9),

    q >= (m/t) f(tC/m) = C/(n-tC/m).                       (10)

No limit or analytic approximation is present. An entirely rational proof of the convexity step uses, with μ=(∑p_ab)/m, the identity

    f(x)-f(μ)-n(x-μ)/(n-μ)²
      = n(x-μ)² / ((n-x)(n-μ)²) >= 0,

and sums it over the edges. The linear terms cancel, because ∑(p_ab-μ)=0. All p_ab<=t<n, and therefore μ<n as well.

Substituting q=l/(n-l-1) in (10) and multiplying positive denominators gives

    (C-l)n <= C(l+1)-l tC/m = C(1+l e/m),                 (11)

using m=t+e. Since C>=l+1 and C<=m,

    C/(C-l) <= l+1 <= m.

Consequently (11) implies

    n <= [C/(C-l)](1+l e/m) <= m+l e = t+(l+1)e.          (12)

But (3) says n>=t+(l+1)e+(l+1), contradicting (12). Thus no counterexample exists. The complement of every low BUG is a disjoint union of stars of one common size, as asserted. ∎


## Formal coverage and sanity checks

`Betweenness.lowBUG_reduction` has the literal `LowBUG` hypothesis and proves
diameter at most two, complement sparseness, positive edge denominators, and
constant co-betweenness. `star_component_reduction` proves the three assertions
of source Lemma 14. `component_average_obstruction` combines the graph double
counts with rational Jensen and the final excess contradiction, under explicit
component-count and lower-closeness hypotheses.

`counterexample_component_data` now produces every one of these hypotheses
from `LowBUG G` and a negation of the classification. `ObstructionComponent` is
only an explicit intermediate interface; it adds no assumption to the endpoint.
`exotic_impossible` combines this construction with the averaging obstruction,
and `lowBUG_complement_equal_stars` discharges the contradiction. There are no
unproved graph obligations or hidden input certificates.

The five inherited numerical modules are unchanged target-only copies of the
proof lane's numerical development. `BetweennessParameters` proves the maximum
closeness and maximum degree bounds and `l>=4`. `BetweennessEdgeBounds` proves
the degree/excess estimate for any edge. `BetweennessClosenessLower` supplies
all of those data to `LowBUG.low_closeness_impossible`, including an incident
edge witnessing the equality-case degree bound. The result proves (5) for
every vertex. Integer-weight incidence counting in `BetweennessIncidence`
and `BetweennessLocal` proves (A): internal neighborhood incidences contribute
one and external incidences two, each close edge is counted twice, and every
neighbor contributes at least four. This is precisely twice the assignment
argument above.

`twoStars_compl_lowBUG` proves a concrete nonvacuous instance of the hypothesis.
The convention checks use the shortest-walk definition through a proved
reduction, never an assumed computation model:

* The centre of the three-vertex path has betweenness 1; doubling unordered
  pairs would make it 2.
* The complement of two copies of \(K_{1,2}\) has betweenness \(2/3\) at every
  vertex, matching the source's introductory family.
* Two isolated vertices have uniform betweenness zero but fail `LowBUG` because
  they are disconnected.
* The complement of `mixedStarsᶜ` consists of \(K_{1,0}\) and \(K_{1,1}\). It is
  componentwise a star but fails `EqualStarUnion`.
* The edge joining the centre to a leaf in \(K_{1,2}\) is close to every vertex.
  Its raw rational weight is zero, and the required strict denominator bound
  fails. The diameter-two bridge explicitly excludes this situation.

The supplied review incorrectly requested \(B_{C_5}(x)=1/2\). The correct
unordered value is 1, as certified by `cycleFive_betweenness` and
`cycleFive_not_half`. At any vertex there is exactly one nonadjacent endpoint
pair whose unique geodesic goes through that vertex. Equivalently the total
betweenness is the five complement edges, and symmetry gives 1 per vertex.
This corrects a sanity example in the review, not the target conjecture.

## Significance and prior-art limits

The new written argument extends the source's uniform-component excess
calculation to arbitrary components by averaging \(p/(n-p)\). Its essential
additional ingredient is the all-vertex bound \(c_v\geq l+1\), including the
maximum-closeness equality case. Jensen alone does not supply that bound.
The independent review re-derived the inequalities and found no gap, but judged
significance a close call: the extension uses elementary tools and might be
regarded by a specialist as natural. The source's authors nevertheless left
the full conjecture open after a substantial star-size case analysis. No claim
of established literature novelty follows merely from the MathDB open label.

The final-check refresh on 20 November 2026 read the live arXiv v1 definitions,
Conjecture 2 and the relevant reductions. The abstract page still lists only v1.
The Discrete Applied Mathematics article, DOI
[10.1016/j.dam.2026.07.018](https://doi.org/10.1016/j.dam.2026.07.018),
395 (2026), 19–34, still identifies Conjecture 2 as open in its indexed publisher
introduction and conclusion. Direct full-text access returned 403; only the
publicly indexed preview was read. The journal statement adds “at least two”
star components. For connected G on at least two vertices this follows from the
classification: a single spanning star in the complement would leave its centre
isolated in G. The singleton case is covered by the arXiv/MathDB formulation,
not by that added journal wording. The source explicitly allows l=0, including
edgeless complements of complete graphs, as well as l=1.

Fresh exact computation covered every connected graph on one through seven
vertices up to isomorphism (996 graphs in the NetworkX graph atlas). For every
vertex, independent simple-path enumeration and a transcription enumerating all
walks of length dist gave identical rational values. The ten low BUGs were
K_n for 1<=n<=7, the complements of 2K_(1,1) and 3K_(1,1), and the complement of
2K_(1,2). Their common values were respectively 0, 1/2, 1/2 and 2/3. Every
complement passed the literal common-size/centre adjacency test. This is a
sanity check, not the proof. The script and full graph certificates are in the
final-check lane's `enumerate.py` and `enumeration.json`.

The final-check search found no relevant hit in the local Principia, mio-qwq,
omega or openai/math archives, or in the two global GitHub code searches.
Omega issue and PR searches for the source id were empty; the phrase search
returned issue 26152 and PRs 15442 and 12190, whose bodies concern unrelated
problems. Semantic Scholar returned five citing titles; relevant passages in
Madaras–Paralič, *Betweenness centers of graphs* (arXiv:2609.09342), and
Pidnebesna–Hartman–Pokorná–Trlifaj–Hlinka, *Graphlets as structural fingerprints
of complex networks* (arXiv:2609.17445), do not resolve this classification.
The latter discusses the broader classification as ongoing. OpenAlex returned
the source metadata but refused its citing-list query because the shared daily
budget was exhausted. SSRN returned 403. The bounded search does not certify
exhaustive novelty; full journal text remains unread. Closest prior work is the
source's uniform-component exclusion (arXiv Theorem 17; journal Theorem 19) and
its 9/10 classification.

## References and reproducibility

The primary source and numbered results are identified above. The proof-lane source is
`../t1-pool025-proof-sol61-20261120-r1/PROOF-382260.md`; the independent review is
`../t1-prelean-X24-opus-20261120-r1/REVIEW-382260.md`. The full checked development
is reproduced in `LEAN-SOURCE-APPENDIX.md`. See `REPORT.md` for exact proved
statements, pinned dependencies, axiom reports and replay receipts.
