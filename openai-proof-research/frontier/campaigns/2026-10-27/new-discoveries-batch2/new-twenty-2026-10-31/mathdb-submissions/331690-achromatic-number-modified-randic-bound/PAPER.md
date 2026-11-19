# The achromatic number is at most twice the index R′ for every graph with an edge

## Abstract

For a finite simple graph $G$ let $R'(G)=\sum_{uv\in E(G)}1/\max\{d(u),d(v)\}$, the variant of the Randić index introduced by Dvořák, Lidický and Škrekovski. Wu and Elphick conjectured in 2015 that the achromatic number satisfies $\psi(G)\le 2R'(G)$ for any graph $G$. We prove the inequality for every graph with at least one edge. The proof bounds the number of colours of every complete colouring, including colourings that are not proper, so it also bounds the pseudoachromatic number. The companion Grundy-number bound follows on the same range. For both conjectures the literal inequality fails exactly on nonempty edgeless graphs, where $\psi=\Gamma=1$ and $R'=0$. The main bounds and the exact achromatic counterexample classification are formalized in Lean 4 with Mathlib. The kernel-checked endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`.

## 1. The conjecture

**Source.** Baoyindureng Wu and Clive Elphick, *Upper bounds for the achromatic and coloring numbers of a graph*, arXiv:1511.00537 (v1, 2 November 2015; v2, 5 November 2015) [WE]. Crossref metadata lists the journal version as Discrete Applied Mathematics 217 (2017) 375–380, doi:10.1016/j.dam.2016.09.005. I read both arXiv versions, fetched from arxiv.org. I did not read the journal version.

**Definitions, quoted from [WE] (identical in v1 and v2).**

* $R'$: "In 2011 Dvořák et al. introduced another variant of the Randić index of a graph $G$, denoted by $R'(G)$ … Formally, $R'(G)=\sum_{uv\in E(G)}\frac{1}{\max\{d(u),d(v)\}}$", where "$d(u)$ denotes the degree of a vertex $u$ in $G$."
* Complete colourings and $\psi$: "A complete $k$-coloring of a graph $G$ is a $k$-coloring of the graph such that for each pair of different colors there are adjacent vertices with these colors. The achromatic number of $G$, denoted by $\psi(G)$, is the maximum number $k$ for which the graph has a complete $k$-coloring. Clearly, $\chi(G)\le\psi(G)$ for a graph $G$."
* Grundy number (Section 4): "A Grundy $k$-coloring of $G$ is a $k$-coloring of $G$ such that each vertex is colored by the smallest integer which has not appeared as a color of any of its neighbors. The Grundy number $\Gamma(G)$ is the largest integer $k$, for which there exists a Grundy $k$-coloring for $G$."

**The conjecture, quoted from Section 4 of [WE].**

> **Conjecture 4.1.** For any graph $G$, $\psi(G)\le 2R'(G)$.
>
> In view of (6), a more tractable conjecture than the above is as follows.
>
> **Conjecture 4.2.** For any graph $G$, $\Gamma(G)\le 2R'(G)$.

Inequality (6) of [WE] is $\Gamma(G)\le\psi(G)$ and $\chi(G)\le\Gamma(G)\le\Delta(G)+1$.

**Conventions used here.**

1. Graphs are finite and simple. As usual for the achromatic number, the source's $k$-colourings are proper. We say a $k$-colouring *uses* all $k$ colours when the map $V\to\{1,\dots,k\}$ is surjective. For $k\ge2$, completeness already forces every colour to appear. Surjectivity matters only for $k\le 1$, and the only graph it affects is the graph with no vertices. That graph gets $\psi=0$ (Remark 3.4).
2. $R'$ is a sum over the edges. A vertex on an edge has degree at least $1$, so every summand is defined. Isolated vertices contribute nothing, and no convention for them is needed.
3. The *pseudoachromatic number* $\psi_s(G)$ is the maximum $k$ for which $V(G)$ has a surjective colouring with $k$ colours, not necessarily proper, such that every two distinct colours appear at the ends of some edge. Since a complete proper colouring is such a colouring, $\psi(G)\le\psi_s(G)$.

**Scope of the source statement.** Conjectures 4.1 and 4.2 both say “for any graph.” The bounds by $R'$ and $H$ in [WE, Theorem 1.4 and Corollaries 1.5–1.7] explicitly assume no isolated vertices. The spectral fraction $2m/\sqrt{s^+}$ in [WE, Theorem 3.1] requires at least one edge. These contexts motivate considering graphs with edges. Theorem 3.1 below covers every graph with an edge, allowing isolated vertices and multiple components. The literal conjectures fail on nonempty edgeless graphs, where $\psi=\Gamma=1$ and $R'=0$ (Proposition 3.3 and §4.7). With the zero-colour convention on the null graph, there are no other failures.

## 2. What was known

All results in this section are due to the cited authors. None of them is claimed here.

* Dvořák, Lidický and Škrekovski [DLS] introduced $R'$, and Knor, Lužar and Škrekovski [KLS] studied it further. Since $\max\{a,b\}\ge (a+b)/2\ge\sqrt{ab}$, we have $R'(G)\le H(G)\le R(G)$, where $H(G)=\sum_{uv\in E(G)}2/(d(u)+d(v))$ is the harmonic index and $R(G)=\sum_{uv\in E(G)}1/\sqrt{d(u)d(v)}$ is the Randić index. This is inequality (1) of [WE]. Bounds by $2R'$ are therefore the strongest of the three kinds.
* For graphs with an edge, Hansen and Vukičević [HV] proved $\chi(G)\le 2R(G)$, with equality for complete graphs, possibly with isolated vertices added.
* For graphs with an edge, Deng, Balachandran, Ayyaswamy and Venkatakrishnan [DBAV] proved $\chi(G)\le 2H(G)$.
* Wu, Yan and Yang [WYY] proved $\mathrm{col}(G)\le 2R(G)$ for graphs without isolated vertices.
* Wu and Elphick [WE, Theorem 1.4] proved $\mathrm{col}(G)\le 2R'(G)$ for graphs without isolated vertices and characterized equality. Corollaries 1.5–1.7 of [WE] derive $\chi\le 2R'$, $\chi_l\le 2R'$ and $\mathrm{col}\le 2H$.
* For the achromatic number, [WE] quotes Tang, Wu and Hu [TWH] for $\psi(G)\le 2R(G)$. For graphs with an edge, Theorem 3.1 of [WE] gives the spectral strengthening $\psi(G)\le 2m/\sqrt{s^+}\le 2m/\mu\le 2R(G)$. Here $m$ is the number of edges, $s^+$ is the sum of squares of the positive adjacency eigenvalues, and $\mu$ is the spectral radius.

Since $\mathrm{col}$ and $\psi$ are incomparable in general (as [WE] notes), Theorem 1.4 of [WE] does not give Conjecture 4.1. Its proof deletes a vertex of minimum degree and uses an induction on the order, and the achromatic number does not behave monotonically under such deletions.

Lin and Wang [LW, Theorem 1.7] prove $\zeta(G)\le 2R'(G)$ for graph parameters satisfying five properties. Their introduction shows that $\psi$ and $\Gamma$ both fail the minimum-degree deletion property. In their example, a clique on $q\ge2$ vertices with one leaf attached to each vertex satisfies $\Gamma=\psi=q+1=2R'$. Deleting one leaf lowers both colouring numbers to $q$. See Section 7 for the scope of the literature check.

## 3. Results

Throughout, $G$ is a finite simple graph with vertex set $V$, and $d(v)$ is the degree of $v$ in $G$. A *colouring with $k$ colours* is any map $c:V\to\{1,\dots,k\}$. It is *complete* if for all colours $i\ne j$ there are adjacent $u,v$ with $c(u)=i$ and $c(v)=j$. It is *proper* if adjacent vertices get different colours.

**Theorem 3.1.** Let $G$ have at least one edge. Let $k\ge0$, and let $c$ be a complete colouring of $G$ with $k$ colours, not necessarily proper and not necessarily surjective. Then
$$k\le 2R'(G).$$

**Corollary 3.2.** If $G$ has at least one edge, then $\Gamma(G)\le\psi(G)\le\psi_s(G)\le 2R'(G)$. In particular, Conjecture 4.1 and Conjecture 4.2 of [WE] hold for every graph with at least one edge, and hence for every graph of order $n\ge1$ without isolated vertices.

**Proposition 3.3 (exact truth set).** Let $V\ne\emptyset$. Then $\psi(G)\le 2R'(G)$ holds if and only if $G$ has an edge, and the same is true with $\psi_s$ in place of $\psi$. If $G$ has no edge, then $\psi(G)=\psi_s(G)=1$ and $R'(G)=0$.

**Remark 3.4 (the null graph).** If $V=\emptyset$, the only surjective colouring is the empty colouring with $0$ colours, so $\psi=\psi_s=0=2R'$. Hence, for graphs on $\{1,\dots,n\}$ with $n\ge0$, the literal inequality $\psi(G)\le2R'(G)$ holds exactly when $n=0$ or $G$ has an edge. The counterexamples to the unrestricted Conjecture 4.1 are exactly the edgeless graphs with $n\ge1$ vertices.

**Equality.** The bound is sharp. For $K_n$ with $n\ge 2$: $\psi=n$ and $R'=\binom n2/(n-1)=n/2$. For the star $K_{1,m}$ with $m\ge1$: $\psi=2$ and $R'=m\cdot\frac1m=1$. For $P_4$: $\psi=3$ and $R'=\frac12+\frac12+\frac12=\frac32$. Section 5 reports how often equality occurs for small orders.

## 4. Proofs

### 4.1 Ordered pairs

Let $A=\{(u,v)\in V\times V: uv\in E(G)\}$ be the set of ordered adjacent pairs. For $(u,v)\in A$ put
$$w(u,v)=\frac{1}{\max\{d(u),d(v)\}}.$$
This is defined and positive, because $d(u),d(v)\ge1$. It is symmetric: $w(u,v)=w(v,u)$.

**Lemma 4.1 (regrouping).** $2R'(G)=\sum_{(u,v)\in A}w(u,v)$.

*Proof.* The map $(u,v)\mapsto\{u,v\}$ sends $A$ onto $E(G)$. Each edge $\{u,v\}$ has exactly the two preimages $(u,v)$ and $(v,u)$, which are distinct since $u\ne v$. Both preimages carry the weight $1/\max\{d(u),d(v)\}$ of the edge. Summing over the fibres gives the claim. ∎

**Lemma 4.2 (unit charge).** If $d(u)\ge1$, then $\sum_{v:(u,v)\in A}1/d(u)=1$.

*Proof.* The sum has exactly $d(u)$ terms, each equal to $1/d(u)$. ∎

### 4.2 The threshold set

**Lemma 4.3.** Let $k,t\ge0$ be integers. There is a set $H\subseteq V$ with $|H|\le k$ and the following properties.

* (a) $d(u)\ge t$ for every $u\in H$.
* (b) $d(v)\le d(u)$ for every $u\in H$ and every $v\notin H$.
* (c) If $|H|<k$, then $d(v)<t$ for every $v\notin H$.

*Proof.* Let $S=\{v:d(v)\ge t\}$ and $m=\min\{k,|S|\}$. The family of $m$-element subsets of $S$ is finite and nonempty, since $m\le|S|$. Choose $H$ in it with $\sum_{v\in H}d(v)$ maximal. Then $|H|=m\le k$, and (a) holds because $H\subseteq S$.

For (b), suppose $u\in H$, $v\notin H$ and $d(v)>d(u)$.
* If $v\in S$, then $H'=(H\setminus\{u\})\cup\{v\}$ is an $m$-element subset of $S$. Its degree sum is $\sum_H d-d(u)+d(v)$, which is larger than $\sum_H d$. This contradicts the choice of $H$.
* If $v\notin S$, then $d(v)<t\le d(u)$ by (a), contradicting $d(v)>d(u)$.

For (c), suppose $|H|<k$. Then $m<k$, so $m=|S|$. Since $H\subseteq S$ and $|H|=|S|$, we get $H=S$. Any $v\notin H$ is then not in $S$, which means $d(v)<t$. ∎

### 4.3 Proof of Theorem 3.1 for $k\ge2$

Let $k\ge 2$ and let $c$ be a complete colouring with $k$ colours. Put $t=k-1\ge1$, and let $H$ be the set given by Lemma 4.3 for these $k$ and $t$. Write $h=|H|\le k$.

Let $U=\{1,\dots,k\}\setminus c(H)$ be the set of colours not used on $H$. Then $|c(H)|\le h$, so $|U|\ge k-h$. If $c(u)\in U$, then $u\notin H$.

For $(u,v)\in A$ define
$$L(u,v)=\frac{[u\in H]}{d(u)}+\frac{[v\in H]}{d(v)}-\frac{[u\in H][v\in H]}{t}+\frac{[h<k]\,[c(u)\in U]\,[c(v)\in U]}{t},$$
where $[P]$ is $1$ if $P$ holds and $0$ otherwise. Every denominator is positive: $d(u)\ge t\ge1$ for $u\in H$ by Lemma 4.3(a), and $t\ge1$.

**Claim 1.** $L(u,v)\le w(u,v)$ for every $(u,v)\in A$.

*Proof.* There are four cases.
* *$u,v\in H$.* Here $c(u)\in c(H)$, so $c(u)\notin U$ and the last term vanishes. Suppose $d(u)\le d(v)$. Then $w(u,v)=1/d(v)$, and $1/d(u)\le 1/t$ because $d(u)\ge t$ by Lemma 4.3(a). Hence $L(u,v)=1/d(u)+1/d(v)-1/t\le 1/d(v)=w(u,v)$. The case $d(v)\le d(u)$ is symmetric.
* *$u\in H$, $v\notin H$.* As before, $c(u)\notin U$, so $L(u,v)=1/d(u)$. By Lemma 4.3(b), $d(v)\le d(u)$, so $w(u,v)=1/d(u)=L(u,v)$.
* *$u\notin H$, $v\in H$.* Symmetrically, $L(u,v)=1/d(v)=w(u,v)$, using Lemma 4.3(b) with the roles of $u$ and $v$ exchanged.
* *$u,v\notin H$.* Here $L(u,v)=[h<k][c(u)\in U][c(v)\in U]/t$. If this is $0$, then $L(u,v)=0<w(u,v)$. If it is $1/t$, then $h<k$. Lemma 4.3(c) gives $d(u),d(v)<t$, and $d(u),d(v)\ge1$ because $uv$ is an edge. So $0<\max\{d(u),d(v)\}\le t$ and $w(u,v)\ge 1/t=L(u,v)$. ∎

By Lemma 4.1 and Claim 1,
$$2R'(G)\ \ge\ \sum_{(u,v)\in A}L(u,v)\ =\ T_1+T_2-T_3+T_4, \tag{4.1}$$
where $T_1,\dots,T_4$ are the sums over $A$ of the four terms of $L$.

**Claim 2.** $T_1=T_2=h$.

*Proof.* $T_1=\sum_{u\in H}\sum_{v:(u,v)\in A}1/d(u)=\sum_{u\in H}1=h$ by Lemma 4.2, which applies because $d(u)\ge t\ge 1$ on $H$. The swap $(u,v)\mapsto(v,u)$ is a bijection of $A$ onto itself that carries the summand of $T_2$ to the summand of $T_1$. Hence $T_2=T_1$. ∎

**Claim 3.** $t\,T_3\le h(h-1)$.

*Proof.* $t\,T_3$ is the number of pairs $(u,v)\in A$ with $u,v\in H$. For fixed $u\in H$, each such $v$ lies in $H\setminus\{u\}$, because $v\ne u$ for an edge. So for each $u$ there are at most $h-1$ such $v$, and at most $h(h-1)$ pairs in total. ∎

**Claim 4.** If $h<k$, then $t\,T_4\ge(k-h)(k-h-1)$. If $h=k$, then $T_4=0$.

*Proof.* If $h=k$, every summand of $T_4$ contains the factor $[h<k]=0$. Suppose $h<k$. Then $t\,T_4$ is the size of $B=\{(u,v)\in A: c(u),c(v)\in U\}$. Let $D=\{(i,j)\in U\times U: i\ne j\}$, which has $|U|(|U|-1)$ elements. The map $(u,v)\mapsto(c(u),c(v))$ from $B$ into $U\times U$ has image containing $D$. Indeed, for $(i,j)\in D$, completeness gives adjacent $u,v$ with $c(u)=i$ and $c(v)=j$, and then $(u,v)\in B$. Hence $|B|\ge|D|=|U|(|U|-1)$. Finally $|U|\ge k-h\ge1$, and $x\mapsto x(x-1)$ is nondecreasing for $x\ge1$, so $|U|(|U|-1)\ge(k-h)(k-h-1)$. ∎

Properness of $c$ was not used anywhere.

*Conclusion.* Multiply (4.1) by $t>0$ and use Claims 2–4.

* If $h=k$: $\;t\cdot2R'\ge 2kt-k(k-1)=2k(k-1)-k(k-1)=k(k-1)=kt$.
* If $h<k$: $\;t\cdot2R'\ge 2ht-h(h-1)+(k-h)(k-h-1)$. Expanding,
$$(k-h)(k-h-1)-h(h-1)=k^2-2kh-k+2h=(k-2h)(k-1)=(k-2h)t,$$
so $t\cdot2R'\ge 2ht+(k-2h)t=kt$.

In both cases dividing by $t>0$ gives $2R'(G)\ge k$. ∎

### 4.4 Proof of Theorem 3.1 for $k\le1$

Let $ab$ be an edge. Colour $a$ with colour $1$ and every other vertex with colour $2$. This colouring is complete. The pair $(1,2)$ is realized by $(a,b)$ and the pair $(2,1)$ by $(b,a)$, since $b\ne a$. By §4.3 with $k=2$, $2\le 2R'(G)$. Hence $k\le1<2\le2R'(G)$. ∎

### 4.5 The achromatic numbers are maxima

**Lemma 4.4.** Every finite graph has a complete proper colouring that uses all its colours.

*Proof.*
* A bijection $V\to\{1,\dots,|V|\}$ is a proper surjective colouring. Let $k_0$ be the least $k$ for which a proper surjective colouring $c$ with $k$ colours exists.
* Suppose $c$ is not complete. Then there are colours $i\ne j$ such that no edge has an end of colour $i$ and an end of colour $j$; by symmetry of adjacency the order of the ends does not matter.
* Define $c'$ by recolouring every vertex of colour $j$ with colour $i$. Then $c'$ is proper. Take an edge $uv$ with $c'(u)=c'(v)$.
  * If $c(u)=c(v)=j$, this contradicts properness of $c$.
  * If exactly one of $c(u),c(v)$ is $j$, the other is $i$, so the edge joins the classes of $i$ and $j$, contradicting the choice of $i,j$.
  * If neither is $j$, then $c(u)=c(v)$, contradicting properness of $c$.
* The image of $c'$ is $\{1,\dots,k_0\}\setminus\{j\}$. Every colour other than $j$ keeps its vertices, colour $i$ certainly occurs, and colour $j$ no longer occurs.
* Composing $c'$ with a bijection from $\{1,\dots,k_0\}\setminus\{j\}$ onto $\{1,\dots,k_0-1\}$ gives a proper surjective colouring with $k_0-1$ colours. This contradicts the minimality of $k_0$. ∎

A surjective colouring with $k$ colours has $k\le|V|$. So the set of $k$ admitting a complete proper surjective colouring is nonempty (Lemma 4.4) and bounded, and $\psi(G)$ is its maximum. Likewise $\psi_s(G)$ is a maximum, and $\psi(G)\le\psi_s(G)$.

### 4.6 Proof of Corollary 3.2

Let $G$ have an edge.
* $\psi_s(G)$ is attained by a complete colouring with $\psi_s(G)$ colours, so Theorem 3.1 gives $\psi_s(G)\le2R'(G)$, and $\psi(G)\le\psi_s(G)$.
* A Grundy colouring is proper, and a vertex of colour $j$ has a neighbour of every colour $i<j$. Given colours $i\ne j$, say $i<j$, pick a vertex $v$ of colour $j$ (the colouring uses all its colours) and a neighbour $w$ of $v$ of colour $i$. Then $(w,v)$ realizes the pair $(i,j)$ and $(v,w)$ realizes $(j,i)$. So a Grundy $k$-colouring is a complete proper $k$-colouring, and $\Gamma(G)\le\psi(G)$, which is inequality (6) of [WE].
* A graph of order $n\ge1$ without isolated vertices has an edge. ∎

### 4.7 Proof of Proposition 3.3 and Remark 3.4

Let $V\ne\emptyset$. If $G$ has an edge, the inequalities hold by Corollary 3.2.

Suppose $G$ has no edge.
* $R'(G)=0$, as an empty sum.
* The constant colouring with one colour is surjective because $V\ne\emptyset$. It is proper because there are no edges, and complete because there is no pair of distinct colours. So $\psi(G)\ge1$.
* A complete colouring with $k\ge2$ colours needs an edge between colours $1$ and $2$. So $\psi_s(G)\le1$.
* Hence $\psi=\psi_s=1>0=2R'$, and the inequality fails.

For $V=\emptyset$, a map $\emptyset\to\{1,\dots,k\}$ is surjective only for $k=0$, so $\psi=\psi_s=0=2R'$. For a nonempty edgeless graph, every vertex gets the least colour in a Grundy colouring, so $\Gamma=1>2R'=0$. On the null graph the empty Grundy colouring gives $\Gamma=0$. ∎

## 5. Numerical checks

[scripts/table331690.py](../shard007-formal-paper-331690-340121-opus-20261119-r1/331690/scripts/table331690.py) works directly from the definitions with exact rational arithmetic. For every labelled graph on $n\le6$ vertices it computes $R'$. It computes $\psi$ and $\psi_s$ by enumerating all set partitions of the vertex set, using that a colouring that uses all its colours is the same as a set partition with labelled classes. The output is in [scripts/table331690.log](../shard007-formal-paper-331690-340121-opus-20261119-r1/331690/scripts/table331690.log).

| $n$ | labelled graphs | with an edge | violations of $\psi_s\le2R'$ | $\psi=2R'$ | $\psi_s=2R'$ | $\min(2R'-\psi_s)$ | edgeless: $(\psi,\psi_s,2R')$ |
|---|---:|---:|---:|---:|---:|---:|---|
| 1 | 1 | 0 | 0 | 0 | 0 | — | (1, 1, 0) |
| 2 | 2 | 1 | 0 | 1 | 1 | 0 | (1, 1, 0) |
| 3 | 8 | 7 | 0 | 7 | 7 | 0 | (1, 1, 0) |
| 4 | 64 | 63 | 0 | 51 | 51 | 0 | (1, 1, 0) |
| 5 | 1024 | 1023 | 0 | 431 | 431 | 0 | (1, 1, 0) |
| 6 | 32768 | 32767 | 0 | 4173 | 4173 | 0 | (1, 1, 0) |

These counts agree with the independent reviewer's computation at $n=6$: 4 173 equality graphs and no violations. The computation is corroborative only. The proof and the Lean formalization do not use it.

## 6. Formal verification

### 6.1 Setting

The formalization uses Lean 4.34.1 and Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. The five modules are listed in import order in [LEAN-SOURCE-APPENDIX.md](../shard007-formal-paper-331690-340121-opus-20261119-r1/331690/LEAN-SOURCE-APPENDIX.md).

* A graph is `G : SimpleGraph V` on a finite type `V` with decidable adjacency. The `Fin n` endpoints instantiate `V = Fin n`.
* The index is `randicPrime G : ℚ`, the sum over `G.edgeFinset` of `Sym2.lift` applied to `wt G u v = 1 / ((max (G.degree u) (G.degree v) : ℕ) : ℚ)`. This is literally $\sum_{uv\in E}1/\max\{d(u),d(v)\}$, using Mathlib's `SimpleGraph.degree`.
* `IsCompleteColouring G c` for `c : V → Fin k` is the source's "for each pair of different colors there are adjacent vertices with these colors". `IsProperColouring` is properness.
* `HasCompleteColouring G k` asks for a surjective, proper, complete `c : V → Fin k`. `HasCompletePseudoColouring` drops properness.
* `achromatic G` is `Nat.findGreatest (HasCompleteColouring G ·) (Fintype.card V)`, and `pseudoachromatic` is defined the same way. These are proved to be genuine maxima (`achromatic_isGreatest`, `pseudoachromatic_isGreatest`), so the cut-off at `|V|` and the default value `0` of `Nat.findGreatest` never matter.
* `grundy G` is defined by the same bounded maximum using surjective `IsGrundyColouring` witnesses. Properness excludes the vertex's own colour from its neighbours, and the smaller-colour condition ensures every smaller colour occurs among them. Together these express the source's least-available-colour rule. A first-fit colouring in any vertex order gives a witness, and surjectivity bounds its number of colours by $|V|$.

### 6.2 Map from the proof to Lean

| Step in this paper | Lean declaration (module) |
|---|---|
| Definition of $R'$, of complete, proper and surjective colourings, $\psi$, $\psi_s$ | `wt`, `randicPrime`, `IsCompleteColouring`, `IsProperColouring`, `HasCompleteColouring`, `HasCompletePseudoColouring`, `achromatic`, `pseudoachromatic` (AchDefs) |
| Lemma 4.1 | `two_mul_randicPrime` (AchDefs) |
| $R'\ge0$; $R'=0$ for edgeless graphs | `randicPrime_nonneg`, `randicPrime_eq_zero_of_edgeless` (AchDefs) |
| Lemma 4.2 | `sum_adj_inv_degree` (AchBound) |
| Lemma 4.3 | `exists_threshold_set` (AchBound) |
| Claim 1 | `pointwise_bound` (AchBound) |
| Claims 2–4 and the conclusion of §4.3 | inside `two_le_card_bound` (AchBound) |
| §4.4 | `exists_complete_two`, `complete_colouring_le_two_randicPrime` (AchBound) |
| Lemma 4.4 and the maxima | `exists_hasCompleteColouring`, `achromatic_isGreatest`, `pseudoachromatic_isGreatest`, `achromatic_le_pseudoachromatic` (AchMain) |
| Corollary 3.2 ($\psi,\psi_s$) | `achromatic_le_two_randicPrime`, `pseudoachromatic_le_two_randicPrime`, `fin_achromatic_le_two_randicPrime`, `wuElphickConjecture41`, `wuElphickConjecture41NoIsolated`, `pseudoachromaticConjecture` (AchMain) |
| Corollary 3.2 ($\Gamma$) | `isCompleteColouring_of_isGrundy`, `grundy_le_achromatic`, `grundy_le_two_randicPrime`, `wuElphickConjecture42` (AchGrundy) |
| Proposition 3.3 | `edgeless_values`, `achromatic_le_two_randicPrime_iff`, `pseudoachromatic_le_two_randicPrime_iff`, `fin_truth_set` (AchMain) |
| Remark 3.4 | `achromatic_eq_zero_of_isEmpty`, `achromatic_randic_exact`, `literal_counterexamples`, `not_wuElphickConjecture41Literal` (AchMain) |

**Comparison with Lean.** The ordered-pair estimates and the threshold-set argument in Sections 4.1–4.7 follow Lean. Lean applies the complete-colouring bound directly to an attaining colouring for each of the two achromatic parameters, whereas §4.6 obtains the proper case through the pseudoachromatic inequality. The null pseudoachromatic value follows from the bounded maximum with cutoff $0$. The named null and unrestricted-counterexample endpoints concern the achromatic number. The route presented here differs from the discovery write-up [PROOF] in four ways.

1. The written discovery proof charges unordered edges and bounds the edges at $H$ and the edges outside $H$ separately. Here and in Lean, everything is summed over ordered adjacent pairs with the single pointwise bound of Claim 1.
2. $H$ is chosen by maximizing the degree sum over $m$-subsets of $S$, not by sorting the vertices.
3. The case $k\le1$ is reduced to $k=2$ through an explicit complete 2-colouring, instead of through $\psi\ge2$.
4. Lean quantifies over arbitrary finite vertex types and also states the `Fin n` forms.

The formal results cover exactly the ranges stated in Section 3. Nothing is proved for a smaller range.

**The conjectures as `Prop`s.** `WuElphickConjecture41` and `WuElphickConjecture42` quantify over all `n` and all `G : SimpleGraph (Fin n)` with at least one edge. Both are proved. `WuElphickConjecture41Literal` is the unrestricted form of Conjecture 4.1, refuted by `not_wuElphickConjecture41Literal` using the one-vertex edgeless graph. `achromatic_randic_exact` gives the exact truth set on `Fin n`: `n = 0 ∨ G.edgeSet.Nonempty`. `literal_counterexamples` states that the failures are exactly the edgeless graphs with `0 < n`.

### 6.3 Endpoint statements and axioms

The following is the output of compiling the final module `AchAxioms.lean` during the clean rebuild, pasted verbatim from `final-compile-AchAxioms.output.txt` without its trailing JSON receipt line:

```text
def Ach331690.wt.{u_1} : {V : Type u_1} → [Fintype V] → (G : SimpleGraph V) → [DecidableRel G.Adj] → V → V → ℚ :=
fun {V} [Fintype V] G [DecidableRel G.Adj] u v => 1 / ↑(max (G.degree u) (G.degree v))
def Ach331690.randicPrime.{u_1} : {V : Type u_1} → [Fintype V] → (G : SimpleGraph V) → [DecidableRel G.Adj] → ℚ :=
fun {V} [Fintype V] G [DecidableRel G.Adj] => ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => wt G u v, ⋯⟩ e
def Ach331690.IsCompleteColouring.{u_1} : {V : Type u_1} → SimpleGraph V → {k : ℕ} → (V → Fin k) → Prop :=
fun {V} G {k} c => ∀ (i j : Fin k), i ≠ j → ∃ u v, G.Adj u v ∧ c u = i ∧ c v = j
def Ach331690.IsProperColouring.{u_1} : {V : Type u_1} → SimpleGraph V → {k : ℕ} → (V → Fin k) → Prop :=
fun {V} G {k} c => ∀ (u v : V), G.Adj u v → c u ≠ c v
def Ach331690.HasCompleteColouring.{u_1} : {V : Type u_1} → SimpleGraph V → ℕ → Prop :=
fun {V} G k => ∃ c, Function.Surjective c ∧ IsProperColouring G c ∧ IsCompleteColouring G c
def Ach331690.HasCompletePseudoColouring.{u_1} : {V : Type u_1} → SimpleGraph V → ℕ → Prop :=
fun {V} G k => ∃ c, Function.Surjective c ∧ IsCompleteColouring G c
def Ach331690.achromatic.{u_1} : {V : Type u_1} → [Fintype V] → SimpleGraph V → ℕ :=
fun {V} [Fintype V] G => Nat.findGreatest (fun k => HasCompleteColouring G k) (Fintype.card V)
def Ach331690.pseudoachromatic.{u_1} : {V : Type u_1} → [Fintype V] → SimpleGraph V → ℕ :=
fun {V} [Fintype V] G => Nat.findGreatest (fun k => HasCompletePseudoColouring G k) (Fintype.card V)
@two_mul_randicPrime : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [inst_1 : DecidableRel G.Adj],
  2 * randicPrime G = ∑ u, ∑ v, if G.Adj u v then wt G u v else 0
@complete_colouring_le_two_randicPrime : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V)
  [inst_1 : DecidableRel G.Adj] [DecidableEq V],
  G.edgeSet.Nonempty → ∀ {k : ℕ} (c : V → Fin k), IsCompleteColouring G c → ↑k ≤ 2 * randicPrime G
fin_complete_colouring_le_two_randicPrime : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj]
  (c : Fin n → Fin k), G.edgeSet.Nonempty → IsCompleteColouring G c → ↑k ≤ 2 * randicPrime G
@achromatic_isGreatest : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
  IsGreatest {k | HasCompleteColouring G k} (achromatic G)
@pseudoachromatic_isGreatest : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
  IsGreatest {k | HasCompletePseudoColouring G k} (pseudoachromatic G)
@achromatic_le_two_randicPrime : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [inst_1 : DecidableRel G.Adj]
  [DecidableEq V], G.edgeSet.Nonempty → ↑(achromatic G) ≤ 2 * randicPrime G
@pseudoachromatic_le_two_randicPrime : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V)
  [inst_1 : DecidableRel G.Adj] [DecidableEq V], G.edgeSet.Nonempty → ↑(pseudoachromatic G) ≤ 2 * randicPrime G
fin_achromatic_le_two_randicPrime : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  G.edgeSet.Nonempty → ↑(achromatic G) ≤ 2 * randicPrime G ∧ ↑(pseudoachromatic G) ≤ 2 * randicPrime G
@edgeless_values : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [inst_1 : DecidableRel G.Adj] [Nonempty V],
  (∀ (u v : V), ¬G.Adj u v) → achromatic G = 1 ∧ pseudoachromatic G = 1 ∧ randicPrime G = 0
@achromatic_le_two_randicPrime_iff : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V)
  [inst_1 : DecidableRel G.Adj] [DecidableEq V] [Nonempty V], ↑(achromatic G) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty
@pseudoachromatic_le_two_randicPrime_iff : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V)
  [inst_1 : DecidableRel G.Adj] [DecidableEq V] [Nonempty V],
  ↑(pseudoachromatic G) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty
fin_truth_set : ∀ (n : ℕ),
  0 < n →
    ∀ (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
      (↑(achromatic G) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty) ∧
        (↑(pseudoachromatic G) ≤ 2 * randicPrime G ↔ G.edgeSet.Nonempty)
achromatic_randic_exact : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  ↑(achromatic G) ≤ 2 * randicPrime G ↔ n = 0 ∨ G.edgeSet.Nonempty
literal_counterexamples : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  ¬↑(achromatic G) ≤ 2 * randicPrime G ↔ 0 < n ∧ ∀ (u v : Fin n), ¬G.Adj u v
def Ach331690.WuElphickConjecture41 : Prop :=
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  G.edgeSet.Nonempty → ↑(achromatic G) ≤ 2 * randicPrime G
def Ach331690.WuElphickConjecture41NoIsolated : Prop :=
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  0 < n → (∀ (v : Fin n), ∃ w, G.Adj v w) → ↑(achromatic G) ≤ 2 * randicPrime G
def Ach331690.WuElphickConjecture41Literal : Prop :=
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj], ↑(achromatic G) ≤ 2 * randicPrime G
def Ach331690.PseudoachromaticConjecture : Prop :=
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  G.edgeSet.Nonempty → ↑(pseudoachromatic G) ≤ 2 * randicPrime G
wuElphickConjecture41 : WuElphickConjecture41
wuElphickConjecture41NoIsolated : WuElphickConjecture41NoIsolated
pseudoachromaticConjecture : PseudoachromaticConjecture
not_wuElphickConjecture41Literal : ¬WuElphickConjecture41Literal
def Ach331690.IsGrundyColouring.{u_1} : {V : Type u_1} → SimpleGraph V → {k : ℕ} → (V → Fin k) → Prop :=
fun {V} G {k} c => IsProperColouring G c ∧ ∀ (v : V), ∀ i < c v, ∃ w, G.Adj v w ∧ c w = i
def Ach331690.grundy.{u_1} : {V : Type u_1} → [Fintype V] → SimpleGraph V → ℕ :=
fun {V} [Fintype V] G => Nat.findGreatest (fun k => HasGrundyColouring G k) (Fintype.card V)
@grundy_le_achromatic : ∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
  grundy G ≤ achromatic G
def Ach331690.WuElphickConjecture42 : Prop :=
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj], G.edgeSet.Nonempty → ↑(grundy G) ≤ 2 * randicPrime G
wuElphickConjecture42 : WuElphickConjecture42
'Ach331690.complete_colouring_le_two_randicPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.fin_complete_colouring_le_two_randicPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.achromatic_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.pseudoachromatic_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.fin_achromatic_le_two_randicPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.fin_truth_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.achromatic_randic_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.literal_counterexamples' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.wuElphickConjecture41' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.wuElphickConjecture41NoIsolated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.pseudoachromaticConjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.not_wuElphickConjecture41Literal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.grundy_le_achromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ach331690.wuElphickConjecture42' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every endpoint depends only on `propext`, `Classical.choice` and `Quot.sound`. The source files contain no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `bv_decide` or `implemented_by`. They contain no `decide` either.

### 6.4 Build

All five modules were compiled from an empty build directory and then kernel-checked with `leanchecker`. Each module was a separate run under the runner limits: 120 s CPU, 6 GiB resident memory and 32 GiB address space, on CPUs 28–29. All ten runs exited with status 0. The record is in [REPORT.md](../shard007-formal-paper-331690-340121-opus-20261119-r1/331690/REPORT.md) and [final-rebuild.log](../shard007-formal-paper-331690-340121-opus-20261119-r1/331690/final-rebuild.log).

## 7. Limits

* **Literature search was bounded.**
  * The independent reviewer could not run web searches, because of an account usage limit. They used the OpenAlex citation graph (18 citing works of [WE]), Crossref keyword searches and arXiv abstract pages. They found no statement of $\psi\le2R'$ or $\Gamma\le2R'$ as a theorem.
  * I additionally checked Crossref metadata (bibliographic data only) for [WE], [LW], [DLS], [KLS], [HV], [DBAV], [WYY] and [TWHZ]. I did not run a new keyword search.
* **Lin–Wang 2025.** The final referee read the publisher-indexed abstract and excerpts from the introduction and §2. These establish that the hypotheses of [LW, Theorem 1.7] exclude both $\psi$ and $\Gamma$, and that the example discussed in §2 above gives equality in both bounds. [LW, §2] also reports a repair to the minimum-degree deletion lemma in [WE]. Our proof uses a different argument. The publisher returned 403 for the direct fetch, and the referee located no open full text or arXiv preprint. The referee also found no proof of either general edge-bearing bound in a bounded search of later citing work and ProbXiv. [Publisher preview](https://www.sciencedirect.com/science/article/abs/pii/S0166218X25001544).
* **Unread journal versions.**
  * I did not read the journal version of [WE] (Discrete Appl. Math. 217 (2017) 375–380). A restriction of Conjecture 4.1 there, if any, would not affect the theorem, which covers every graph with an edge.
  * I did not read the published version [TWHZ] of [TWH].
  * I did not read [DLS], [HV], [DBAV], [WYY] or [KLS]. They are cited as [WE] quotes them, with bibliographic data checked on Crossref where noted.
* **AI-produced.** The proof was found and written by AI systems. The discovery write-up came from an AI discovery lane of this campaign, the review from Claude Opus, and this formalization and paper from Claude Opus. The paper has had no human peer review. The Lean proof is the strongest available check of correctness.

## References

* [WE] Baoyindureng Wu and Clive Elphick, *Upper bounds for the achromatic and coloring numbers of a graph*, arXiv:1511.00537 (2015). Journal version (per Crossref): Discrete Applied Mathematics 217 (2017) 375–380, doi:10.1016/j.dam.2016.09.005.
* [DLS] Zdeněk Dvořák, Bernard Lidický and Riste Škrekovski, *Randić index and the diameter of a graph*, European Journal of Combinatorics 32 (2011) 434–442, doi:10.1016/j.ejc.2010.12.002.
* [KLS] Martin Knor, Borut Lužar and Riste Škrekovski, *Sandwiching the (generalized) Randić index*, Discrete Applied Mathematics 181 (2015) 160–166, doi:10.1016/j.dam.2014.08.032. [WE] lists the second author as "B. Kuzar".
* [HV] Pierre Hansen and Damir Vukičević, *Variable neighborhood search for extremal graphs. 23. On the Randić index and the chromatic number*, Discrete Mathematics 309 (2009) 4228–4234, doi:10.1016/j.disc.2008.12.022.
* [DBAV] Hanyuan Deng, S. Balachandran, S. K. Ayyaswamy and Y. B. Venkatakrishnan, *On the harmonic index and the chromatic number of a graph*, Discrete Applied Mathematics 161 (2013) 2740–2744, doi:10.1016/j.dam.2013.04.003. [WE] lists the volume as "16".
* [WYY] Baoyindureng Wu, Juan Yan and Xiaojing Yang, *Randić index and coloring number of a graph*, Discrete Applied Mathematics 178 (2014) 163–165, doi:10.1016/j.dam.2014.06.024.
* [TWH] Zixing Tang, Baoyindureng Wu and Lin Hu, *The Grundy number of a graph*, arXiv:1507.01080 (2015), as cited in [WE].
* [TWHZ] Zixing Tang, Baoyindureng Wu, Lin Hu and Manouchehr Zaker, *More bounds for the Grundy number of graphs*, Journal of Combinatorial Optimization 33 (2017) 580–589, doi:10.1007/s10878-015-9981-8 (per Crossref; not read).
* [LW] Dazhi Lin and Tao Wang, *A simplified graph parameter and its relationship to the modified Randić index*, Discrete Applied Mathematics 371 (2025) 60–64, doi:10.1016/j.dam.2025.03.030 (publisher abstract and indexed excerpts consulted).
* [PROOF] Discovery write-up `fresh-shard007-discovery-sol62-20261118-r1/PROOF-331690.md` and independent review `shard007-candidates-review-opus-20261118-r1/REVIEW-331690.md` in this campaign.
