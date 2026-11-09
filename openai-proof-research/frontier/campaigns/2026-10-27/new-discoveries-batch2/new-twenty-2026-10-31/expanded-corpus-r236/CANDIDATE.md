# CANDIDATE — MathDB 350432: proof of the Contreras-Mendoza–Hernández-Cruz uniqueness conjecture

Lane: expanded-corpus-r236 (Claude). Status: **ordinary proof complete; Lean NOT run in this lane (Claude-lane
restriction). The draft Lean in `lean-draft/` is UNCOMPILED.** No self-acceptance. Zero credit unless root accepts.

## 1. Exact target

MathDB 350432 (raw line `raw/350432.jsonl`; chunk, line and hashes in `extracted.json`):

> A cograph minimal $(\infty,k)$-polar obstruction is a cograph that is not $(\infty,k)$-polar, but whose every proper
> induced subgraph is $(\infty,k)$-polar. Its type $(c,i)$ records its number $c$ of connected components and its
> number $i$ of isolated vertices. For integers $k,c,i$ satisfying $1\le i\le c-2\le k$: there exists exactly one
> cograph minimal $(\infty,k)$-polar obstruction of type $(c,i)$.

Source: F. E. Contreras-Mendoza and C. Hernández-Cruz, *Minimal obstructions to $(\infty,k)$-polarity in cographs*,
arXiv:2104.07852 (v1 is the only version), Discrete Math. 344(7) (2021) 112407, **Conjecture 1** (Section 7). The same
statement is Conjecture 3.27 of Contreras-Mendoza's doctoral thesis (UNAM, April 2023, `sources/cm-thesis-0837616.pdf`),
which still lists it as open.

Source definitions (Section 1 of the source): an $(s,k)$-polar partition of $G$ is a partition $(A,B)$ of $V(G)$ such
that $A$ induces a complete multipartite graph with at most $s$ parts and $B$ induces a disjoint union of at most $k$
cliques with no other edges (a *cluster*). Either side may be empty. $(\infty,k)$ means there is no bound on the parts of $A$. "Exactly
one" means up to isomorphism (the source's Corollary 26 uses "up to isomorphism, this is the only ...").

What the source proves: uniqueness for $c\in\{k,k+1,k+2\}$ (Corollary 26), complete lists for $k\le 3$
(Theorems 27, 28), and a recursion (Theorem 25). The authors write (Section 7) that their techniques "might not be
enough" for the types $(c,c-1)$, $3\le c\le k-1$. The open part of the conjecture is $3\le c\le k-1$, first at $k=4$, $(c,i)=(3,1)$.

## 2. Theorem (full scope)

**Theorem.** Let $1\le i\le c-2\le k$. Up to isomorphism, the unique cograph minimal $(\infty,k)$-polar obstruction
of type $(c,i)$ is
$$P(k,c,i)\;=\;iK_1+(c-i-1)K_2+X,$$
where
* $X=K_{i,i}$ if $c=k+2$ (for $i=1$, $X=K_{1,1}=K_2$, so $P=K_1+(k+1)K_2$);
* $X=\overline{K_2}\oplus(K_2+iK_1)$ if $c=k+1$;
* $X=K_1\oplus\big((k-c+2)K_2+iK_1\big)$ if $c\le k$.

Here $+$ is disjoint union and $\oplus$ is join. For $c\in\{k,k+1,k+2\}$ this agrees with the source's Corollary 26.
The source's printed formulas lose their complement bars in text extraction; we checked them against our own exhaustive census, section 5.

## 3. Proof

All graphs are finite and simple. Write $\overline{K_a}$ for the edgeless graph on $a$ vertices. *CM* means complete
multipartite: equivalently, non-adjacency is an equivalence relation, i.e. there is no induced $K_1+K_2$. A *cluster* is a
$P_3$-free graph; $\mathrm{cl}(B)$ is its number of components (cliques). $(1,k)$-polar means that $A$ is edgeless. Both CM and cluster
are hereditary, and $\mathrm{cl}$ does not increase on induced subgraphs. Hence $(\infty,k)$- and $(1,k)$-polarity are hereditary, and
"every proper induced subgraph is polar" is equivalent to "$G-v$ is polar for every vertex $v$". Induced subgraphs of
cographs are cographs, so minimality among cographs is the same as minimality among all graphs.

**Facts.**
(F1) A CM graph with an edge is connected. (Vertices in different parts are adjacent. Two vertices of one part have a
common neighbour in another part, which exists because an edge forces at least two parts.) Hence a CM graph with an
isolated vertex, or a disconnected CM graph, is edgeless.
(F2) A graph that is both CM and a cluster is edgeless or a clique (by F1, if it has an edge it is a connected cluster).
(F3) In a join $X\oplus Y$ with $X,Y\ne\emptyset$: a cluster meeting both $X$ and $Y$ is connected, hence a clique; an
edgeless set lies inside $X$ or inside $Y$.
(F4) (Seinsche) A connected cograph on at least $2$ vertices is a join $X\oplus Y$ of two nonempty cographs. This is in
Lean Pool as `IsP4Free.not_preconnected_or_compl` (`LeanPool/StructuralGraphClasses/CographDecomposition.lean` at
01db1d70).

**Lemma 1 (clusters).** A cluster with $c\ge1$ components, $r'$ of them of order $\ge2$, is $(\infty,k)$-polar iff
$\min(r',c-1)\le k$.
*Proof.* Let $A$ be CM inside the cluster. By F2, $A$ is edgeless or a nonempty clique inside one component. If $A$ is
edgeless, each component of order $\ge2$ keeps a vertex in $B$, so $\mathrm{cl}(B)\ge r'$. Equality holds by putting one vertex of every
component into $A$. If $A$ is a nonempty clique in a component $K$, then $B$ contains the other $c-1$ components, with
equality for $A=K$. $\square$

**Lemma 2.** Let $G$ be a minimal $(\infty,k)$-polar obstruction with an isolated vertex $x$. Then every nontrivial
component of $G$, except at most one, is complete.
*Proof.* Take an $(\infty,k)$-partition $(A,B)$ of $G-x$. If $A$ were edgeless, $(A\cup\{x\},B)$ would be a
partition of $G$. So $A$ has an edge and, by F1, lies in one component of $G-x$. All other components lie in $B$, so they are
connected clusters, i.e. complete. $\square$

**Case I: $G$ is a cluster.** By Lemma 1, $r'\ge k+1$ and $c\ge k+2$. Deleting an isolated vertex gives $c-1$ components and
the same $r'$, which must be polar, so $c=k+2$. Deleting a vertex of a component of order $\ge3$ changes neither $c$ nor $r'$,
so all nontrivial components are $K_2$. Deleting a vertex of a $K_2$ gives $(c,r'-1)$, and this must be polar with $c-1=k+1>k$,
so $r'=k+1$. Then $i=c-r'=1$ and $G=K_1+(k+1)K_2$. Conversely, Lemma 1 shows that this graph is a minimal
obstruction, of type $(k+2,1)$.

**Case II: exactly one non-complete component $Q$.** Write $G=iK_1+K_{s_1}+\dots+K_{s_r}+Q$ with $s_j\ge2$, where
$Q$ is connected and non-complete.

**Lemma 3 (criterion).** For such $G$ (any $i,r\ge0$), $G$ is $(\infty,k)$-polar iff $Q$ is $(1,k-r)$-polar or $Q$ is
$(\infty,k-r-i)$-polar. (A negative index means false.)
*Proof.* ($\Leftarrow$) Given a $(1,k-r)$-partition $(A_Q,B_Q)$ of $Q$, put into $A$ the set $A_Q$, all isolated vertices and one
vertex of each $K_{s_j}$. This $A$ is edgeless and $\mathrm{cl}(B)\le k-r+r$. Given an $(\infty,k-r-i)$-partition, put everything outside $Q$
into $B$. ($\Rightarrow$) Let $(A,B)$ be a partition of $G$. If $A$ is edgeless, each $K_{s_j}$ leaves at least one vertex in $B$, and
these vertices lie in distinct cliques of $B$ outside $Q$. So $(A\cap Q,B\cap Q)$ is a $(1,k-r)$-partition of $Q$. If $A$ has an edge, it is connected (F1), so it lies in
one component. It is not an isolated vertex or a $K_{s_j}$, for otherwise $Q\subseteq B$ would be a connected cluster, i.e. complete.
So $A\subseteq Q$ and $B$ contains $i+r$ cliques outside $Q$. $\square$

**Lemma 4.** In Case II every $s_j=2$. (Deleting a vertex of $K_{s_j}$ with $s_j\ge3$ leaves $i,r,Q$ unchanged, so by Lemma 3
$G-v$ is still not polar.)

So $G=iK_1+rK_2+Q$ and $c=i+r+1$. **In the conjectured range $r=c-i-1\ge1$.** Put $\ell=k-r$. Then
$\ell\ge i-1\ge0$ because $c\le k+2$. Lemma 3 and the vertex deletions show that $G$ is a minimal obstruction iff:
* (C1) $Q$ is not $(1,\ell)$-polar; (C2) $Q$ is not $(\infty,\ell-i)$-polar (this is non-polarity of $G$);
* (C3) $Q$ is $(\infty,\ell-i+1)$-polar (delete an isolated vertex);
* (C4) $Q$ is $(1,\ell+1)$-polar (delete a vertex of a $K_2$; Lemma 3 with $r-1$ and (C2));
* (C5) $G-v$ is $(\infty,k)$-polar for every $v\in V(Q)$.

**Lemma 5 (structure).** Let $Q$ be a connected cograph that is $(1,\ell+1)$-polar but not $(1,\ell)$-polar, with
$\ell\ge1$. Then $Q=\overline{K_a}\oplus C$ with $a\ge1$ and $C$ a cluster with exactly $\ell+1$ cliques.
*Proof.* Let $(A,B)$ be a $(1,\ell+1)$-partition. Then $\mathrm{cl}(B)=\ell+1\ge2$, so $B$ is disconnected. By F4, $Q=X\oplus Y$. By F3,
$B\subseteq Y$, say. Then $X\subseteq A$, and $A$ is edgeless and meets $X$, so $A\subseteq X$ (F3). Hence $A=X$ and $B=Y$. $\square$

**Lemma 6 (polarity of $\overline{K_a}\oplus C$).** Let $C$ be a cluster with $m\ge2$ cliques of orders $n_1,\dots,n_m$,
let $\beta=\#\{j:n_j\ge2\}$, $a\ge1$ and $Q=\overline{K_a}\oplus C$.
(a) For $1\le p\le m-1$: $Q$ is $(1,p)$-polar iff ($a=1$ and $\beta\le1$) or ($\beta=0$ and $a\le p$).
(b) For $p\ge0$: $Q$ is $(\infty,p)$-polar iff $\min(\beta,m-1)\le p$.
*Proof.* Let $I$ be the $\overline{K_a}$ side.
(a) By F3, an edgeless $A$ lies in $I$ or in $C$. If $A\subseteq I$ and $I\setminus A\ne\emptyset$, then $B$ meets both sides,
so it is a clique and $m=1$, a contradiction. So $A=I$ and $\mathrm{cl}(B)=m>p$. If $A\subseteq C$ is nonempty (at most one vertex per
clique) and $C=A$, then $\beta=0$ and $B=I$ has $a$ cliques. If $C\ne A$, then $B=I\cup(C\setminus A)$ meets both sides, so it is a clique.
Then $a=1$, and $C\setminus A$ lies in one clique, so all other cliques are singletons, i.e. $\beta\le1$. The converse constructions are
$A=$ {one vertex of every clique other than a largest one}, $B=I\cup$ {a largest clique} (one clique, $p\ge1$); and $A=C$, $B=I$.
(b) ($\Leftarrow$) If $\beta\le p$: $A=I\cup$ {one vertex per clique}, which is CM because it is $\overline{K_a}$ joined with an edgeless set, and $\mathrm{cl}(B)=\beta$.
If $m-1\le p$: $A=I\cup K_{n_1}$ (CM) and $\mathrm{cl}(B)=m-1$. ($\Rightarrow$) Suppose first that $B$ meets both sides. Then $B$ is a clique $\{x\}\cup Q'$ with $Q'$ in one
clique of $C$, and $p\ge1$. Now $A\cap C=C\setminus Q'$ is CM and a cluster, so by F2 it is edgeless (then $\beta\le1$) or a clique
(then $m=2$). Next suppose $B\subseteq I$. Then $C\subseteq A$ is CM with $m\ge2$ cliques, so it is edgeless and $\beta=0$. Finally suppose $B\subseteq C$. If
$A\cap C=\emptyset$ then $\mathrm{cl}(B)=m$. If $A\cap C$ is edgeless then $\mathrm{cl}(B)\ge\beta$. If $A\cap C$ is a clique then $\mathrm{cl}(B)\ge m-1$. $\square$

**Finishing Case II.** First let $\ell=0$, so that $i=1$. By (C4) $Q$ is split, by (C3) it is CM, and by (C1) it has an edge. A CM split
graph has at most one part of order $\ge2$, since $K_{2,2}=C_4$ is not $(1,1)$-polar. $Q$ is non-complete, so
$Q=K_t\oplus\overline{K_a}$ with $a\ge2$ and $t\ge1$. Delete $v$ in the $\overline{K_a}$ part. If $a\ge3$, $Q-v$ is connected, non-complete and not
edgeless, so by Lemma 3 $G-v$ is not polar. If $a=2$, then $G-v=K_1+kK_2+K_{t+1}$ is a cluster with $k+2$ components, $k+1$ of them nontrivial, so it is not polar by
Lemma 1. So there is no Case II obstruction with $\ell=0$.

Now let $\ell\ge1$. By (C1), (C4) and Lemma 5, $Q=\overline{K_a}\oplus C$ with $m=\ell+1$ cliques. Lemma 6 turns the conditions into:
(C1) $\neg[(a=1\wedge\beta\le1)\vee(\beta=0\wedge a\le\ell)]$. (C2) $\beta\ge\ell-i+1$. (C3) $\beta\le\ell-i+1$ or $i=1$.
For (C5), consider the cases for $v$:
(v1) $v\in I$ with $a\ge2$. Then $Q-v=\overline{K_{a-1}}\oplus C$ and (C2) is unchanged, so we need $(a=2\wedge\beta\le1)\vee(\beta=0\wedge a\le\ell+1)$.
(v2) $v\in I$ with $a=1$. Then $G-v$ is a cluster, and Lemma 1 gives $\beta\le\ell$.
(v3) $v$ in a clique of order $\ge3$. Nothing changes, which is impossible, so all $n_j\le2$.
(v4) $v$ in a clique of order $2$. We need $(a=1\wedge\beta\le2)\vee(\beta=1\wedge a\le\ell)\vee\min(\beta-1,\ell)\le\ell-i$.
(v5) $v$ a singleton clique. This is always polar: $A=I\cup\{\text{isolated vertices}\}$ is edgeless, and $B=rK_2+(C-v)$ has $r+\ell=k$ cliques.
* $\beta=0$: (C1) gives $a\ge\ell+1$. (C2) gives $i\ge\ell+1$, so $i=\ell+1=m$. (v1) gives $a\le\ell+1$. Hence $Q=K_{i,i}$ ($i\ge2$) and $c=k+2$.
* $\beta=1$: (C1) gives $a\ge2$ and (v1) gives $a=2$. (C2) and (C3) give $i=\ell$ (for $i=1$, (C2) gives $\ell\le1$). (v4) holds because $0\le\ell-i$. Hence
  $Q=\overline{K_2}\oplus(K_2+iK_1)$ and $c=k+1$.
* $\beta\ge2$: (v1) is impossible, so $a=1$. (C2), (C3) and (v2) give $\beta=\ell-i+1$ (for $i=1$, by (C2) and (v2)). (v4) holds with equality.
  Hence $Q=K_1\oplus(\beta K_2+iK_1)$ with $\beta=k-c+2\ge2$, i.e. $c\le k$.

In each case all of (C1)–(C5) were checked as equivalences, so the graph found is indeed a minimal obstruction (existence).
Each type $(c,i)$ in the range therefore has exactly the one obstruction $P(k,c,i)$. For $c=k+2,\ i=1$ it is the Case I cluster,
since Case II needs $\beta=0$ and hence $i\ge2$. For every other type, Case I is impossible. $\blacksquare$

## 4. Novelty and credit risk (honest)

* There is no public resolution in the source (only one arXiv version), in the 2023 thesis (Conjecture 3.27 still open), or in
  the 2024 Graphs Combin. follow-up (arXiv:2203.04953, which mentions $(\infty,k)$ only as prior work). Web searches found no
  later citing paper that resolves it. The Lean Pool, Omega D5/Problems and OpenAI/math path screens found no polar-obstruction
  item (outputs/registry-screen.json). This is a bounded search, not global clearance.
* **Risk: the proof is elementary and about three pages.** It does not use the source's Theorem 25 or Corollary 26. It reproves the needed
  parts of the source's Lemma 5 (items 4 and 5; the source omits that proof) inline, as Lemmas 2 and 4. The decisive new step is that in the
  conjectured range there is a $K_2$ component. Deleting one of its vertices forces $(1,\ell+1)$-polarity of $Q$, and together with non-$(1,\ell)$-polarity this
  rigidly gives $Q=\overline{K_a}\oplus$ cluster (Lemma 5). After that, an exact polarity calculus (Lemma 6) settles everything. The authors did not find
  this. Root should judge whether it clears the "short proof from source ingredients" bar (precedents 374241, 371637). In my
  assessment it is not a bridge from the source's printed lemmas: the source's lemmas alone do not give it, and the source states the general
  $(c,c-1)$ types are hard.
* Significance: a named conjecture in a 2021 Discrete Mathematics paper, repeated in a 2023 thesis, about a niche topic.

## 5. Computational corroboration (diagnostics, not proof)

* `scripts/polar_cographs.py`: canonical cotree enumeration of all unlabeled cographs through order 12. The counts match OEIS A000669:
  43,930 at $n=12$. The exact cotree DP for polarity was cross-checked against brute-force partitions through order 7. Totals: 23 obstructions for $k=2$ and
  49 for $k=3$, matching the source's Theorems 27/28. Uniqueness holds in every conjecture-range type found for $k\le4$
  (`outputs/polar-census-N12-K6.json`, logs).
* `scripts/polar_targeted.py`: every $G=iK_1+tK_2+H$ with $H$ connected of order $\le10$, $k\le7$, and all in-range
  $(c,i)$. The found obstructions are exactly $P(k,c,i)$ whenever its order is in range, and there are none otherwise: 0 mismatches
  (`outputs/polar-targeted-H10-K7.json`).
* `scripts/polar_lemmas.py`: machine checks of Lemmas 1, 3, 5 and 6 (38,736 instances) against the DP. All pass.

## 6. Lean plan (UNCOMPILED, not run in this lane)

Endpoint statement (literal): for all naturals $k,c,i$ with $1\le i$, $i+2\le c$, $c\le k+2$:
(1) existence: there are `n` and `G : SimpleGraph (Fin n)` with `IsP4Free G`, `IsMinInfPolarObstruction k G`,
`numComponents G = c` and `numIsolated G = i`; and (2) uniqueness: any two such graphs (on possibly different `Fin n`) are
isomorphic (`Nonempty (G ≃g H)`). Definitions are kept literal: `IsCompleteMultipartite` (non-adjacency transitive on
the induced set), `IsCluster` (induced $P_3$-free), clique count = number of connected components of the induced
subgraph, and polarity = existence of a `Finset` split. Minimality is phrased over proper induced subgraphs exactly
as in the source; the vertex-deletion reduction is a proved lemma (heredity).

Proof route (mirrors section 3): F1–F3 as small lemmas; F4 imported or copied from Lean Pool (Seinsche, with
attribution; check its mathlib pin against d13f23b7); Lemma 1 on clusters; Lemma 3; Lemmas 5/6 on
$\overline{K_a}\oplus C$; then the case analysis, and finally an explicit isomorphism to a normal form `P k c i` built on
`Fin`-indexed vertex sets. Expected cost: high (component bookkeeping and isomorphism to the normal form dominate),
roughly 2–4k lines. A cheaper alternative to discuss with root is an intermediate certified normal form: a structure
recording $(i,r,a,(n_j))$ with a proved isomorphism `G ≃g realize params`. Draft statement skeleton:
`lean-draft/PolarUniqueness.lean` (UNCOMPILED; it contains `sorry` placeholders and is a plan, not a certificate).
