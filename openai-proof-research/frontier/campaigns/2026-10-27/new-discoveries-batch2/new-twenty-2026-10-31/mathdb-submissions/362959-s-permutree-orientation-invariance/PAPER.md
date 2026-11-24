# Orientation invariance for s-permutree lattices

## Abstract

For a fixed signature $s$, the number of elements and every canonical join face count of an $s$-permutree lattice are invariant under an individual change from an up decoration to a down decoration. The proof counts decorated noncrossing $s$-arc diagrams by sweeping an ordered list of active keys. Arcs with a common key are represented by one retained arc and marks at zero levels. The two one-sided decorations have equal local placement counts for every choice of event and active-list length.

## The statement

The MathDB 362959 statement is reproduced verbatim.

> Fix an $n$-tuple ${\boldsymbol{s}}$ of non-negative integers and a decoration map ${\boldsymbol{\delta}}$ assigning one of the four local orientations—none, up, down, or up-down—to each index $i$ with $s_i\ne0$. Let $W_{\boldsymbol{s}}/\equiv_{\boldsymbol{\delta}}$ be the ${\boldsymbol{\delta}}$-permutree lattice, and let its canonical join complex be the simplicial complex formed by canonical join representations.
>
> **Orientation invariance conjecture for s-permutree lattices.** For fixed ${\boldsymbol{s}}$, changing any up decoration to a down decoration in ${\boldsymbol{\delta}}$ does not affect the cardinality of the ${\boldsymbol{\delta}}$-permutree lattice or the $f$-vector of its canonical join complex.
>
> The conjecture concerns invariants that remain unchanged under the indicated decoration change, while the source notes that other structures, such as the undirected cover graph and face lattices, can depend on the positions of the up and down decorations. No resolution is supplied.

This is Conjecture 76 of Eva Philippe and Vincent Pilaud, *Geometric realizations of the $s$-weak order and its lattice quotients*. The $f$-vector is indexed here by size, with the empty face counted at size zero. [arXiv v4](https://arxiv.org/abs/2405.02092v4), [journal article](https://doi.org/10.1112/jlms.70268)

## Source definitions and Lean declarations

Quotations below transcribe the mathematical text of arXiv v4, with mathematical glyphs rendered in LaTeX. In the decoration passage the four source pictograms are denoted by $\mathrm{N},\mathrm{U},\mathrm{D},\mathrm{X}$ for none, up, down, and up-down. Lean indexes levels by `Fin n`, so the source's level $i$ has index $i-1$, and stores an arc's positive label $r$ as $r-1$.

**Definition 1 and Remark 2(4), (6)**

> An $s$-bush is a plane graph with a root, $n$ internal nodes bijectively labeled by $[n]$, and some leaves, defined inductively as follows:
>
> - start with the rooted graph with just a root, no internal node, and a single leaf,
> - at step $j$, attach either to a leaf or to two consecutive leaves, a new node $j$ with $s_j+1$ leaves (except that if $s_j=0$ and $j$ is attached to two leaves, then $j$ gets itself two leaves).
>
> The rank $r(B)$ of an $s$-bush is its number of indegree $1$ nodes. An $s$-tree (resp. $s$-trunk) is an $s$-bush of maximal rank $n$ (resp. minimal rank $\min(\{i\in[n]\mid s_i\ne 0\}\cup\{n\})$). Note that the $s$-trees are precisely the rooted plane trees with internal nodes bijectively labeled by $[n]$ such that the node $j$ has $s_j+1$ children that are either leaves or nodes larger than $j$.
>
> In fact, denoting by
> $$
> \Gamma_s := \prod_{j\in[n]}[S_{j-1}]
> \qquad\text{and}\qquad
> \Lambda_s := \prod_{j\in[n]}[\max(1,T_{j-1}-1)],
> $$
> we can associate to each $p\in\Gamma_s$ the $s$-tree $S_p$ obtained by attaching node $j$ to leaf $p_j$, and to each $q\in\Lambda_s$ the $s$-trunk $T_q$ obtained by attaching node $j$ to leaves $q_j$ and $q_j+1$ (or to the only leaf if there is only one).

`TreePrefix` is the successive single-leaf insertion code and `STree s` is its depth-$n$ carrier. `leafCount s m` starts at one and increases by $s_j$ at each insertion.

**Definitions 28 and 31**

> For an $s$-tree $T$ and $1\le i<j\le n$, the position $\mathrm{pos}(T,i,j)\in\{0,\ldots,s_i\}$ is the minimum of $s_i$ and the number of outgoing edges of $i$ strictly to the right of the increasing path from the root of $T$ to $j$.
>
> The $s$-weak order $W_s$ is the partially ordered set of $s$-trees given by $T\le T'$ if and only if $\mathrm{pos}(T,i,j)\le\mathrm{pos}(T',i,j)$ for all $1\le i<j\le n$.

`TreePrefix.profile` assigns to each leaf its vector of right-edge counts. Inserting $j$ uses the profile of the chosen leaf for the $j$-column of `TreePrefix.pos`. The children inside the inserted node's subtree have new coordinate $s_j,s_j-1,\ldots,0$, and the external leaves receive $s_j$ on the left and $0$ on the right. This is precisely the truncated count in Definition 28. `STree.WeakLE` is the coordinatewise order. `STree.positionOrderIso` proves Proposition 30 and supplies the lattice through the chain-closure join of Remark 37.

**Definition 46**

> An $s$-arc is a quintuple $(i,j,A,B,r)$ where $1\le i<j\le n$, the sets $A$ and $B$ form a partition of $\{k\in]i,j[\mid s_k\ne 0\}$, and $r\in[s_i]$.

`SArc` stores $A$ as `right` and recovers $B$ as `left`, the complement in the positive interior. The source draws the arc to the right of points in $A$ and to the left of points in $B$.

**Definition 48**

> For $J\subseteq[n]$, the left (resp. right) $s$-comb with nodes $J$ is the increasing tree on $J$, where each node $j\in J$ has $s_j+1$ outgoing edges, which are all leaves except the leftmost (resp. rightmost). For an $s$-arc $\alpha:=(i,j,A,B,r)$, we define $T_\vee(\alpha)$ (resp. $T_\wedge(\alpha)$) as the $s$-tree obtained by attaching the right (resp. left) $s$-comb with nodes $A\cup\{j\}$ (resp. $B\cup\{j\}$) to the $(r+1)$-st (resp. $r$-th) rightmost leaf of $i$ in the right (resp. left) $s$-comb with nodes $[n]\setminus(A\cup\{j\})$ (resp. $[n]\setminus(B\cup\{j\})$).

`SArc.Tvee` tracks the rightmost leaf of the graft as the nodes of the two right combs are inserted. `SArc.pos_Tvee` proves the formula in Lemma 49. `STree.Tvee_bijective_irreducibles` proves the join half of Proposition 51.

**Definition 55**

> Consider two $s$-arcs $\alpha:=(i,j,A,B,r)$ and $\alpha':=(i',j',A',B',r')$. Assume without loss of generality that $j\le j'$ (otherwise, exchange $\alpha$ and $\alpha'$). Then $\alpha$ and $\alpha'$ are non-crossing if $j<j'$, and one of the following conditions hold
>
> 1. $j\le i'$,
> 2. $i<i'<j$ and $i'\in A$ and $j\notin A'$ and $A'\cap]i,j[\subseteq A\cap]i',j'[$,
> 3. $i<i'<j$ and $i'\in B$ and $j\notin B'$ and $A'\cap]i,j[\supseteq A\cap]i',j'[$,
> 4. $i=i'$ and $r<r'$ and $j\notin A'$ and $A'\cap]i,j[\subseteq A\cap]i',j'[$,
> 5. $i=i'$ and $r=r'$ and $s_j=0$ and $A'\cap]i,j[=A\cap]i',j'[$,
> 6. $i=i'$ and $r>r'$ and $j\notin B'$ and $A'\cap]i,j[\supseteq A\cap]i',j'[$,
> 7. $i'<i$ and $i\in A'$ and $j\notin B'$ and $A'\cap]i,j[\supseteq A\cap]i',j'[$,
> 8. $i'<i$ and $i\in B'$ and $j\notin A'$ and $A'\cap]i,j[\subseteq A\cap]i',j'[$.
>
> A non-crossing $s$-arc diagram is a set $\delta$ of pairwise non-crossing $s$-arcs. The non-crossing $s$-arc complex is the (flag) simplicial complex of non-crossing $s$-arc diagrams.

`SArc.orderedNoncrossing` is the eight-case predicate. `SArc.Noncrossing` accepts the two possible orders of ends.

**Section 3.1.1**

> A join representation of $x\in L$ is a subset $J\subseteq L$ such that $x=\bigvee J$. Such a representation is irredundant if $x\ne\bigvee J'$ for any strict subset $J'\subsetneq J$. The irredundant join representations of an element $x\in L$ are ordered by containment of the down sets of their elements, i.e. $J\le J'$ if and only if for any $y\in J$ there exists $y'\in J'$ such that $y\le y'$ in $L$. The canonical join representation of $x$ is the minimal irredundant join representation of $x$ for this order when it exists. Its elements are the canonical joinands of $x$.
>
> The canonical join complex of $L$ is the simplicial complex whose vertices are the join irreducible elements of $L$ and whose simplices are the canonical join representations of elements of $L$, see [Rea15, Bar19].

`IsCanonicalJoinRep` requires that the join equal $x$, deleting any joinand strictly lowers the join, and the representation refines every representation of $x$. In a finite lattice every representation contains an irredundant subrepresentation with the same join, so testing refinement on all representations gives the same condition as testing it on irredundant representations. `CanonicalFaceOfSize` is the subtype of these representations whose finite set has the specified size.

**Definition 70**

> Consider two $s$-arcs $\alpha:=(i,j,A,B,r)$ and $\alpha':=(i',j',A',B',r')$. We say that $\alpha$ is a subarc of $\alpha'$ if all the following conditions hold:
>
> - $i'\le i<j\le j'$,
> - $A\subseteq A'$ and $B\subseteq B'$,
> - if $s_j=0$ then $j=j'$,
> - if $i'=i$ then $r=r'$,
> - if $i'<i$ then either $i\in A'$ and $r=1$, or $i\in B'$ and $r=s_i$.

`SArc.IsSubarc` implements this relation. `SArc.allowed_of_subarc` establishes the required down-set property directly.

**Sections 4.1.1 and 4.3.3**

> A congruence $\equiv$ on $L$ is an equivalence relation on $L$ that respects the lattice operations, i.e. such that $x\equiv x'$ and $y\equiv y'$ implies $x\vee y\equiv x'\vee y'$ and $x\wedge y\equiv x'\wedge y'$.
>
> The lattice quotient $L/\equiv$ is the lattice structure on the congruence classes of $\equiv$, where for any two congruence classes $X$ and $Y$, the order is given by $X\le Y$ if and only if $x\le y$ for some representatives $x\in X$ and $y\in Y$, and the join $X\vee Y$ (resp. meet $X\wedge Y$) is the congruence class of $x\vee y$ (resp. $x\wedge y$) for any representatives $x\in X$ and $y\in Y$.
>
> For a map $\delta:\{i\in[n]\mid s_i\ne0\}\to\{\mathrm{N},\mathrm{U},\mathrm{D},\mathrm{X}\}$, the $\delta$-permutree congruence $\equiv_\delta$ is defined by the down set of arcs that do not pass on the right of a point $j$ with $\delta(j)\in\{\mathrm{U},\mathrm{X}\}$ nor on the left of the points $j$ with $\delta(j)\in\{\mathrm{D},\mathrm{X}\}$. The $\delta$-permutree lattice is the quotient $W_s/\equiv_\delta$.

`Allowed` implements the two restrictions at positive levels. `permutreeCon` is the least lattice congruence identifying the join comb of each forbidden arc with its lower cover. The forward implication of Theorem 72, proved below, identifies the uncontracted combs of this generated congruence with the allowed down set used in Corollary 74. `PermutreeLattice` is the genuine quotient by the generated congruence. `ConQuot.gc` proves that the least-representative section is left adjoint to the quotient map. In particular the quotient ordering is equivalent to comparison of least representatives and to the existence of comparable representatives. [Source definitions](https://arxiv.org/pdf/2405.02092v4)

**Conjecture 76**

> For any fixed $s$, changing any $\mathrm{U}$ to $\mathrm{D}$ in $\delta$ does not affect
>
> - the cardinality of the $\delta$-permutree lattice,
> - the $f$-vector of the canonical join complex of the $\delta$-permutree lattice.

## Proof

By Propositions 59 and 61 of Philippe and Pilaud, the map $\alpha\mapsto T_\vee(\alpha)$ identifies noncrossing arc diagrams with canonical join representations of $W_s$. The uncontracted join irreducibles of the decoration congruence are exactly the combs of allowed arcs. The next section proves the forcing implication needed for this identification. The congruence acts on the canonical join complex by restricting it to its uncontracted vertices, as in §4.1.2. Consequently the number of allowed diagrams with $m$ arcs is the number of canonical join faces of size $m$ in the quotient. The $s$-weak order is semidistributive ([CP24a, Thms. 1.21 & 1.40]; Theorem 36 of the source), and a lattice quotient of a join-semidistributive lattice is again join semidistributive. A finite join-semidistributive lattice has a unique canonical join representation for every element. Taking joins gives a bijection from all canonical join faces to lattice elements. The cardinality of the quotient is therefore the sum of the face counts, including the empty face.

### The forcing implication for the decoration congruence

Write $J_a=T_\vee(a)$ and $J_a^-$ for the unique lower cover of this join comb. The coordinates of $J_a^-$ are those of $J_a$ except at the start–end pair $(p,q)$ of $a$, where the label $r$ is replaced by $r-1$. Let $Z=z\vee J_a$ with $J_a^-\le z$. In the coordinatewise maximum of $z$ and $J_a$, the only possible increase over $z$ is this edge. By Remark 37 of the source ([CP24a]), the join is the increasing-walk closure of that maximum, with the first edge carrying the desired threshold and subsequent edges carrying threshold $1$. If $t\le Z(u,v)$ but $t>z(u,v)$, a witnessing walk must contain the edge $p\to q$. Every other edge is available in $z$. Thus $u\le p<q\le v$. If $u<p$, the prefix gives $z(u,p)\ge t$, while $u=p$ requires $t=r$. If $q<v$, the suffix gives $z(q,v)>0$. These prefix and suffix inequalities follow from transitivity of position coordinates.

Suppose $J_b\le Z$ and $J_b\nleq z$. Use a changed coordinate $(u,v)$ at threshold $t=J_b(u,v)$. By the comb coordinate formula, $u$ is the start of $b$ or lies in $b$'s left set, and $v$ is the end of $b$ or lies in its right set. The interval of $a$ is therefore contained in that of $b$. If a positive interior point $h$ is in $a$'s right set, then $z(p,h)\ge r$ by the lower-cover formula, so $z(u,h)\ge t$. If $h$ were in $b$'s left set, the comb of $b$ would require $Z(h,v)=s_h>0$. The coordinate is unchanged because $h>p$, so $z(u,v)\ge t$, a contradiction. If $h$ lies in $a$'s left set, then $z(h,q)=s_h>0$. If $h$ were in $b$'s right set, the same row of the comb of $b$ would require $Z(u,h)\ge t$. This coordinate is unchanged because $h<q$. The suffix, when present, extends $z(h,q)>0$ to $z(h,v)>0$, again implying $z(u,v)\ge t$. Thus both side sets of $a$ are included in the corresponding side sets of $b$.

If $s_q=0$, there can be no positive suffix out of $q$, and $v=q$ cannot lie in $b$'s right set. Hence $q$ is the end of $b$. If the starts coincide, then $u=p$ and the failed threshold is the label of both arcs. If $p$ is strictly later than the start of $b$ and lies in $b$'s right set, then $u<p$. A label $r>1$ would give $z(p,q)>0$, and the prefix and suffix would imply $z(u,v)\ge t$. Thus $r=1$. If $p$ lies in $b$'s left set, the comb of $b$ requires $Z(p,v)=s_p$. When $u=p$, the failed threshold is exactly $s_p$, so $r=s_p$. When $u<p$, a label $r\ne s_p$ would mean $z(p,v)=s_p$, since a changed threshold in row $p$ must equal $r$. The prefix would again imply $z(u,v)\ge t$. This proves that a newly visible comb $J_b$ requires $a$ to be a subarc of $b$ in the sense of Definition 70.

Fix $a$ and compare trees by the sets of combs below them whose arcs do not extend $a$. Equality of these sets is an equivalence and is preserved by meet, since lying below a meet is lying below both factors. To see preservation by join, first consider a cover $x\lessdot y$ with equal sets. A minimal element $w$ with $x\vee w=y$ is join irreducible, hence a comb $J_e$, and $J_e^-\le x$. Indeed, $x\vee J_e^-$ lies in $\{x,y\}$, and if it were $y$, the element $J_e^-<J_e$ would contradict minimality. As $J_e$ lies below $y$ and is absent below $x$, equality of the observed sets forces $a$ to be a subarc of $e$. For any $z$, a comb newly below $(x\vee z)\vee J_e$ extends $e$ by the previous argument, and hence extends $a$ by transitivity of Definition 70. Equality of the observed sets therefore persists after joining both elements of the cover with $z$. A saturated chain proves this for comparable trees with equal sets, since each intermediate set is trapped between the two equal sets. For arbitrary trees with equal sets, their meet has that same set and is comparable with both. This proves join compatibility and gives a lattice congruence.

The congruence just constructed contracts $J_a^-\lessdot J_a$. Any comb lying below $J_a$ and missing below $J_a^-$ is $J_a$ itself, which is outside the observed set. Therefore the principal congruence generated by this cover is contained in the constructed congruence. If it contracts $J_b^-\lessdot J_b$, the comb $J_b$ must be unobserved, so $a$ is a subarc of $b$. This is the forward implication of Theorem 72.

Allowed arcs form a subarc down set by inclusion of the two side sets. If the join of the principal congruences of the forbidden arcs contracts a cover $x\lessdot y$, a chain of member-congruence steps connects $x$ to $y$. Clamping the chain by the lattice polynomial $z\mapsto (z\vee x)\wedge y$ sends every step into the two-element interval $[x,y]$. Some member therefore contracts the cover itself. By the forcing implication, the lower cover of an allowed comb cannot be contracted in this way. The lower cover of every forbidden comb is contracted by construction. This yields the claimed identification of uncontracted join irreducibles.

### Relative order of two arcs

Write $(i,r)$ for the key of an arc. Ends of distinct arcs in a diagram are distinct. For two arcs of the same key with ends $j<j'$, part (5) of Definition 55 says that $s_j=0$ and the arcs agree on their common strict interior.

For distinct keys, consider arcs whose open intervals overlap. At a common start the larger label is on the left. At different starts, the arc starting later lies to the left of the earlier arc exactly when the earlier arc passes to the right of the new start. This prescribes the order throughout the overlap. In a common positive strict interior the left arc cannot pass to the right of the point while the right arc passes to the left. At the first end, if positive, the surviving arc passes on its prescribed side of the ending arc. At a zero level both end-side tests hold automatically. If the open intervals are disjoint, compatibility follows from part (1).

For the verification write $\alpha=(i,j,A,B,r)$ and $\beta=(i',j',A',B',r')$ with $j<j'$ and $i'<j$. When $\beta$ is on the left, the interior test reads $A'\cap]i,j[\subseteq A\cap]i',j'[$, and the end test reads $j\notin A'$. When $\beta$ is on the right, the inclusion is reversed and the end test reads $j\notin B'$. The following table gives the corresponding source cases.

| Start comparison | $\beta$ left of $\alpha$ | $\beta$ right of $\alpha$ | Cases |
|---|---|---|---|
| $i<i'$ | $i'\in A$ | $i'\in B$ | (2), (3) |
| $i=i',r\ne r'$ | $r'>r$ | $r'<r$ | (4), (6) |
| $i'<i$ | $i\in B'$ | $i\in A'$ | (8), (7) |

### Retention and marks

Keep the arc with largest end for each key. Mark that retained arc at the other ends of arcs with its key. Each mark lies at a zero level strictly between start and end. Each erased arc is the restriction of the retained arc to its marked end. There is at most one end or mark altogether per level.

Conversely, start with allowed pairwise noncrossing retained arcs with distinct keys. Place any marks satisfying the preceding conditions and restore the shorter arc at each mark. The decoration restrictions survive because shortening preserves the side assignments on the shortened interior. For arcs of the same key, the earlier end is a zero and the common interior agrees, as required by case (5). For different keys, if the restored arcs overlap, their relative order is inherited from the retained arcs since the relative order depends on the later start and the labels. Interior side tests on the shorter common interval are inherited as well. If the earlier restored end is a mark, its zero level makes the end test automatic. If that end is retained, it is the earlier of the two retained ends because the other retained end is at least as late as its restored end. The end test therefore follows from the original pair. Cases with disjoint open intervals satisfy case (1). These constructions undo each other and the original number of arcs is the number of retained ends plus marks.

### The ordered-list sweep

Scan levels $1,\ldots,n$. Just before level $h$, the active list contains the retained arcs that started earlier and have not yet ended. The list is ordered from left to right and records each arc by its key. Initially and finally it is empty.

At $s_h>0$, if no arc ends, place the point in one of the gaps of the active list. If an arc ends, place the point at that entry and remove it. The entries on each side record their side of the point, subject to the decoration. Independently choose a subset of $[s_h]$ for the starts at this level, and insert those keys in decreasing label order at the gap or in place of the removed entry. There is no mark at such a level.

At $s_h=0$, choose no event, the end of any active entry, or a mark on any active entry. Remove the entry only for an end. This level has no side assignments or starts.

To reconstruct the marked diagram from a completed sweep, record each key's start, end, side assignments and marks as the sweep runs. Each key starts at most once because its first coordinate is the level and the labels form a set. A completed sweep gives every started key a later end. Every mark was made while the key remained live and thus strictly precedes its end. Every positive strict interior level assigns a side exactly once, and all assigned sides are allowed. Pair order is set when the later key starts, or by decreasing labels when two keys start together. Deletion and insertion preserve the relative order of the surviving old entries. The consecutive placement of entries on the two sides of the point prevents reversed sides in the common strict interior. At every positive end the right and left sides agree with the position of that ending entry. Therefore the pair tests hold for all constructed arcs.

Conversely, from a marked diagram one reconstructs the choices in level order. The active list starts empty. Inductively suppose the active list orders each pair by the relative-order rule. At a positive level with no end, the interior test implies that the left-passing entries form a prefix and the right-passing entries form its complementary suffix. This gives a unique gap. With an end, the end test puts the through arcs on their respective sides of the ending entry, giving a unique placement. New keys and labels are specified by the diagram. Their decreasing label order and their insertion between the two sides of the point are precisely the relative-order rule for the new pairs. At a zero level the diagram specifies an ending or marked entry, or no event. The surviving old entries keep their relative orders. The reconstructed sweep gives the original endpoints, marks and assignments, so it inverts the forward construction.

### Transfer counts

Give each end or mark weight $z$. At a positive level with $b$ old active entries and end flag $e\in\{0,1\}$, we require $e\le b$ and have $b-e$ through entries. The number of placements is as follows.

| Allowed through sides | Number of placements |
|---|---:|
| Either side | $b+1-e$ |
| Only left | $1$ |
| Only right | $1$ |
| Neither side | $\mathbf 1_{b=e}$ |

An up decoration forbids through arcs to pass on the right of the point, so they all pass on its left ("only left"); a down decoration gives "only right"; up-down gives "neither side". The two one-sided placements are at opposite extreme gaps, or at opposite extreme entries when one ends. With neither side allowed the through list must be empty. Independently, starting $t$ keys has $\binom{s_h}{t}$ choices. The next active length is $b-e+t$ with weight $z^e$. At zero there is one way to stay at $b$ with weight $1$, $b$ ways to move to $b-1$ with weight $z$ if $b>0$, and $b$ ways to stay at $b$ with weight $z$ by marking.

Starting from the empty list, propagate the counting polynomial of prefixes at each active length. The local counts and next lengths depend only on the old length, and each prefix extension has a unique preceding prefix and local choice. The coefficient of $z^m$ at final length zero is the number of diagrams with $m$ arcs, by retention and sweep reconstruction. The two one-sided rows agree, so a single up-to-down change preserves these counts. Summing them also preserves the quotient cardinality. This proves both clauses of Conjecture 76.

## Significance and prior work

The proof gives a transfer enumeration by active-list length for arbitrary nonnegative signatures. Positive entries can start multiple keys, and zero entries support both ends and marks. The coefficient-wise invariance controls the full canonical join face vector. The two quotients may have different undirected cover graphs, as in the example following Conjecture 76.

The supplied independent review found no resolution in arXiv versions 1–4, the authors' copy, the FPSAC 2025 abstract, the registries checked, or the related work it located. The FPSAC abstract asks the cardinality part as Conjecture 6.11. The closest mechanism is the classical generating tree of Pilaud and Pons, *Permutrees*, §2.5.1, Proposition 19 and Lemma 20. That argument treats unit labels and cardinality. The grouping and zero-level events here handle arbitrary signatures and preserve size in the canonical join complex. The review's citation and keyword searches were partly rate-limited, so this survey has those limits. A refresh on 2026-11-19 found v4 (5 December 2025, the published version) still the latest arXiv version, no erratum in Crossref, and two citing works in OpenAlex, neither on this question. The nearest later framework is von Bell and Ceballos, *Framing lattices and flow polytopes* (arXiv:2512.20575). It realizes the $s$-weak order and the classical permutree lattices as framing lattices, but it does not treat the $s$-permutree congruences or Conjecture 76, and it leaves open whether every lattice quotient of a framing lattice is a framing lattice (its Question 1.6.1). [Classical permutrees](https://arxiv.org/abs/1606.09643), [FPSAC abstract](https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2025/121.pdf)

## Formalization status

The Lean theorem `Permutree.philippe_pilaud_conj76` is unconditional on the literal lattice quotient. It quantifies over every $n$, every $s:\mathrm{Fin}\,n\to\mathbb N$ (zero entries allowed), every decoration $d$ of the positive levels, and every positive level $k$ with $d(k)=\mathrm{up}$. For $d'$ equal to $d$ with $k$ set to down, it asserts $|W_s/\equiv_d|=|W_s/\equiv_{d'}|$ and, for every $m\ge 0$, equal numbers of canonical join representations of size $m$ in the two quotients. Here $W_s$ is the coordinatewise order on insertion trees, $\equiv_d$ is the least lattice congruence contracting the lower covers of $T_\vee(\alpha)$ for the forbidden arcs $\alpha$, and canonical join representations are defined lattice-theoretically in the quotient. The packet proves the insertion-tree lattice, both semidistributive laws, the join-comb coordinates and irreducibles, the lattice-theoretic quotient theorem, and the join cases of Propositions 59 and 61. The graded sweep is an equivalence on the full marked diagrams and sweep codes. The forward implication of Theorem 72 follows from the direct coordinate congruence proof above. These results identify the graded canonical join faces of the literal quotient with the allowed diagrams in Lean. The endpoint and the intermediate diagram and forcing theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The appendix contains the complete checked sources, and the report records the endpoint statements and replay receipts.

## References cited in the source definitions

- [Rea15] Nathan Reading. Noncrossing arc diagrams and canonical join representations. *SIAM Journal on Discrete Mathematics* 29(2), 736–750, 2015.
- [Bar19] Emily Barnard. The canonical join complex. *Electronic Journal of Combinatorics* 26(1), Paper 1.24, 2019.
