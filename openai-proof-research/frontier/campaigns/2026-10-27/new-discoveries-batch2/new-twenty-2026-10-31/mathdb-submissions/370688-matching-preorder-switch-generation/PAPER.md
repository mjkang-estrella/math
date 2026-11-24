# The realization preorder of labelled perfect matchings

**MathDB 370688. Formalization status: COMPLETE.**

Joseph Briggs, Jessica McDonald and Songling Shan, *Degree sequences realizing labelled perfect matchings*, arXiv:2510.01110v1 (1 October 2025), Conjecture 11, is the sole target of this packet. The complete written proof below follows the supplied proof and independent Opus review. The Lean theorem `Matching370688.conjecture_11` proves the universal statement with literal graph realizability, weakly decreasing natural degree vectors, all three literal switch types, and both the preorder and switch conjuncts at every consecutive pair. It has no additional mathematical hypotheses. The separating graph, small-block reductions, direct rank step and source Lemma 10(b) are proved. All 41 stage-two source modules are retained unchanged. Stage three adds an explicit theorem on literal finite-edge matchings and a complete six-label rank/preorder table.

## Source definitions and Lean transcription

The source opens §1 with: “All graphs in this paper are assumed to be simple.” It then says:

> Consider a weakly decreasing sequence $d_1\ge\cdots\ge d_n$ of non-negative integers for some $n\in\mathbb N$. If there exists a graph $G$ where $V(G)=[n]=\{1,2,\ldots,n\}$ and $\deg_G(i)=d_i$ for $1\le i\le n$, then we say that $(d_1,\ldots,d_n)$ is graphic, and that $G$ realizes $(d_1,\ldots,d_n)$; we also refer to $(d_1,\ldots,d_n)$ as the degree sequence of $G$.

Later in §1, the matching-specific definition is:

> We may also ask when $(d_1,d_2,\ldots,d_n)$ can realize some particular $M\in\mathcal M_n$, that is, when there exists a graph $G$ with $V(G)=[n]$, $\deg_G(i)=d_i$, and $G$ contains the perfect matching $M$.

The source defines the ambient matching family as follows:

> Given the complete graph $K_n$ on the vertex set $[n]$ (with $n$ even) we denote by $\mathcal M_n$ the set of all perfect matchings in $K_n$.

The corresponding Lean objects and edge set are:

```lean
abbrev PM (n : ℕ) := {p : Fin n → Fin n // Function.Involutive p ∧ ∀ v, p v ≠ v}
-- in namespace PM, with n implicit:
def E (M : PM n) : Finset (Sym2 (Fin n)) := univ.image (fun v => s(v, M.val v))
```

Our labels `Fin n` are zero-based, in the same fixed order. `PM n` consists of fixed-point-free involutive partner functions; `PM.E` is the finite image of `v ↦ s(v,p(v))`. `PM.not_diag` and `PM.cover` establish the literal edge conditions. Conversely `EdgePM.toPM_edges` and `all_edge_matchings_represented` show that every loop-free edge matching covering every vertex exactly once has this representation. Thus no restricted model is substituted for the source objects. In addition, `Matching370688.EdgePM.conjecture_11` states and proves the same nonempty-list conclusion directly for the finite edge sets, with literal `EdgePM.Realizes`, `EdgePM.Prec`, and `EdgePM.IsSwitchOf`. Its proof transports the entire list and both adjacent-pair conditions through the proved representation bridge, so the transport is itself kernel checked.

The Lean definition next to the quoted realization definition is:

```lean
def Realizes {n : ℕ} (d : Fin n → ℕ) (M : PM n) : Prop :=
  ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
    (∀ v, G.degree v = d v) ∧ ∀ e ∈ M.E, e ∈ G.edgeSet
```

The source's §5 preorder is:

> Given two matchings $M,N\in\mathcal M_n$, we say that $N\preceq M$ if every degree sequence $(d_1,\ldots,d_n)$ which can realize $M$ can also realize $N$.

```lean
def Prec {n : ℕ} (N M : PM n) : Prop :=
  ∀ d : Fin n → ℕ, Antitone d → Realizes d M → Realizes d N
```

The source switch definition is:

> Given $N,M\in\mathcal M_n$, we say that $N$ is a switch of $M$ if the symmetric difference $M\mathbin\Delta N$ consists of the single 4-cycle $(w,x,y,z)$ for some $w,x,y,z\in[n]$ with $w<x<y<z$ and either:
>
> (1) $M\setminus N=\{(w,x),(y,z)\}$ and $N\setminus M=\{(w,y),(x,z))\}$, or
>
> (2) $M\setminus N=\{(w,y),(x,z)\}$ and $N\setminus M=\{(w,z),(x,y))\}$, or
>
> (3) $M\setminus N=\{(w,x),(y,z)\}$ and $N\setminus M=\{(w,z),(x,y))\}$;

The extra right parentheses in the three target edge sets above are printed in the source; they carry no mathematical meaning. The two prescribed set differences force exactly one alternating four-cycle on the four displayed vertices, so the Lean relation transcribes the three edge replacements directly. The source’s notation “(w,x,y,z)” names those four vertices; it cannot impose that increasing cyclic traversal in all three cases (as the explicit edge pairs and its four-label examples make clear).

```lean
def IsSwitchOf {n : ℕ} (N M : PM n) : Prop :=
  ∃ w x y z : Fin n, w < x ∧ x < y ∧ y < z ∧
    ((M.E \ N.E = {s(w,x), s(y,z)} ∧ N.E \ M.E = {s(w,y), s(x,z)}) ∨
     (M.E \ N.E = {s(w,y), s(x,z)} ∧ N.E \ M.E = {s(w,z), s(x,y)}) ∨
     (M.E \ N.E = {s(w,x), s(y,z)} ∧ N.E \ M.E = {s(w,z), s(x,y)}))
```

**Conjecture 11 (verbatim mathematical statement).**

> Suppose $N,M\in\mathcal M_n$ have $N\preceq M$. Then there exists a sequence
>
> $$N=M_1\preceq M_2\preceq\cdots\preceq M_{k-1}\preceq M_k=M$$
>
> such that $M_j$ is a switch of $M_{j+1}$, for each $j$.

The universal Lean statement is expressed by `Conjecture11`, using `ChainConclusion` below, and proved by the theorem `conjecture_11`. Mathlib 4.34 calls its adjacent-pair chain predicate `List.IsChain`; our compatibility abbreviation `List.Chain'` expands to precisely that predicate.

```lean
def ChainConclusion {n : ℕ} (N M : PM n) : Prop :=
  ∃ L : List (PM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
    L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B)

def Conjecture11 : Prop := ∀ n (N M : PM n), Prec N M → ChainConclusion N M
```

The antitone quantifier is essential: realizability is defined on natural vectors and actual simple graphs, without a rank-order replacement or a built-in positivity condition. `realizes_pos` proves positivity from realization. `realizes_code`, `mem_degreeSupport`, and `prec_iff_support` prove finite reflection in Lean; the four-label computations use this bridge. They recover exactly the six vectors in the source's support table. The six-label checks reproduce the source's incomparable pair, the two positive realizing graphs, both exclusions, and representatives of all three literal switch types. The full six-label endpoint is now a specialization of the general theorem (`conjecture_11_six`). `sixMatch_complete` additionally proves that the 15 listed involutions exhaust every matching on six labels. The complete 225-pair rank test is checked by ordinary `decide`; `six_pair_count` certifies 101 comparable ordered pairs, and `six_complete_preorder_table` identifies this table with the literal preorder through the proved general `prec_iff_rank`. This is a full finite preorder table derived using the universal characterization. No independent exhaustive six-label graph-realization computation is claimed; the earlier support enumeration exceeded its runner deadline.

## Written proof of the universal assertion

The following is the complete written argument implemented by the formalization. It uses an elementary decreasing-rank-defect induction rather than Watson's cover theorem. The new step is the separating-graph construction. Section 3 supplies the preorder signs from source Lemma 10(b).

## 1. The new separating-graph lemma

Write \(p_M\) for the fixed-point-free involution belonging to \(M\). For consecutive blocks
\[
 S=[1,k],\qquad C=[k+1,t],\qquad B=[t+1,n],
 \qquad 1\le k\le t<n,
\]
put
\[
 e_M(S,B)=|\{s\in S:p_M(s)\in B\}|.
\]

**Separating-graph lemma.** If
\[
 e_M(S,B)>e_N(S,B),\tag{2}
\]
there exists a weakly decreasing positive degree sequence which realizes \(M\) and does not realize \(N\).

We give the actual graph, without invoking a sufficient degree-sequence criterion or Tutte's theorem.

### 1.1 Two small-block reductions

We may first replace the block boundaries, keeping (2), as follows.

If \(|C|=1\), say \(C=\{u\}\), and \(p_M(u)\in S\), move \(u\) into \(B\). The new \(M\)-count increases by 1, while the new \(N\)-count increases by at most 1, so (2) persists. Thus we may assume that a one-vertex middle block has its \(M\)-partner in \(B\).

If \(|C|=2\), say \(C=\{u,v\}\) with \(u<v\), its only problematic pattern will be
\[
 p_M(u)\in S,\qquad p_M(v)\in B.\tag{3}
\]
If (3) holds and \(p_N(u)\notin B\), move \(u\) into \(S\). Neither cross-count changes, and the remaining one-vertex middle block has its \(M\)-partner in \(B\).

If (3) holds and \(p_N(u)\in B\), instead move both \(u,v\) into \(B\). The \(M\)-count increases by exactly 1. Since \(u\) is already matched by \(N\) into the old \(B\), at most one of \(u,v\) can have its \(N\)-partner in \(S\); hence the \(N\)-count increases by at most 1. Again (2) persists, and the middle block is now empty.

Consequently we can assume that either:

- \(C\) is empty;
- \(C=\{u\}\) and \(p_M(u)\in B\);
- \(C=\{u,v\}\) and the binary sequence \(1_{p_M(u)\in B},1_{p_M(v)\in B}\) is weakly decreasing;
- \(|C|\ge3\).

For the two-vertex assertion, if the binary pattern were \((0,1)\), the first vertex could not be matched to the second, which is matched into \(B\), so it would be matched into \(S\). This is exactly the pattern already removed in (3).

From now on use the resulting blocks and put \(b=|B|\), \(c=|C|\), and \(e=e_M(S,B)\). By (2), \(e\ge1\).

### 1.2 The graph before correcting the middle degrees

Start with the following simple graph \(G_0\):

1. Include every edge with at least one endpoint in \(S\).
2. Include every edge inside \(C\).
3. Outside these edges include exactly the edges of \(M\) (in particular the prescribed \(C\)-to-\(B\) and \(B\)-to-\(B\) edges).
4. For each \(x\in B\) whose \(M\)-partner is not in \(S\), delete the edge \(\{k,x\}\), where \(k\) is the last vertex of \(S\).

No deleted edge belongs to \(M\). There are exactly \(b-e\) such deletions, all incident with the last vertex of \(S\). Thus
\[
 d_{G_0}(s)=n-1\quad(s<k),\qquad
 d_{G_0}(k)=n-1-(b-e)=t-1+e\ge t.\tag{4}
\]
Every vertex of \(B\) has degree exactly \(k\): if it is matched into \(S\), it has all \(k\) neighbors in \(S\); otherwise it has \(k-1\) neighbors in \(S\) and its one prescribed matching edge outside \(S\).

For \(x\in C\), let \(\varepsilon_x=1\) if \(p_M(x)\in B\), and 0 otherwise. Its degree is
\[
 d_{G_0}(x)=t-1+\varepsilon_x.\tag{5}
\]
The construction already contains \(M\). Its only possible failure to have decreasing degrees is the order of the 0–1 increments in (5).

For \(c=0\), there is nothing to correct. For \(c=1,2\), the small-block reductions make (5) decreasing, every middle degree is greater than \(k\), and its maximum is at most \(t\). Equation (4) makes the whole degree sequence decreasing.

### 1.3 Correcting every middle block of size at least three

Suppose \(c\ge3\). Put
\[
 E=\{x\in C:p_M(x)\in B\},\qquad w=t.
\]
We delete a small graph \(J\) inside \(C\). Every deleted edge will have an endpoint in \(E\). It therefore cannot belong to \(M\), since a vertex in \(E\) has its prescribed partner in \(B\).

- If \(|E|\) is even, pair the vertices of \(E\) arbitrarily and delete those pair edges. The vertices of \(E\) each lose their extra degree 1. Every middle degree becomes \(t-1\).
- If \(|E|\) is odd and \(w\notin E\), pair \(E\cup\{w\}\) and delete those edges. Each pair has an endpoint in \(E\). Every middle degree is \(t-1\), except the last one, which is \(t-2\).
- If \(|E|\) is odd, \(w\in E\), and \(|E|\ge3\), choose two other vertices \(x,y\in E\). Delete \(wx,wy\), and pair and delete the vertices of \(E\setminus\{w,x,y\}\). Again all middle degrees are \(t-1\), except the last one, which is \(t-2\).
- The remaining case is \(E=\{w\}\). Delete the two edges from \(w\) to the preceding two middle vertices. Exactly the last three middle degrees become \(t-2\), and all earlier ones remain \(t-1\).

Call the resulting graph \(G\). This list exhausts all cases, and every pairing is on an even set. All degrees on \(C\) are now decreasing and lie in \(\{t-1,t-2\}\). Since \(c\ge3\),
\[
 t-2=k+c-2\ge k+1.
\]
Together with (4) and the constant \(B\)-degree \(k\), this proves that the complete fixed-label degree sequence \(d\) of \(G\) is weakly decreasing and positive. The graph still contains \(M\). At most five distinct degree values occur.

### 1.4 A necessary inequality excludes \(N\)

We record the necessary inequality with a derivation, because retaining the prescribed matching correction is crucial. Let a graph with degree vector \(d\) contain a perfect matching \(L\). Delete the matching. In \(K_n-L\) the residual required degrees are \(f_i=d_i-1\). Counting residual degrees from \(S=[k]\) gives
\[
 \sum_{i\in S} f_i
 \le 2|E((K_n-L)[S])|
      +\sum_{j\notin S}\min\{f_j,k-1_{p_L(j)\in S}\}.
\]
Use
\[
 \min\{d_j-1,k-1_{p_L(j)\in S}\}
 =\min\{d_j-1,k\}-1_{p_L(j)\in S,\ d_j>k},
\]
and \(k=2e_L(S)+e_L(S,S^c)\). After adding back the \(k\) matching incidences on \(S\), the inequality becomes
\[
 \sum_{i=1}^k d_i\le
 k(k-1)+\sum_{j>k}\min\{d_j-1,k\}
 +e_L(S,\{j>k:d_j\le k\}).\tag{6}
\]

The Lean proof counts the same inequality directly. Each prefix vertex has at most $k-1$ neighbors in the prefix. An outside vertex whose prescribed partner is also outside has at most $d_j-1$ prefix neighbors. If its partner is inside, it has at most $\min(d_j,k)$ prefix neighbors; this differs from $\min(d_j-1,k)$ by one precisely when $d_j\le k$. Double counting the cross edges and applying the partner involution to this correction gives exactly (6). Thus the implementation needs no separate residual-graph subtraction identity.

For the constructed \(d\), the final set in (6) is exactly \(B\): the middle degrees exceed \(k\), and the suffix degrees equal \(k\). The common part of its right side is
\[
 k(k-1)+ck+b(k-1)=k(n-1)-b.
\tag{7}
\]
By (4),
\[
 \sum_{i=1}^k d_i=k(n-1)-b+e_M(S,B).
\tag{8}
\]
Deleting \(J\) did not alter any \(S\)-degree. Equations (2), (7), and (8) violate (6) for \(L=N\). Thus no graph with degree vector \(d\) contains \(N\). The separating-graph lemma is proved. \(\square\)

## 2. From separators to the complete switch chain

Assume \(N\preceq M\). The separating-graph lemma proves
\[
 e_M([k],[t+1,n])\le e_N([k],[t+1,n])
 \qquad(1\le k\le t<n).
\tag{9}
\]
Let
\[
 R_L(i,j)=|\{a\le i:p_L(a)\le j\}|.
\]
For \(i\le j\),
\[
 R_L(i,j)=i-e_L([i],[j+1,n]).
\]
The case \(j=n\) is equality. The matrix \(R_L\) is symmetric, because \(p_L\) is an involution. Consequently (9) gives
\[
 R_M(i,j)\ge R_N(i,j)\quad\text{for all }i,j.
\tag{10}
\]
We next give an elementary rank-to-switch lemma. The first-disagreement choice also appears in Watson's proof of Proposition 11, cited below; the argument here explicitly handles arbitrary intervals and the possible overlap of the two rank rectangles. It does not assume the existence of a fixed-point-free chain in a larger permutation poset.

**Rank-to-switch lemma.** Let \(x,y\) be fixed-point-free involutions with
\[
 R_x(h,k)\ge R_y(h,k)\quad\text{for every }h,k.
 \tag{11}
\]
If \(x\ne y\), there is an allowed source switch \(x\longrightarrow z\) such that
\[
 R_x\ge R_z\ge R_y,
 \qquad
 \sum_{h,k}(R_x-R_y)>
 \sum_{h,k}(R_z-R_y).
 \tag{12}
\]

**Proof.** Let \(i\) be the first label with \(x_i\ne y_i\), and write
\(a=x_i\), \(c=y_i\). The common earlier rows and (11) imply \(a<c\): if \(a>c\), the rank inequality at \((i,c)\) fails. Both \(a\) and \(c\) exceed \(i\). Indeed a partner smaller than \(i\) is in a common earlier row, and involutivity then forces the two partners at \(i\) to agree.

Choose the first \(j>i\) satisfying
\[
 a<x_j\le c,
\]
and put \(b=x_j\). Such a \(j\) exists: the \(x\)-partner of \(c\) exceeds \(i\), because any earlier partner would also be the \(y\)-partner of \(c\), contradicting \(y_c=i\). Thus
\[
 i<a<b\le c,\qquad j>i,
 \tag{13}
\]
and \(i,j,a,b\) are distinct. Minimality says that for \(i<\ell<j\),
\[
 x_\ell\notin(a,c].\tag{14}
\]
Replace the edges \((i,a),(j,b)\) by \((i,b),(j,a)\), obtaining \(z\). This is an allowed source switch: the three possible orders are \(i<j<a<b\) (crossing to nested), \(i<a<j<b\) (separated to nested), and \(i<a<b<j\) (separated to crossing).

A direct count of the four changed entries gives
\[
 D(h,k):=R_x(h,k)-R_z(h,k)
 =1_{i\le h<j,\ a\le k<b}
  +1_{a\le h<b,\ i\le k<j}.
 \tag{15}
\]
In particular \(R_x\ge R_z\). Write \(G=R_x-R_y\), which is nonnegative by (11). We must prove \(G\ge D\).

For a point in the first rectangle of (15), compare columns \(k\) and \(c\). Contributions from rows before \(i\) cancel because those rows agree. Among rows \(i,\ldots,h\), the \(x\)-matrix has no entry in columns \((k,c]\), by (14) and \(x_i=a\le k\); the \(y\)-matrix has at least its entry \((i,c)\). Therefore
\[
 G(h,k)-G(h,c)\ge1,
\]
so \(G(h,k)\ge1\). Symmetry gives the same bound on the second rectangle.

Where the rectangles overlap, both \(h,k\) lie in
\[
 I=[a,\min(j,b)-1].
\]
Their diagonal gaps \(G(h,h),G(k,k)\) are at least 1 by the preceding argument. Each diagonal rank of a fixed-point-free involution is even, since it counts both ends of every internal matched pair. Hence both diagonal gaps are at least 2.

Assume \(h\le k\), and put \(W=\{h+1,\ldots,k\}\). There is no \(x\)-matching edge with both endpoints in \(W\): its labels lie between \(a\) and \(\min(j,b)-1\), so (14) excludes every such partner. Symmetry and the decomposition of the square \([k]^2\) along \([h]^2\) now give exactly
\[
 2G(h,k)=G(h,h)+G(k,k)
   +|\{\ell\in W:y_\ell\in W\}|\ge4.
 \tag{16}
\]
Thus \(G(h,k)\ge2\) throughout the overlap. The case \(k<h\) follows by symmetry. Outside the rectangles \(D=0\), so altogether \(G\ge D\), proving \(R_z\ge R_y\).

Finally the sum of (15) over all rank entries is
\[
 \sum_{h,k}D(h,k)=2(j-i)(b-a)>0.
 \tag{17}
\]
This gives the strict decrease in (12), and proves the lemma. \(\square\)

For the formal natural-number induction, the exact area in (17) is unnecessary. Formula (15) gives weak decrease at every rank cell and strict decrease at $(i,a)$ in the paper's inclusive rank convention (at strict-prefix sizes $(i+1,a+1)$ with zero-based Lean labels). Since $R_z\ge R_y$, subtracting $R_y$ preserves that strict inequality at this cell. Summing the nonnegative defects therefore gives strict potential descent.

Starting with \(x=p_M\), \(y=p_N\), apply the lemma repeatedly. The nonnegative integer potential \(\sum_{h,k}(R_x-R_y)\) decreases strictly, so induction produces a finite allowed-switch chain from \(M\) to \(N\). Reverse the list to obtain exactly the source's displayed sequence. Lemma 10(b), proved again in Section 3 below, supplies every internal preorder comparison in that list. Equality uses a singleton chain; an empty matching, if included, is immediate, and odd orders have no perfect matchings. This proves the entire Conjecture 11. \(\square\)

For context, (10) is the ordinary Bruhat rank criterion \(p_M\le_B p_N\). Watson, *Bruhat order on fixed-point-free involutions in the symmetric group*, Electronic Journal of Combinatorics 21(2) (2014), P2.20, Proposition 11 ([DOI](https://doi.org/10.37236/3861)), also supplies a shorter published route to the chain. Its scope is the order **induced on fixed-point-free involutions**, whose increasing covers change two matching edges by transposition conjugation. The proof above avoids having to import that cover theorem into Lean. Hansson's Definition 4 uses an equivalent northeast-rank convention, obtained by subtracting the southwest rank from its row-prefix size.

Together with source Lemma 10(b), the proof gives the useful exact characterization
\[
 \boxed{\quad N\preceq M\ \Longleftrightarrow\ p_M\le_B p_N
 \ \Longleftrightarrow\ N\text{ is obtainable from }M\text{ by source switches}.\quad}
\]

## 3. Switches preserve the realization preorder

For completeness we give the finite graph alternation argument of source Lemma 10(b), which is formalized as `lemma_10b` in this packet. Suppose the antitone vector $d$ is realized by $G$ containing $M$. For any switch, if both target edges are present then $G$ already contains $N$; if neither is present, delete the two old matching edges and insert the two target edges. Every degree is unchanged.

In a type (1) switch $(wx,yz)\to(wy,xz)$, suppose only $wy$ is present. Then $x\not\sim z\sim y$, and $d_x\ge d_y$. There is a vertex $q$ with $x\sim q\not\sim y$, distinct from $x,y,z$: otherwise, after deleting the possible common adjacency between $x,y$, the neighbors of $x$ would be contained in those of $y$ with $z$ an additional neighbor of $y$, contradicting the degree inequality. Replace $xq,yz$ by $xz,yq$. If only $xz$ is present, use $w\not\sim y\sim z$ and $d_w\ge d_z$, choose $q$ with $w\sim q\not\sim z$, and replace $wq,yz$ by $wy,zq$. In either case the present target edge is not deleted: the auxiliary vertex cannot be its other endpoint because that would contradict the required nonadjacency at $q$. All remaining edges of $N$ are unchanged since $N$ is a matching.

For type (2), $(wy,xz)\to(wz,xy)$, if only $wz$ is present, use $y\not\sim x\sim z$ and $d_y\ge d_z$ to choose $q$ with $y\sim q\not\sim z$. Replace $yq,xz$ by $xy,zq$. If only $xy$ is present, use $w\not\sim z\sim x$ and $d_w\ge d_x$, choose $q$ with $w\sim q\not\sim x$, and replace $wq,xz$ by $wz,xq$. The same neighborhood-count argument excludes the coincident vertices, and the already present target edge cannot be deleted. Thus the resulting graph contains $N$ and has degree vector $d$.

A type (3) switch is the composition of types (1) and (2) on the same four ordered labels, through $(wy,xz)$. Applying the two proved realization transfers in turn proves its assertion. Hence $N\preceq M$ for every literal switch. This establishes the signs in the reversed list constructed above and completes the written proof of Conjecture 11.

## 4. Significance, prior art, and formal verification limits

The principal mathematical claim is the separating graph: it converts any rectangular matching-count discrepancy into a decreasing labelled degree vector that distinguishes two matching supports. The rank chain is a self-contained replacement for a known Bruhat-order route, not claimed as the main novelty. The construction is elementary once found, and its significance is correspondingly bounded; the independent review estimated only a moderate chance that a specialist would call it more than a routine result. This packet claims no new significance merely from formalizing helpers or finite instances.

The independent review dated 20 November 2026 reported that arXiv:2510.01110 had only v1 and no journal reference. Its citation search found Zhen Liu and Qinghou Zeng, *Degree sequences realizing labelled h-factors*, arXiv:2604.11939 (13 April 2026), which proves the source's different h-factor conjecture, not the switch preorder conjecture. The reviewer read that paper and found no switch-preorder statement in it. The review also checked Watson, *Bruhat order on fixed-point-free involutions in the symmetric group*, EJC 21(2) (2014), P2.20, Proposition 11, and Hansson, arXiv:1502.03598, for the rank convention. Neither identifies degree-realization preorders. Bounded registry and web searches in the review found no public proof of the present conjecture. These are inherited, dated review findings, not a new live prior-art clearance by this formalization lane. No external queries or submissions were made in this lane.

The checked endpoint is the universal `Matching370688.conjecture_11` displayed below. It assumes only the source premise `Prec N M`. The theorem is assembled from unconditional `separating_graph`, `first_disagreement_rank_step`, and `lemma_10b`. The universal source preorder is also proved antisymmetric as `prec_antisymm`. The optional theorem `prec_iff_rank` proves the converse rank implication by the same natural-defect induction and source Lemma 10(b); it supplies the connection used by the six-label finite table. All modules are reproduced byte-for-byte in `LEAN-SOURCE-APPENDIX.md`, in dependency order, and compiled and kernel-checked using the pinned 32 GiB runner. The endpoint axiom audit contains exactly `propext`, `Classical.choice`, and `Quot.sound`. The checked mathematical statement covers all n; equality uses the singleton chain, the empty case is included, and odd orders have no partner involutions. This formalization does not constitute a fresh public-status or novelty clearance; the independent final review remains a separate pipeline step.

```lean
theorem conjecture_11 {n : ℕ} (N M : PM n) (h : Prec N M) :
    ∃ L : List (PM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
      L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B)
```

## References

1. J. Briggs, J. McDonald and S. Shan, [Degree sequences realizing labelled perfect matchings](https://arxiv.org/abs/2510.01110v1), 2025, §§1 and 5.
2. Z. Liu and Q. Zeng, [Degree sequences realizing labelled h-factors](https://arxiv.org/abs/2604.11939), 2026.
3. M. Watson, [Bruhat order on fixed-point-free involutions in the symmetric group](https://doi.org/10.37236/3861), Electronic Journal of Combinatorics 21(2), P2.20, 2014.
4. M. Hansson, [The Bruhat order on conjugation-invariant sets of involutions in the symmetric group](https://arxiv.org/abs/1502.03598), 2015.
