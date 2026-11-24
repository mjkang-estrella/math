# Polynomial formulas for truncated depth-first search in ordered trees

## Abstract

We prove Conjecture 7.6 of Dimitrov, Minchev and Zhuang, as stated in arXiv:2404.05664v1 and recorded as MathDB 362667. The total number of visits skipped by truncated depth-first search at target depth \(h\) is \(\sum_{j=h+2}^{2h+1}\binom{2n}{n-j}\), summed over all ordered trees with \(n\) edges and all their depth-\(h\) targets. Consecutive binomial ratios give explicit witness polynomials. A simultaneous recurrence proves coefficientwise nonnegativity for both parities. The conjecture appears only in arXiv v1; arXiv v2 omits it without resolving it, and we have not read the journal version.

## Source statement and definitions

Dimitrov, Minchev and Zhuang state the following in Conjecture 7.6. [arXiv v1, §7](https://arxiv.org/pdf/2404.05664v1#page=30)

> **Conjecture 7.6.** For all \(n\geq \ell\geq 1\), we have
>
> \[
> \operatorname{totalD}(n,2\ell-1)-\operatorname{totalDTrunc}(n,2\ell-1)
> =
> \frac{a_\ell(n)}{(n+2\ell+2)^{(2\ell-2)}}\binom{2n}{n-2\ell-1}
> \]
>
> and
>
> \[
> \operatorname{totalD}(n,2\ell)-\operatorname{totalDTrunc}(n,2\ell)
> =
> \frac{b_\ell(n)}{(n+2\ell+4)^{(2\ell-2)}}\binom{2n+1}{n-2\ell-2}\, ,
> \]
>
> where \(a_\ell(n)\) and \(b_\ell(n)\) are polynomials of degree \(2\ell-2\) with non-negative integer coefficients, such that the leading coefficient of \(a_\ell(n)\) is \(2\ell-1\) and the leading coefficient of \(b_\ell(n)\) is \(\ell\).

The source defines the underlying trees, order, and level as follows. [arXiv v1, §1.1](https://arxiv.org/pdf/2404.05664v1#page=2)

> Consider the set \(\mathcal T\) of all unlabeled rooted ordered trees, which we simply refer to as ordered trees (also called plane trees in the literature). In each of these trees, we have a fixed node called a root, as well as a fixed ordering for the children of each node.
>
> Let \(\mathcal T_n\) denote the subset of trees in \(\mathcal T\) having exactly \(n\) edges[.]
>
> The level of a node \(v\) is the length of the unique path from \(v\) to the root; thus the root is at level \(0\).
>
> DFS is equivalent to a pre-order traversal of the tree, that is, the root is visited first and then recursively the subtrees from left to right.

In Lean, ordered children are a list. The traversal lists the root depth first, then appends the pre-order depths of each child subtree with each entry incremented. Indices distinguish vertices even when their depths agree.

~~~lean
inductive PTree where
  | node : List PTree → PTree

mutual
  def preorderDepths : PTree → List ℕ
    | .node ts => 0 :: forestDepths ts
  def forestDepths : List PTree → List ℕ
    | [] => []
    | t :: ts => (preorderDepths t).map Nat.succ ++ forestDepths ts
end

def trees (n : ℕ) : Finset PTree :=
  (BinaryTree.treesOfNumNodesEq n).map decodeEmbedding
~~~

The binary encoding used to generate this finite set splits a nonempty child list into its first child and the root with the remaining children. The empty binary tree decodes to a root with no children. Lean proves both inverse identities and proves that the binary node count equals the ordered-tree edge count. Consequently, `mem_trees` characterizes membership by `edges t = n`.

The source gives the following score and total definitions. [arXiv v1, §1.1](https://arxiv.org/pdf/2404.05664v1#page=3) · [arXiv v1, §7](https://arxiv.org/pdf/2404.05664v1#page=23)

> \(\operatorname{dfsScore}(v):=\) the number of nodes visited before \(v\) when using DFS.
>
> **Definition 7.1 (Truncated DFS).** Apply DFS, but for a fixed level \(\ell\), we ignore nodes at levels \(>\ell\).
>
> \(\operatorname{dfsTruncScore}(v):=\) the number of nodes visited before \(v\) when using truncated DFS.
>
> \[
> \operatorname{totalD}(n,\ell):=\sum_{T\in\mathcal T_n}\sum_{v\in\operatorname{lev}(T,\ell)}\operatorname{dfsScore}(v).
> \qquad
> \operatorname{totalDTrunc}(n,\ell):=\sum_{T\in\mathcal T_n}\sum_{v\in\operatorname{lev}(T,\ell)}\operatorname{dfsTruncScore}(v).
> \]

The definition of \(\operatorname{lev}(T,\ell)\) is “the set of nodes at level \(\ell\) in the tree \(T\).” At zero-based pre-order position \(k\), the full score is \(k\), and the truncated score is the length of the depth-filtered prefix ending just before \(k\). Descendants of a skipped vertex are also deeper than the cutoff, so suppressing them preserves the pre-order of all retained vertices. The Lean definitions sum these scores over the same positions and trees.

~~~lean
def dfsScore (k : ℕ) : ℕ := k

def dfsTruncScore (h : ℕ) (ds : List ℕ) (k : ℕ) : ℕ :=
  ((ds.take k).filter (· ≤ h)).length

def scoreSum (h : ℕ) (ds : List ℕ) (score : ℕ → ℕ) : ℕ :=
  ∑ k ∈ range ds.length, if ds[k]? = some h then score k else 0

def totalD (n h : ℕ) : ℕ :=
  ∑ t ∈ trees n, scoreSum h (preorderDepths t) dfsScore

def totalDTrunc (n h : ℕ) : ℕ :=
  ∑ t ∈ trees n, scoreSum h (preorderDepths t) (dfsTruncScore h (preorderDepths t))
~~~

We take \((x)^{(d)}=\prod_{i=0}^{d-1}(x+i)\) and use zero for a binomial coefficient with negative lower index. The source leaves the factorial convention implicit. The rising convention reproduces the nonerroneous entries in Tables 2 and 3. For example, it yields \(a_2(n)=3n^2+4n+37\), as printed. A falling factorial would multiply that polynomial by \((n+5)/(n+7)\), which is incompatible with the table and does not yield a polynomial. In Lean, `rising` is the integer cast of `Nat.ascFactorial`; `chooseZ` returns zero below lower index zero and otherwise casts `Nat.choose`.

## 1. A binomial enumeration

Write \(D_h(n)=\operatorname{totalD}(n,h)-\operatorname{totalDTrunc}(n,h)\). For each target \(v\), the score difference counts the vertices \(u\) earlier in pre-order with depth greater than \(h\). Thus \(D_h(n)\) counts ordered pairs \((u,v)\) with those properties over all the trees. We prove
\[
D_h(n)=\sum_{j=h+2}^{2h+1}\binom{2n}{n-j}
\tag{1}
\]
for \(n,h\geq0\), with the sum empty when \(h=0\).

Use formal power series over \(\mathbb Z\) in \(z\) by edge count. Let \(C\) count trees, \(V\) count vertices over all trees, \(L_h\) count vertices at level \(h\), \(A_h\) count vertices deeper than the cutoff, that is, with depth strictly greater than \(h\), and \(P_h=\sum_nD_h(n)z^n\). Any tree with at least one edge splits uniquely into its first child subtree and a tree consisting of the root and its remaining children. There is one joining edge in addition to the edges of the two smaller trees. This split gives
\[
C=1+zC^2,\qquad V=1+z(VC+CV).
\]
For \(V\), the two vertex counts add because the first child lies in the left subtree and the original root lies in the right tree. Put \(T=zC^2\). Then \(C=1+T\) and \(C(1-zC)=1\).

Every tree has exactly one root, so \(L_0=C\). At depth \(h+1\), a vertex of the first child subtree is at relative depth \(h\), and a vertex in the remaining tree keeps its original depth. At depth greater than \(h+1\), the same shift applies. At depth greater than zero, every vertex of the first child subtree qualifies. The one-vertex tree contributes zero to each of these recurrences. It follows that
\[
\begin{aligned}
L_{h+1}&=z(L_h C+C L_{h+1}),\\
A_0&=z(VC+CA_0),\\
A_{h+1}&=z(A_h C+CA_{h+1}).
\end{aligned}
\]
Multiplying these equations in rearranged form by \(C\) gives \(L_h=T^h C\) and \(A_h=T^{h+1}V\).

The root is the first vertex, so \(P_0=0\). For \(P_{h+1}\), pairs internal to the first child subtree contribute \(zP_hC\). Pairs internal to the remaining tree contribute \(zCP_{h+1}\). In a crossing pair the earlier deep vertex lies in the first child subtree and the target lies in the remaining tree. A target at the original root is excluded since \(h+1>0\). This gives the product \(zA_hL_{h+1}\), and the single-vertex tree again contributes zero. Therefore
\[
P_{h+1}
=z(P_hC+CP_{h+1}+A_hL_{h+1})
=T P_h+T^{2h+3}V
\]
where the second equality for \(P_{h+1}\) uses \(C(1-zC)=1\) to solve the recurrence. Starting from \(P_0=0\), induction gives \(P_h=\sum_{j=h+2}^{2h+1}T^j V\).

For \(j\geq0\), let \(F_j=T^jV\). From \(V=1+2zCV\), \(C=1+T\), and \(T=z(1+T)^2\), we obtain
\[
F_0=1+2z(F_0+F_1),\qquad
F_{j+1}=z(F_j+2F_{j+1}+F_{j+2}).
\]
The same relations hold for the series with coefficients \(\binom{2n}{n-j}\). Applying Pascal twice gives the second relation, and at \(j=0\) the equality of the coefficients at lower indices \(n+1\) and \(n-1\) gives the first. For \(n=0\) these two off-central coefficients are both zero. The constant terms are \(1,0,0,\ldots\). Induction on the coefficient index determines all the series jointly, proving (1).

## 2. Explicit polynomials and the two identities

Let empty products equal \(1\). For odd \(h=2\ell-1\), let \(d=h-1\) and \(c_i=h+2+i\), for \(0\leq i\leq d\). Set
\[
a_\ell(X)=\sum_{r=0}^{d}
 \prod_{i<r}(X-c_i)\prod_{r<i\leq d}(X+c_i).
\tag{2}
\]
For even \(h=2\ell\), let \(d=\ell-1\) and \(c_i=h+2+2i\), for \(0\leq i\leq d\). Set
\[
b_\ell(X)=\sum_{r=0}^{d}
 \prod_{i<r}(X-c_i)(X-c_i-1)
 \prod_{r<i\leq d}(X+c_i)(X+c_i+1).
\tag{3}
\]
The odd sum has \(2\ell-1\) monic terms of degree \(2\ell-2\). The even sum has \(\ell\) monic terms of the same degree. Thus the leading coefficients and degrees are exact, also when \(\ell=1\).

For both parities let \(j_0=h+2\). When \(n\geq j_0\), the ratio of the \(j_0+r\) term in (1) to its \(j_0\) term is
\[
\frac{\prod_{i=0}^{r-1}(n-j_0-i)}
     {\prod_{i=1}^{r}(n+j_0+i)}.
\]
This is the successive binomial ratio. For a negative lower index the numerator has a zero factor, so the formula also covers those terms. When \(h=2\ell-1\), bring all \(d+1\) terms to the common denominator \(\prod_{i=1}^d(n+j_0+i)=(n+2\ell+2)^{(2\ell-2)}\). The numerator becomes (2) evaluated at \(n\), multiplied by \(\binom{2n}{n-j_0}\).

When \(h=2\ell\), pair the terms in (1) at indices \(j_0+2r\) and \(j_0+2r+1\). Pascal's identity gives
\[
D_h(n)=\sum_{r=0}^{\ell-1}\binom{2n+1}{n-j_0-2r}.
\]
Relative to the first summand, the \(r\)-th summand has ratio
\[
\frac{\prod_{i=0}^{2r-1}(n-j_0-i)}
     {\prod_{i=0}^{2r-1}(n+j_0+2+i)}.
\]
Use the common denominator \((n+2\ell+4)^{(2\ell-2)}\). Group its factors and the numerator factors two at a time to obtain (3) evaluated at \(n\), multiplied by \(\binom{2n+1}{n-j_0}\). If \(n<j_0\), all the binomial terms in (1) and in the two claimed identities are zero. Each common denominator is strictly positive for \(n\geq0\).

## 3. Coefficientwise nonnegativity

Call a polynomial nonnegative when every coefficient is nonnegative. Such polynomials are closed under addition and multiplication. Let \((E_i,O_i)\) be a finite list of pairs of nonnegative polynomials, with \(O_{i+1}-O_i\) nonnegative at each step. For any suffix \(S\), let \(U(S)=\prod_{i\in S}(E_i+O_i)\) and let \(P(S)\) be the sum over cut indices \(r\in S\) with block \(r\) omitted, using \(E_i-O_i\) before the cut and \(E_i+O_i\) after it. For a polynomial \(q\) also set \(R_q(S)=U(S)-qP(S)\).

We show simultaneously that \(P(S)\) is nonnegative, and that \(R_q(S)\) is nonnegative whenever \(q\) is nonnegative and \(O_i-q\) is nonnegative for the first index \(i\) of \(S\). For the empty suffix, \(P=0\) and \(R_q=1\) for every \(q\). Write a nonempty suffix as \(iS'\), with first block \(i\) and remaining suffix \(S'\). Separating the cut at \(i\) yields
\[
P(iS')=U(S')+(E_i-O_i)P(S')
       = E_i P(S')+R_{O_i}(S').
\]
By the induction hypothesis both terms on the right are nonnegative. The parameter \(O_i\) is valid for \(S'\) because the \(O\)'s are coefficientwise nondecreasing. For the second assertion, \(O_i-q\) nonnegative implies that the same parameter \(q\) is valid for \(S'\). Expanding the definition and using \(U(iS')=(E_i+O_i)U(S')\) gives
\[
R_q(iS')
=(E_i+(O_i-q))R_q(S')+q\bigl(O_i+(O_i-q)\bigr)P(S').
\]
All factors on the right are nonnegative by hypothesis or induction. This proves the simultaneous assertion.

In (2), use \(E_i=X\), \(O_i=c_i\). In (3), use \(E_i=X^2+c_i(c_i+1)\), \(O_i=(2c_i+1)X\). In the even case \(E_i\pm O_i=(X\pm c_i)(X\pm(c_i+1))\). Both choices meet the hypotheses, so \(a_\ell\) and \(b_\ell\) have nonnegative coefficients. They have integer coefficients by construction. Together with the degree calculation and the two identities, this proves the conjecture.

For \(\ell=3\), (3) gives
\[
b_3(X)=3X^4+16X^3+1133X^2+1792X+36312.
\]
Table 3 in v1 prints \(113\) for the quadratic coefficient. The coefficient \(1133\) follows both by expanding (3) and by exact interpolation from independent enumeration of the original pre-order scores. Lean also checks the expansion in `DMZ.table3_b3`. This is a typo in the illustrative table. [arXiv v1, Table 3](https://arxiv.org/pdf/2404.05664v1#page=30)

## 4. Version history, prior work, and significance

The conjecture appears in arXiv v1 (8 April 2024) as Conjecture 7.6. ArXiv v2 (10 July 2026) omits it, together with the exact-formula Theorems 7.3–7.5 of v1, without proving or refuting it. V2 keeps the pair-counting interpretation and the operator identity (43), says that it will not include an explicit formula for \(\operatorname{totalDTrunc}(n,\ell)\), and adds the moment identity (49) and an asymptotic theorem (its Theorem 7.3). The paper was published in SIAM J. Discrete Math. 40(4) (2026), 1913–1945. We have not read the journal text, which requires a subscription. Its public abstract agrees with the v2 abstract, including the asymptotic result for truncated DFS, which suggests that the journal version follows v2, but we have not checked whether it contains Conjecture 7.6 or a proof of it. [arXiv v1](https://arxiv.org/abs/2404.05664v1) · [arXiv v2](https://arxiv.org/abs/2404.05664v2) · [SIAM publication](https://doi.org/10.1137/25M1760891)

The closest prior route is to insert v1 Lemma 5.3 into its Theorems 7.3–7.4 and simplify the Fibonacci-polynomial generating functions. This is a plausible route to (1), and binomial cancellation then gives the product formulas and their leading terms. The bounded review searched the omega, OpenAI Math, Principia and mio-qwq inventories, indexed GitHub code, and arXiv, Crossref, OpenAlex and Semantic Scholar for the source and the truncated DFS formula. It found no prior resolution. Some citation listings and code-search queries were rate-limited, and the journal body remained unavailable. A refresh on 19 November 2026 found no new arXiv version after v2 and no citing work on the formula: Semantic Scholar lists two citing papers, both applications of depth-first search, and Crossref lists no citations of the journal version. [arXiv v1](https://arxiv.org/abs/2404.05664v1) · [OpenAlex work record](https://openalex.org/W4394673504)

Formula (1) reduces the exact truncated-score correction to a single sum of nonnegative binomial coefficients. The polynomial formulas are a different assertion about the same correction. Their cut terms contain negative coefficients, so enumeration and cancellation alone leave the coefficient signs open. The simultaneous recurrence in §3 establishes those signs in the original size variable \(n\) for both parities.

## Lean formalization

The [source appendix](LEAN-SOURCE-APPENDIX.md) contains the full code. `DMZ.depth_difference_binomial` proves (1) from the two score totals, with the finite pre-order pair reduction and first-child tree split checked in Lean. `DMZ.odd_normalize` and `DMZ.even_normalize` use the signed-index binomial recurrence after multiplying by the common denominator. The cut recurrence in §3 is `DMZ.cutPoly_nonneg_aux`. The integer theorem is `DMZ.dmz_conj_7_6`. The positive-denominator equivalence is `DMZ.rising_clear`, and `DMZ.dmz_conj_7_6_div` states the source's formulas with rational division. The [verification report](REPORT.md) records the statements and kernel receipts.

