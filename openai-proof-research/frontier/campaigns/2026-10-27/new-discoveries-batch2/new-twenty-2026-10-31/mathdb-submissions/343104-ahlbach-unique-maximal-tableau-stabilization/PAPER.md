# The increasing permutation uniquely maximizes tableau stabilization

## Abstract

Connor Ahlbach conjectured that the increasing permutation is the unique permutation of size \(n\) with tableau stabilization time \(n\). We prove that the increasing permutation has stabilization time \(n\) and that every permutation with a descent stabilizes by \(n-1\). The new step is a shape formula one copy earlier than the published formula, under the necessary bound on the number of ascents. Decreasing levels give the upper bound. Disjoint increasing routes with a three-row column give the matching lower bound for at most \(n-2\) subsequences, and a deletion and labeling argument gives it for \(n-1\). The formal endpoint defines stabilization through Schensted row insertion; its identification with Ahlbach's jeu de taquin definition is the source's Lemma 2.10 and is not proved in Lean.

## Statement and source definitions

Ahlbach states the conjecture as follows.

> **Conjecture 9.2.** The permutation \(w = 1\ 2\ \ldots\ (n-1)\ n\) is the only permutation with \(\operatorname{stab}(w)=n\).

[Connor Ahlbach, *Tableau Stabilization and Rectangular Tableaux Fixed by Promotion Powers*, arXiv:1907.00105v2, p. 55](https://arxiv.org/pdf/1907.00105v2#page=55)

MathDB 343104 states the conjecture in the following form.

> Let \(w\) be a permutation of \(\{1,2,\dots,n\}\), viewed as a tableau, and let \(\operatorname{stab}(w)\) denote its stabilization time. **Maximal-stabilization conjecture.** The increasing permutation
>
> \[
> w=1\,2\,\dots\,(n-1)\,n
> \]
>
> is the only permutation with \(\operatorname{stab}(w)=n\).

The definitions below are transcribed from the same version, with mathematical typography normalized.

> **Definition 1.1.** For any standard skew tableau \(S\), let \(S^{(k)}\) denote the result of attaching \((k-1)\) shifted copies of \(S\) to the right of \(S\) so that the result is a standard skew tableau. Let \(m\) denote the size of \(S\) and \(k\) be a positive integer. We say \(S\) stabilizes at \(k\) if the entries in \([(k-1)m+1,km]\) lie in the same rows in \(\operatorname{Rect}(S^{(k)})\) and \(S^{(k)}\). Let \(\operatorname{stab}(S)\) denote the minimum value at which \(S\) stabilizes.

[Definition 1.1, p. 1](https://arxiv.org/pdf/1907.00105v2#page=1)

> **Definition 8.1.** For \(w=w_1\ldots w_n\in S_n\), let \(T(w)\) be the unique standard skew tableau with shape \((1)\cup\cdots\cup(1)\) with reading word \(w\), and define \(\operatorname{stab}(w):=\operatorname{stab}(T(w))\). Let
> \[
> \operatorname{asc}(w):=\#\{i:w_i<w_{i+1}\}
> \]
> denote the number of ascents of \(w\).

[Definition 8.1, p. 47](https://arxiv.org/pdf/1907.00105v2#page=47)

> The reading word of \(S\) is the sequence of entries in \(S\) read left to right along the rows, from bottom to top.

[Section 2.1, p. 8](https://arxiv.org/pdf/1907.00105v2#page=8)

> **Definition 2.2.** For any tableau \(T\) and \(x\in\mathbb Z_{\ge1}\), let \(T\leftarrow x\) be the tableau obtained by row inserting \(x\) into \(T\). For a word \(w=w_1w_2\ldots w_n\), let
> \[
> T\leftarrow w:= (\ldots((T\leftarrow w_1)\leftarrow w_2)\ldots)\leftarrow w_n.
> \]
> Let \(P(w):=\varnothing\leftarrow w\) denote the insertion tableau of \(w\) and \(Q(w)\) denote the recording tableau of \(w\), which records the order the cells are created in \(\varnothing\leftarrow w\).

[Definition 2.2, p. 8](https://arxiv.org/pdf/1907.00105v2#page=8)

> **Definition 2.8.** For any skew tableau \(S\), an inner slide on \(S\) is the act of sliding into an outer corner of the inner shape of \(S\) and continuing to slide into the created hole so that increasing rows and columns are preserved until we reach an outer corner of \(S\). Let \(\operatorname{Rect}(S)\) denote the rectification of \(S\), obtained by continually performing inner slides until straight shape is achieved. \(\operatorname{Rect}(S)\) is well-defined in that it is independent of the order of the slides. See Example 2.9.

[Definition 2.8, p. 9](https://arxiv.org/pdf/1907.00105v2#page=9)

> **Lemma 2.10.** [Ful97, §2.1, Corollary 2] For any skew tableau \(S\),
> \[
> \operatorname{Rect}(S)=P(w),
> \]
> where \(w\) is the reading word of \(S\).

[Lemma 2.10, p. 10](https://arxiv.org/pdf/1907.00105v2#page=10)

The source expands the permutation’s reading word explicitly in the proof of Lemma 8.4.

> The reading word of \(T(w)^{(r)}\) is
> \[
> w_1^{(r)}\ldots w_n^{(r)}
> =w_1(w_1+n)\ldots(w_1+(r-1)n)\ldots w_n(w_n+n)\ldots(w_n+(r-1)n),
> \]
> so
> \[
> \operatorname{Rect}(T(w)^{(r)})=P(w_1^{(r)}\ldots w_n^{(r)})
> \tag{75}
> \]
> by Lemma 2.10.

The Lean definition uses the **row-insertion form** supplied by Lemma 2.10. Write \(W_k\) for the concatenation of the blocks \(w_i,w_i+n,\ldots,w_i+(k-1)n\) in increasing order of \(i\), and take \(W_0\) to be empty. This is the word in Ahlbach’s equation (75). In Lean, `kFoldWord w k` is \(W_k\), `insertionTableau` is \(P\) from Definition 2.2, and `lastCopy w k i` is the letter \(w_{i+1}+(k-1)n\) for zero-based reading index \(i\). The predicate `stabilizesAt w k` requires \(k>0\) and checks that the row of each such letter in \(P(W_k)\) has zero-based top index \(n-1-i\), its original row in \(T(w)^{(k)}\). The definition `stab` takes the least positive \(k\) satisfying this predicate. [Equation (75), p. 48](https://arxiv.org/pdf/1907.00105v2#page=48)

**Scope of the formal definition.** The Lean development does not define jeu de taquin or rectification. It defines \(\operatorname{stab}\) directly by the row-insertion form above: the least \(k>0\) such that every last-copy letter of \(W_k\) lies in \(P(W_k)\) in its original row of \(T(w)^{(k)}\). That this is Ahlbach's quantity of Definition 1.1 is the source's Lemma 2.10, \(\operatorname{Rect}(S)=P(\text{reading word of }S)\), which the source quotes from Fulton without proof, applied exactly as in the source's equation (75). This bridge is a published classical theorem and is not checked in Lean. The endpoint assumes \(n>0\). For \(n=0\) both definitions give \(\operatorname{stab}=1\) for the empty permutation, so the equivalence would fail there; the source's statement concerns \(S_n\) with \(n\ge1\).

The written proof uses Ahlbach’s equivalent shape criterion. Here \(\operatorname{rv}\) lists the row sizes from top to bottom. Definition 3.1 defines row shift equivalence as follows.

> For any skew tableau \(S\), let \(S+x\) denote the result of adding \(x\) to each cell of \(S\). We say two skew tableaux \(S_1\) and \(S_2\) are row shift equivalent, denoted \(\sim\), if there exists a constant \(x\) so \(S_1+x\) and \(S_2\) differ only by horizontal slides.

> **Definition 3.2.** For \(c\le d\), let \(S|_{[c,d]}\) be the restriction of \(S\) to the cells with entries in \([c,d]\). Suppose \(S\) is a standard skew tableau with \(m\) entries and decreasing row vector. Recall that \(S^{(k)}\) is the result of attaching \((k-1)\) shifted copies of \(S\) to the right of \(S\) so that the result is a standard skew tableau. This means \(S^{(k)}|_{[(j-1)m+1,jm]}\sim S\) for all \(j=1,\ldots,k\). We say \(S\) stabilizes at \(k\) if any of the following equivalent conditions hold:
>
> (a) \(\operatorname{Rect}(S^{(k)})|_{[(k-1)m+1,km]}\sim S\),
>
> (b) \(\operatorname{Rect}(S^{(k)})|_{[(k-1)m+1,km]}\) and \(S\) have the same number of cells in each row,
>
> (c) \(\operatorname{rv}(\operatorname{Rect}(S^{(k)}))-\operatorname{rv}(\operatorname{Rect}(S^{(k-1)}))=\operatorname{rv}(S)\).
>
> Let \(\operatorname{stab}(S)\) denote the minimum value at which \(S\) stabilizes. See Example 1.2 for examples.

[Definitions 3.1 and 3.2, p. 17](https://arxiv.org/pdf/1907.00105v2#page=17)

For the permutation shape, \(\operatorname{rv}(T(w))=(1,\ldots,1)\). If \(\lambda_j(k)\) is row \(j\)'s length in \(P(W_k)\), padded with zeros, then the criterion is
\[
\lambda_j(k)=\lambda_j(k-1)+1\qquad (1\le j\le n).
\tag{1}
\]
The \(n\) increasing blocks cover \(W_k\), so Greene’s identity, proved for distinct letters in the appendix below, gives \(\sum_{j=1}^n\lambda_j(k)=nk\). Hence \(P(W_k)\) has at most \(n\) rows. For \(k=1\), the shape of \(W_0\) in (1) is empty and (1) is the assertion that the rectified tableau has one cell in each original row, as in Definition 3.2(b).

The formal proof also derives (1) directly for its row-insertion definition. Restricting to entries at most \((k-1)n\) commutes with insertion. At each row, a letter above the cutoff changes only entries above the cutoff. A letter at or below the cutoff either bumps the same retained entry in the restricted row or appends there, in which case any bump in the original row is above the cutoff. This gives the identity row by row through the whole word. The retained word is \(W_{k-1}\), so the difference of lengths in (1) counts last-copy entries.

To recover the individual rows from the counts, insert each increasing block as a batch. At a fixed row, successive inputs replace or append at strictly increasing columns. The bumped letters are taken from the original row in increasing order, and each input stays in that row for the rest of the batch. Repeating this with the increasing stream sent to each lower row shows that a letter moves down at most one row in any subsequent batch. A last-copy letter enters the first row during its original block and has \(n-i\) subsequent blocks when its reading index is \(i\in\{1,\ldots,n\}\). Its final row index from the top is at most its original row index. Condition (1) places exactly one such letter in each of the \(n\) rows. The sums of the original and final row indices agree, so each letter has its original row index. This is the Lean lemma `stabilizesAt_iff_growsOne`.

## Proof

**Theorem.** If \(n\ge1\) and \(w\in S_n\), then \(\operatorname{stab}(w)=n\) if and only if \(w=1\,2\,\cdots\,n\).

Index the letters of \(W_k\) by \((i,c)\), with \(1\le i\le n\) and \(1\le c\le k\); the letter \((i,c)\) is \(w_i+(c-1)n\). In this section \(i\) is called the row and \(c\) the column of the letter. These are positions in the \(n\times k\) grid of letters, not rows of a tableau. Reading order is lexicographic on \((i,c)\), and value order is lexicographic on \((c,w_i)\). Let \(a_i\) indicate \(w_i<w_{i+1}\), set \(s_i=\sum_{h=1}^{i-1}a_h\), and let \(A=s_n\).

We prove that for \(n\ge2\), \(k\ge n-2\) and \(k\ge A\), the shape has partial sums
\[
\sum_{j=1}^t\lambda_j(k)=tk+\sum_{j=1}^t(s_{n-t+j}-s_j)
\quad (1\le t\le n). \tag{2}
\]
By Greene's theorem (Theorem 2.7 in the source), the left side is the maximum total size of \(t\) disjoint increasing subsequences of \(W_k\), with empty subsequences allowed. The appendix proves the identity for distinct letters.

**Upper bound.** Group the cells by their level \(\ell=c+s_i\). The rows on a fixed level satisfy \(s_i\in[\ell-k,\ell-1]\), so they form a consecutive interval. On successive rows of a level, the column drops by \(a_i\). A strict column drop strictly decreases the value. If the column stays the same, then \(a_i=0\), so \(w_i>w_{i+1}\) and the value again strictly decreases. Thus a level is a decreasing subsequence. A union of \(t\) increasing subsequences takes at most \(\min(t,L)\) cells from a level of length \(L\).

A level of length \(L\) contains \(\max(L-t,0)\) windows of \(t+1\) consecutive rows. Given a window \([i,i+t]\), the levels visiting every row of that window are the integers in \([1+s_{i+t},k+s_i]\). Their number is \(k-(s_{i+t}-s_i)\), since \(k\ge A\). Counting the cells excluded by the bound \(\min(t,L)\) over all levels therefore gives
\[
nk-\sum_{i=1}^{n-t}\bigl(k-(s_{i+t}-s_i)\bigr)
=tk+\sum_{j=1}^{t}(s_{n-t+j}-s_j).
\]
The equality follows by writing the sum of all \(s_i\) as the first \(t\) terms plus the remaining \(n-t\) terms, and also as the first \(n-t\) terms plus the last \(t\) terms.

**Lower bound for \(1\le t\le n-2\).** Set \(h=n-t\), so \(h\ge2\). For each \(1\le j\le t\), construct a route using one interval of rows per column. At column \(c\), set \(v=c-t+j\). Relative to row \(j\) the interval is \([f(v),g(v)]\), given by
\[
\begin{array}{c|c}
v & [f(v),g(v)]\\ \hline
v\le0 & [0,0]\\
1\le v\le h-2 & [v-1,v]\\
v=h-1 & [h-2,h]\\
v\ge h & [h,h].
\end{array}
\]
The columns with an interval of length two or three range from \(t-j+1\) to \(t-j+h-1\), and hence lie in \([1,n-2]\). The last row of route \(j\) in column \(c\) is \(j+g(v)\), while the first row of route \(j+1\) in that column is \(j+1+f(v+1)\). The table gives \(g(v)=f(v+1)\) for every integer \(v\), including \(h=2\) when the two-row range is empty. The intervals of adjacent routes are strictly ordered and disjoint. The same relation shows that successive intervals of a single route meet at one row, with all rows of the earlier interval at or before all rows of the later interval.

On a one-row interval select its only cell. On a two-row interval select both cells if the boundary is an ascent, and one otherwise. On a three-row interval select all three if both boundaries are ascents, the adjacent ascending pair if just one boundary is an ascent, and one cell if neither is. This selects exactly one cell per column plus one for each ascent crossed by the route. Within a column the selection is in increasing value and reading order. Between columns the rows are nondecreasing and the column strictly increases, ensuring increasing value and reading order there as well. The route from \(j\) to \(j+h\) consequently gives an increasing subsequence of length \(k+s_{j+h}-s_j\). The \(t\) subsequences are disjoint and attain the bound in (2).

**Lower bound for \(t=n-1\).** Here the right side of (2) equals \(nk-(k-A)\). Delete row 1's \(k-A\) cells with column strictly greater than \(A\). A decreasing subsequence of length \(n\) must use one cell in each of the \(n\) rows. Its column can only decrease weakly, and it must decrease strictly at every ascent boundary. Its first column is therefore at least \(1+A\), so no such subsequence survives. Assign to each remaining cell the maximum length of a decreasing subsequence ending there. These labels lie in \([1,n-1]\). Cells with the same label form an increasing subsequence, since an earlier larger cell would otherwise give a decreasing subsequence ending at the later cell with strictly larger length. The labels partition the remaining word into \(n-1\) increasing subsequences, with empty ones allowed. This attains the desired size.

**Lower bound for \(t=n\).** The \(n\) row blocks give a partition into increasing subsequences. This finishes (2).

If \(w\) has a descent, then \(A\le n-2\), so (2) holds at both \(n-2\) and \(n-1\). Each \(t\)-th partial sum increases by \(t\). Subtracting consecutive partial sums shows that each row length increases by one, so \(w\) stabilizes by \(n-1\). This includes \(n=2\), where \(W_{n-2}=W_0\).

For the increasing permutation, \(A=n-1\), so (2) at \(n-1\) and \(n\) gives stabilization at \(n\). For \(1\le k<n\), each copy column is an increasing subsequence for the identity. The \(k\) columns cover the word and we may add \(n-1-k\) empty subsequences. Greene's theorem gives \(\sum_{j=1}^{n-1}\lambda_j(k)=nk\), so row \(n\) is empty and the stabilization test fails at \(k\). Finally, for \(n=1\), the single cell stays in its row at \(k=1\), giving stabilization time 1. ∎

## Relation to previous work

Ahlbach’s Lemma 4.2 constructs routes using at most two rows per column, for \(k\ge n-1\). Theorem 1.6, whose case \(r=1\) (which contains the permutation case) the source attributes in effect to Purbhoo–Rhee’s Lemma 11(ii), gives the same partial sums in that range. Comparing the shape at \(k=n-1\) and \(k=n\) gives the bound \(\operatorname{stab}(w)\le n\). Ahlbach’s Lemma 8.4 gives \(\operatorname{stab}(w)>\operatorname{asc}(w)\), which settles the increasing case using that upper bound. Ahlbach, David, Oh, and Wu prove the \(n\)-row upper bound under weaker row-length hypotheses in *Tableau Stabilization and Lattice Paths*. Their §4 leaves the permutation statistic open. Ahlbach’s thesis repeats the uniqueness claim as Conjecture 5.9.2. A search of the papers citing either source (through November 2026) located no resolution of the uniqueness claim. [Ahlbach, arXiv:1907.00105v2](https://arxiv.org/abs/1907.00105v2) · [Ahlbach–David–Oh–Wu, arXiv:2009.02644v2](https://arxiv.org/abs/2009.02644v2) · [Ahlbach’s thesis](https://digital.lib.washington.edu/server/api/core/bitstreams/18516a81-41eb-41ca-a876-f92ff2d0fda0/content)

The threshold improvement comes from allowing a three-row interval in a route, using a separate deletion and labeling argument for \(t=n-1\), and bounding all covers by the decreasing levels. This proves uniqueness of the largest stabilization time for all positive sizes. The other frequencies in the stabilization distribution and the unimodality and log-concavity questions of the source's Open Problem 9.4 remain outside the theorem.

## Formal certificate

`TableauStabilization.mathdb_343104` proves the stated equivalence for \(n>0\) and `w : Equiv.Perm (Fin n)`. `exists_stabilizes` supplies the witness used by `Nat.find`, and `stab_spec` proves that the least count passes the last-copy test. The two bounds used at the endpoint are `stab_id` and `stab_le_pred_of_ne_one`. The distinct-letter Greene identity and the grid shape formula are checked as `greene` and `shape_formula`. The source appendix contains the Lean modules in dependency order. The report records the checker outputs.

## Appendix. A direct proof of the distinct-letter Greene identity used here

For a distinct-letter word, let \(M_t\) be the largest total cardinality of \(t\) disjoint increasing subsequences. The Knuth move \(xzy\leftrightarrow zxy\) for \(x<y<z\) preserves \(M_t\) in arbitrary contexts. Going from \(xzy\) to \(zxy\) can only break a covering when one chain contains both \(x,z\). If \(y\) is unused, take \(x,y\) in that chain in place of \(x,z\). Otherwise write the two affected chains as \(A\,x\,z\,B\) and \(C\,y\,D\), and replace them by \(A\,x\,y\,D\) and \(C\,z\,B\). The prefixes precede the triple, the tails follow it, and the inequalities at the joins follow from the old chains and \(x<y<z\). Sizes and disjointness are preserved. In the reverse move, no increasing chain had contained both \(z,x\), so no chain can break. The second Knuth move \(yxz\leftrightarrow yzx\) follows by simultaneously reversing positions and reversing the value order, which preserves increasing-chain sizes.

The word and the bottom-to-top reading word of its row-insertion tableau are Knuth-equivalent. To prove this, a local calculation suffices. If insertion of \(x\) into an increasing row \(U\,y\,V\) bumps \(y\), the letters of \(U\) are less than \(x\), and \(x<y\) with \(y\) less than the letters of \(V\). In \(U\,y\,V\,x\) first move \(x\) left through \(V\), from right to left, using \(abx\mapsto axb\) where \(x<a<b\). The result is \(U\,y\,x\,V\). Move \(y\) left through \(U\) using \(ayb\mapsto yab\) where \(a<b<y\). The result is \(y\,U\,x\,V\), the bumped letter followed by the updated row. If \(x\) appends, no move is necessary. Apply this to the top row at the end of the reading word. The bumped \(y\) now follows the reading word of the lower rows and precedes the updated top row. Induction on the number of rows propagates the insertion through the lower rows, and induction on word length gives the claim.

Row insertion preserves the partition shape and the column inequalities. If a letter is bumped from column \(b\), then in the next row either the entry in column \(b\) is strictly larger than that letter, or the row has length below \(b\). The next replacement or append is in a column \(b'\le b\). For \(b'=b\) the cell immediately above was just replaced by a smaller letter. For \(b'<b\) its letter is smaller than the formerly bumped letter because its row is strictly increasing. A replacement leaves the letter strictly smaller than the old letter, so it stays smaller than the old entry below it. A later replacement immediately below it inserts the old bumped letter and also preserves this inequality. An append below the first row has a cell above by \(b'\le b\); no cell below is present in its new column since the old shape was a partition. An append in the first row also maintains the shape and column conditions. The first-greater-entry rule maintains increasing rows.

In a bottom-to-top reading word of a tableau, each column is a decreasing subsequence. A union of \(t\) increasing subsequences can take at most \(\min(t,\mathrm{height})\) cells from each column. The sum of these bounds is exactly the number of cells in the top \(t\) rows, which themselves give \(t\) disjoint increasing subsequences with empty rows allowed. Invariance of \(M_t\) under Knuth moves now proves the identity.
