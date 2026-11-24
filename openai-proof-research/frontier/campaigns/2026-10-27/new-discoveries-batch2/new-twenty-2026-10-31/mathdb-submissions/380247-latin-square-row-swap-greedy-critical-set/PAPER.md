# Greedy critical sets after a close row swap in the elementary abelian 2-group table

## Abstract

An explicit family of blank masks proves Hämäläinen’s Conjecture 6.1 for the addition tables of elementary abelian 2-groups. After interchanging rows at distance less than three, Algorithm A yields a 2-critical set that admits forced completion one cell at a time in increasing row order. A private intercalate certifies each retained clue, and a decreasing rank certifies the forced fills.

The source contains a misprint, and our result is for the corrected reading. The source’s displayed formula for the greedy order \(f_0\) visits the rows from top to bottom. The sentence that follows it, the proof of its Lemma 3.4, its Corollaries 3.5 and 4.2, and every greedy critical set printed in the paper and its TeX source use the order from bottom to top. We prove the conjecture for that bottom-to-top order. Under the literal formula the top-down conclusion is false at order four for the swap of rows 0 and 1, a case of the source’s own Theorem 5.1. Lean verifies this failure as well.

## Statement and definitions

Conjecture 6.1 of Carlo Hämäläinen, *New 2–critical sets in the abelian 2–group*, JCMCC **61** (2007), 193–219, reads as follows, with mathematical notation typeset for this manuscript. [arXiv version](https://arxiv.org/abs/math/0612338)

> Conjecture 6.1. Let \(\alpha_{k,k'}\) be a row isotopism on a latin square of order \(n=2^s\), defined by
>
> \[
> \alpha(i)=
> \begin{cases}
> k', & i=k \\
> k, & i=k' \\
> i, & \text{otherwise}.
> \end{cases}
> \]
>
> where \(|k-k'|<3\) Then \(\operatorname{gcs}(\alpha_{k,k'}L_s)\) is 2–critical, strong, and completes top down.

The journal text of this conjecture and of the formula for \(f_0\) (pp. 198 and 212) agrees with arXiv:math/0612338v1, the only arXiv version.

**Main Theorem.** Let \(s\ge0\), \(n=2^s\), and \(k,k'\in\{0,\ldots,n-1\}\) with \(|k-k'|<3\). Let \(\operatorname{gcs}\) be Algorithm A run on the full square, inspecting the cells from right to left along each row and from the bottom row to the top row (the order the source describes in words). Then \(\operatorname{gcs}(\alpha_{k,k'}L_s)\) is 2–critical and strong, and it completes top down. Here, completing top down means that the blank cells can be filled one at a time, each with the only symbol missing from its row and column, in nondecreasing row order. In Lean this is `Rowswap.conj_6_1`.

**Proposition (the literal formula).** If Algorithm A instead inspects the cells in the order of the displayed formula for \(f_0\), the resulting critical set of \(\alpha_{0,1}L_2\) does not complete top down. In Lean this is `Rowswap.printed_order_counterexample`, and `Rowswap.printedOrder_eq_formula` identifies the inspection order used there with the displayed formula.

The source says that a square extends top down if, once rows \(0,\ldots,i\) are filled, row \(i+1\) "can be shown to have unique extension". We prove the strongest natural reading of this, filling one forced cell at a time. That implies the weaker reading in which each row, taken as a whole, has a single filling compatible with the row and column constraints. The proposition refutes both readings (see the section on the displayed formula at order four). The source's phrase cannot mean uniqueness among all completions of the square, because then every critical set would complete top down.

We include \(k=k'\), which acts as the identity, and the order-one square. The following quotations pair the source's definitions with the Lean declarations. A support \(P\) represents a subset of triples of a fixed square \(L\). Each coordinate in \(P\) carries the entry of \(L\) there.

**Latin square, partial square, and completion (§2).**

> We begin with some definitions. Let \(N_n^k=\{nk,nk+1,\ldots,nk+n-1\}\) for integers \(k\ge0\) and \(n>0\). A latin square \(L\) of order \(n\) is an \(n\times n\) array with rows indexed by \(N_n^k\), columns by \(N_n^{k'}\), and with entries from the set \(N_n^{k''}\). Further, each \(e\in N_n^{k''}\) appears exactly once in each row and exactly once in each column. This is equivalent to the usual definition where \(k=k'=k''=0\) but allows more flexibility when discussing subsquares. A partial latin square is an \(n\times n\) array where each entry of \(N_n^{k''}\) occurs at most once in each row and in each column.

> A partial latin square \(P\) is uniquely completable if there is just one latin square \(L\) of the same order as \(P\) such that \(P\subseteq L\).

The Lean type is `Square n := Fin n → Fin n → Fin n`. `IsLatin` asserts bijections in every row and column. `PartialLatin` asserts injectivity on the occupied positions in each row and column. `Completes P L M` asserts `IsLatin M` and agreement with \(L\) at every coordinate in \(P\). `UniqueCompletion P L` asserts that \(L\) completes \(P\) and every \(M\) satisfying `Completes P L M` is \(L\).

**Critical and 2-critical (§2).**

> A partial latin square \(C\subseteq L\) is a critical set if
>
> 1. \(C\) has unique completion to \(L\), and
> 2. no proper subset of \(C\) satisfies 1.

> The latin trade containing the least number of entries is a \(2\times2\) subsquare, known as an intercalate. Let \(C\) be a critical set in \(L\), \(c\in C\), and \(I\subseteq L\) an intercalate such that \(C\cap I=\{c\}\). Then \(c\) is said to be 2–essential. If all \(c\in C\) are 2–essential then \(C\) is 2–critical.

Lean’s `IsCritical` checks every single-entry deletion. The lemma `isCritical_iff_proper_subsets` proves equivalence with the proper-subset condition by monotonicity of unique completion. `Intercalate` is a rectangle of distinct rows and columns carrying two symbols on opposite diagonals. `TwoCritical` requires `IsCritical` and such a rectangle meeting the clue set at each individual clue. Lean constructs the disjoint mate by exchanging the two symbols.

**Alternatives, strong completion, and top-down completion (§2).**

> For each \((r,c)\in S\), define
>
> \[
> S_{r,c}=\begin{cases}
> \varnothing,&\text{if }(r,c;e)\in P\text{ for some }e\in N_n,\\
> N\setminus(R_r^P\cup C_c^P),&\text{otherwise}.
> \end{cases}
> \]
>
> Then the array of alternatives of \(S\) with respect to \(P\) and \(L\) is given by \(A(P,S,L)=\{(r,c;S_{r,c})\mid(r,c)\in S\}\).

> A partial latin square \(P\) of order \(n\) is strongly completable if it is uniquely completable to \(L\), there is a sequence of partial latin squares \(P_0=P\subset P_1\subset P_2\subset\ldots\subset P_m=L\) where \(m=n^2-|P|\), and for each \(P_k\) there exists \(r,c\) such that \(|A(N_n\times N_n,P_k)_{r,c}|=1\).

> A strong critical set is a critical set that has strong completion. We say that a (uniquely completable) partial latin square extends top down if, given that rows \(0,1,\ldots,i\) are filled in, then row \(i+1\) can be shown to have unique extension. If all rows can be extended in this manner then the critical set has unique completion top down.

The Lean predicate `Available` requires a blank and excludes the occupied row and column symbols and `Forced` asserts a singleton of alternatives. `Fills` adds that blank, with its forced symbol, at each step until the support is full. `Strong` requires `IsCritical` and this fill sequence. `CompletesTopDown` requires the fill sequence to have nondecreasing row indices. This proves the stated row-by-row unique extension, including uniqueness when filling a row using only the row and column constraints of the current entries. Each fill forces the same symbol in any extension of that row.

**Algorithm A and the order (§3).**

> Input: Partial latin square \(P\) of order \(n\) with unique completion, and bijection \(f:\{1,\ldots,|P|\}\to S_P\).
>
> \(P_0\gets P\)  
> for \(i=1,\ldots,|P|\)  
> \(\quad\) let \(x,y,z\) be integers such that \((x,y;z)\in P_{i-1}\) and \(f(i)=(x,y)\)  
> \(\quad\) if \(P_{i-1}\setminus\{(x,y;z)\}\) has unique completion then  
> \(\qquad P_i\gets P_{i-1}\setminus\{(x,y;z)\}\)  
> \(\quad\) else  
> \(\qquad P_i\gets P_{i-1}\)  
> return \(P_{|P|}\)

> Let \(f_0:\{1,\ldots,n^2\}\to S_L\) be the bijection defined by
>
> \[
> f_0(i)=\left(\left\lfloor\frac{i-1}{n}\right\rfloor,n-i\pmod n\right)
> \]
>
> for \(1\le i\le n^2\) and \(L\) of order \(n\). Then \(f_0\) orders the cells of \(L\) from right to left along each row and from the bottom row to the top row. We abbreviate \(\operatorname{ggcs}(L,f_0)\) to \(\operatorname{gcs}(L)\) and call this the greedy critical set of \(L\).

Lean’s `attempt` tests `UniqueCompletion` after erasing the inspected coordinate. `greedy` folds `attempt` starting at the full square. `gcs` uses `f0order`, the list of all cells sorted by descending \(nr+c\). `printedGcs` instead uses `printedOrder`, with descending key \(n(n-1-r)+c\). The lemma `printedOrder_eq_formula` verifies this order against the printed formula. For \(i=nr+j\) with \(1\le j\le n\), the printed coordinates are \((r,n-j)\) and the key is \(n^2-i\).

**The elementary abelian square (§4).**

> We define \(L_s\) to be the latin square corresponding to the abelian 2–group of order \(n=2^s\) and the partial latin square \(P_s\subset L_s\) as in [2]. That is,
>
> \[
> P_1=\begin{pmatrix}0&\\&\end{pmatrix}\qquad
> L_1=\begin{pmatrix}0&1\\1&0\end{pmatrix}
> \]
>
> and for \(s\ge2\),
>
> \[
> L_s=L_1\times L_{s-1}=\{(x,y;z),(x,y+n/2;z+n/2),(x+n/2,y;z+n/2),
> (x+n/2,y+n/2;z)\mid (x,y;z)\in L_{s-1}\},\quad\text{and}
> \]

Lean’s `recursiveEntry` produces these four blocks, shifting every entry of the two off-diagonal blocks by \(n/2\). `Ls_eq_recursiveSquare` identifies this construction with `Ls`, the XOR table. For the induction, quotient by \(2^{s-1}\) extracts the top bit, where the block offset follows \(L_1\). Remainder modulo \(2^{s-1}\) extracts the remaining bits, where the induction hypothesis applies. Division and remainder by a power of two commute with XOR. `rowSwap` uses `Equiv.swap` on the row argument, which gives the stated isotopism because the swap is an involution.

## A certificate for the actual greedy algorithm

Put \(n=2^s\). Name a row by its original value \(x\in\{0,\ldots,n-1\}\), even after the swap, so the symbol at column \(u\) of row \(x\) is \(x\oplus u\). A row is “later” if it is below the other row after the swap. The main object will be a set of blank columns \(B_x\) for each row. All other entries are clues.

For two distinct columns \(u,v\) in row \(x\), the only possible intercalate containing that pair has other row \(y=x\oplus u\oplus v\). Its four entries exchange in a second Latin square. Consider the following two certificate conditions.

1. For every clue at \((x,u)\), there is a later row \(y\) and a column \(v>u\) with \(v=u\oplus x\oplus y\), \(v\in B_x\) and \(u,v\in B_y\). The clue is the earliest entry of this intercalate in lexicographic row-column order.
2. The directed graph on \(B_x\) with an arc \(u\to v\), for \(u\ne v\), if \(y=x\oplus u\oplus v\) is later and \(u\in B_y\), is acyclic for every row \(x\).

To see condition 2 yields strong top-down completion, start after all earlier rows have been filled. The alternative symbol \(x\oplus v\), \(v\ne u\), is absent elsewhere in row \(x\) and column \(u\) exactly when \(v\) remains blank in row \(x\) and the later row \(y\) containing that symbol in column \(u\) has a blank there. Thus the available alternatives are precisely the outgoing arcs induced on the remaining blanks. Fill a sink, repeat in the same row, and then move down. Each clue is essential and has a private intercalate by condition 1, so the completed set of clues is 2–critical.

These conditions also prove that the set of clues is the true greedy critical set even though the greedy algorithm considers all Latin completions. Induct through its deletion order. At a blank, all the proposed clues are still present, so the certificate guarantees unique completion after deletion. At a clue, the three other entries in its intercalate are later in lexicographic order, hence already deleted. The alternate intercalate gives a distinct completion after deleting the clue. The algorithm therefore reaches exactly the prescribed set.

## Bit conventions and two elementary rules

All masks have \(s\) bits. Treat masks as sets of bit positions when using \(\subseteq, \cup, \cap, \setminus\), and as integers for numerical comparisons. Write \(\bar x\) for the complement and
\[
 W_x=\{u:\bar x\subseteq u\}.
\]
This is the ordinary set of blanks for row \(x\). A designated later row with \(B_y=W_y\) will be called ordinary. Two basic rules will be used throughout.

- **Canonical witness.** For \(u\notin W_x\), let \(D=\bar x\setminus u\), \(y=x\cup D\), and \(v=u\cup D\). Then \(y>x, v>u\), \(v\in W_x\), and \(u,v\in W_y\). If \(y\) is later and \(B_y\) contains \(W_y\), this proves condition 1.
- **Two columns in a later ordinary row.** When \(v=u\oplus x\oplus y\), \(u,v\in W_y\) is equivalent to \(x\subseteq y\) and \(\bar x\subseteq u\cup v\). Indeed the columns must agree and be set on \(\bar y\), forcing \(x\subseteq y\). Under this containment, outside \(x\) the columns differ on \(y\setminus x\) and agree on \(\bar y\), so their union covers \(\bar x\) just when they both contain \(\bar y\). Also, if both columns are in \(W_x\), then \(u\oplus v\subseteq x\), so \(y\subsetneq x\). This last fact will exclude arcs in most rows.

The identity swap, including \(n=1\), uses \(B_x=W_x\). The two rules give witnesses and no arcs. For an adjacent swap of an odd \(a\) and \(b=a+1\), use \(W_x\) for every row value as well. The only row-order reversal is the pair \(a,b\). The canonical witness for \(a\) cannot use \(b\) because \(a\) has bit 0 and \(b\) does not. A prospective arc in row \(b\) through the now later row \(a\) is impossible for the same reason, as it would require \(a\subseteq b\).

## A mask computation shared by three cases

We first give the three cases covered by one calculation.

| Swap | Values and order of the special rows | Odd row value \(z\) | Later partner \(z\oplus1\) |
|---|---|---|---|
| Even adjacent | \(a\) even, \(b=a+1\), order \(b,a\) | \(b\) | \(a\) |
| Distance two, even start | \(a=K+H-2, b=K+H-1, c=K+H\), order \(c,b,a\) | \(b\) | \(a\) |
| Distance two, odd start with \(H\ge 4\) | \(a=K+H-1, b=K+H, c=K+H+1\), order \(c,b,a\) | \(c\) | \(b\) |

For either distance-two swap, \(H\) is the highest power of two whose bit is changed between \(a\) and \(a+2\), and \(K\) is a multiple of \(2H\). Since adding 2 crosses the midpoint of that aligned \(2H\)-block, the pairs are exactly \((K+H-2,K+H)\) and \((K+H-1,K+H+1)\), with \(H\ge 2\). The odd-start case \(H=2\) is proved separately below.

Let \(S=\bar z\). When \(S\ne\varnothing\) let \(q\) be its least bit. Define
\[
 B_z=\{u:u\text{ odd}, S\subseteq u\}
        \cup \{u:u\text{ even}, S\ne\varnothing, q\notin u\},
 \qquad  B_{z\oplus1}=W_z.
\]
In the first case these are all special rows. In the second case set \(B_c=W_c\). In the third set \(B_a=W_a\). Rows after the special rows are ordinary. Before the special rows use \(B_x=W_x\) except that when \(x\) is even and \(x\subseteq z\), set
\[
 B_x=W_x\cup E_x(z),\qquad E_x(z)=\{u:u\cap\bar x=\bar z\}.
\]
These two parts are disjoint because \(x<z\). In the expanded rows every element of \(E_x(z)\) is even and every element of \(W_x\) is odd.

### The row \(z\)

For every nonempty \(D\subseteq S\), the row value \(z\cup D\) is ordinary and later. In the adjacent and third cases all these values are above the special values. In the second case the only larger special value \(c=K+H\) lacks bit 0, so cannot be \(z\cup D\).

If \(u\) is odd and misses a bit in \(S\), use the canonical witness. If \(u\) is even and contains all of \(S\), use row \(z\oplus1\) and \(v=u+1\). Otherwise a clue \(u\) must be even, contain \(q\), and miss some higher bit of \(S\). Take \(v\) to agree with \(u\) outside \(S\) and to contain exactly \(S\setminus\{q\}\) inside \(S\). It is blank and \(v>u\). With \(D=u\oplus v\) the later ordinary row \(z\cup D\) contains both columns in its blank set by the second rule. This gives all witnesses.

There are no arcs between two odd blanks through an ordinary later row, since their difference is contained in \(z\). Two even blanks both miss \(q\), so the prospective row \(y=z\oplus u\oplus v\) also misses \(q\). They cannot be a source through \(W_y\). In a mixed pair \(y\) is even, so an ordinary \(W_y\) requires bit 0, and arcs can only go from odd to even. The special partner \(z\oplus1\) cannot give an arc, as a mixed pair also differs at \(q\), and a same-parity pair cannot differ only at bit 0. When \(S\) is empty there are no even blanks, so this assertion holds as well. In the third case the other later special row is \(a\). The difference \(z\oplus a\) is even and includes bit 1, so neither a same-parity odd pair (which agree on \(S\), including bit 1), a same-parity even pair (both missing bit 1), nor a mixed pair has this displacement. The arcs in row \(z\) are acyclic.

### Other special rows

For an even adjacent swap, a clue of the later row \(a\) misses some bit of \(S\). Its canonical partner in row \(a\) therefore exceeds \(b\), and the canonical witness works using \(W_a\subseteq B_a\). Every pair in \(B_a=W_b\) has displacement contained in \(b\), giving partner \(y\subseteq b\), so no arcs.

For a distance-two even start, the same argument for \(a\) holds unless the canonical partner is \(c\), which requires \(H=2\) and that \(u\) misses only \(H\) among the bits in \(S\). In that case take the ordinary later row \(y=K+3\) and toggle both bits of values \(1,H\) in \(u\). This gives \(v>u\) because the \(H\)-bit is set in \(v\). Both columns are in \(W_y\) because they already cover \(S\setminus\{\text{bit of }H\}\), and \(v\in B_a\). Arcs in \(a\) are impossible as above. For row \(c\), the canonical partners exceed \(c\) and are ordinary. Both columns of a prospective arc are in \(W_c\), so a later partner must be \(a\) or \(b\) and a subset of \(c\). The only possibility is \(a\) when \(H=2\). The difference is then just the \(H\)-bit, and \(B_a\) requires it to be set. All such arcs therefore go from a column with that bit set to one without it.

For a distance-two odd start with \(H\ge 4\), the canonical partners of \(a\) cannot be \(b,c\), since those do not contain \(a\) (bit 1 suffices). The ordinary witnesses work and the last special row \(a\) has no arcs. For row \(b\) a clue misses a bit of \(S\), so its canonical partner is greater than \(c\) and ordinary. A pair in \(B_b=W_c\) has difference contained in \(c\), which gives \(y\subseteq c\) since \(b\subseteq c\). The only later row of value \(\le c\) is \(a\), which is not contained in \(c\). Thus row \(b\) has no arcs.

### Rows before and after the special rows

For an earlier row \(x\), every larger value is later. For a clue \(u\) the canonical witness works unless its partner is \(z\), the only value where \(W_y\) has lost entries. If the canonical partner is \(z\) then \(u\cap\bar x=\bar z=S\). When \(x\) is even this is exactly the added blank class, so it is not a clue. When \(x\) is odd the two canonical columns have the same parity. If odd, both are blank in \(z\). If even, use the partner \(z\oplus1\). Its displacement sets bit 0 of \(u\) as well as the bits of \(z\setminus x\), so the new column \(v\) is greater than \(u\), is in \(W_x\), and both \(u,v\) contain \(S\) as needed by \(B_{z\oplus1}\).

A row with \(B_x=W_x\) before the special rows has no arcs. For an expanded \(B_x\), two columns of the same class (\(W_x\) or \(E_x(z)\)) differ only on \(x\), so cannot have a later partner. A mixed pair differs on all of \(z\setminus x\) and on no bit outside \(z\). The prospective partner \(y=x\oplus u\oplus v\) is a subset of \(z\), contains \(z\setminus x\), and is odd. If \(y\ne z\), it is ordinary. The other special values are even or, in the third case, \(a\) is not contained in \(z\). The earlier expanded rows are all even. In this ordinary case some bit of \(x\) was reset in \(y\) and any arc source must be set on all such bits because it belongs to \(W_y\). The number of set bits in \(u\cap x\) strictly decreases along the arc \(u\to v\). If \(y=z\), no bit in \(x\) changes, and only the odd member of the mixed pair lies in \(B_z\), since the even member contains all of \(S\). Rank the odd class above the even class for ties in the count of set bits. This gives acyclicity. After the special rows all witnesses and the absence of arcs follow from the two basic rules in the original numerical order.

## The distance-two odd start with \(H=2\)

Here \(a=K+1, b=K+2, c=K+3\), in the order \(c,b,a\), with \(4\mid K\). Set \(Q=\bar c\), which uses only bits of value at least four. When \(Q\ne\varnothing\) write \(q\) for its least bit. The low part of a mask is its residue modulo four. Say \(u\) covers \(Q\) when \(Q\subseteq u\). The special blank sets are:

| Row value | Columns covering \(Q\) | Additional columns if \(Q\ne\varnothing\) |
|---|---|---|
| \(a\) | All low parts | None |
| \(b\) | Low part 2 or 3 | Low part 0 or 1, missing \(q\) |
| \(c\) | Low part 0 or 3 | Low part 1 or 2, missing \(q\) |

Ordinary rows after the triple use \(W_x\). Earlier rows use \(W_x\), also including \(E_x(b)\) if \(x\) has low part 0 and \(x\subseteq b\), or \(E_x(c)\) if \(x\) has low part 1 and \(x\subseteq c\). In either expanded row the two classes are disjoint.

### The special rows

For \(a\), a clue misses some bit of \(Q\), hence its canonical partner exceeds \(c\) and works. Any pair of blanks differs only in \(c\), giving a partner contained in \(c\), so no arcs to a later row.

For \(b\), a clue covering \(Q\) has low part 0 or 1. Use partner \(a\) with displacement 3, which gives a bigger blank column and both columns in \(B_a\). For a clue \(u\) missing some of \(Q\) and of low part 2 or 3, take \(v\) with all \(Q\) set, the same bits outside \(Q\) except setting bit 0. It is a larger blank. The difference \(D=u\oplus v\) is contained in \(\bar b=Q\cup\{0\}\), where \(\{0\}\) denotes bit position zero, with a nonempty \(Q\)-part. Since \(u\cup v\) covers \(\bar b\), row \(y=b\cup D>c\) gives the witness. The remaining clues have low part 0 or 1, miss some of \(Q\), and have \(q\) set. Use the same construction for \(v\) but set only \(Q\setminus\{q\}\) and set bit 0. The union still covers \(\bar b\), and \(v>u\) since \(u\) misses some higher bit of \(Q\). For acyclicity, two blanks from the class covering \(Q\) differ only on \(c\) and agree on bit 1, so their partner is not \(a\) and cannot exceed \(c\). Two additional blanks both miss \(q\) and bit 1. The partner is not \(a\), and an ordinary partner also misses \(q\), so its \(W_y\) cannot contain a source. A mixed pair cannot use \(a\), because it differs at \(q\). It differs at bit 1, so an ordinary partner lacks bit 1 and requires that bit of the source column. Such arcs go from first-class blanks to additional blanks.

For \(c\), a clue covering \(Q\) has low part 1 or 2. Use partner \(a\) (displacement 2) for low part 1 and \(b\) (displacement 1) for low part 2. Both lead to a blank of low part 3 with higher numerical value and the two columns in the other row's blank set. If \(u\) misses some of \(Q\) and has low part 0 or 3, fill all \(Q\)-bits in \(v\) and keep the other bits. This is the canonical witness through a later ordinary row. For any remaining clue \(u\), its low part is 1 or 2, it misses some bit of \(Q\), and \(q\) is set. Let \(v\) agree outside \(Q\) and have exactly \(Q\setminus\{q\}\) set there. It is a bigger blank and the witness through \(y=c\cup(u\oplus v)\) follows by the second rule, since their union covers \(Q\). For acyclicity a pair in the first class has difference contained in \(c\), so cannot use a later ordinary partner. Its low-part difference is 0 or 3, so it cannot use \(a,b\). A pair in the additional class also has low-part difference 0 or 3, and both miss \(q\), excluding \(a,b\) and ruling out an ordinary source. A mixed pair differs at \(q\), so it cannot use \(a,b\). Its low parts differ in exactly one bit. An ordinary partner then lacks that bit (both low bits of \(c\) are set), so an arc starts with the bit set and clears it. The number of set low bits is strictly decreasing. When \(Q=\varnothing\) the arguments concerning the additional classes are vacuous.

### Earlier rows

For a clue in an earlier row \(x<a\), canonical partners outside the triple work. The canonical partner \(a\) also works because \(B_a\supseteq W_a\). It remains to consider canonical partners \(b,c\), for which \(x\subsetneq y\) and \(u\cap\bar x=\bar y\). In particular \(u\) covers \(Q\), and its bits in the high part of \(K\setminus x\) are unset.

- If \(y=b\), then \(x\) has low part 0 or 2. In the first case \(u\in E_x(b)\) is a blank. In the second case \(u\) has low part 1 or 3. For low part 3, the canonical partner works. For low part 1 use row \(K\), which is later than \(x\) (as \(x<a\) with low part 2), and take \(v=u\oplus x\oplus K\). This sets every bit of \(K\setminus x\) and turns low part 1 into 3. It is bigger and in \(W_x\). Row \(K\) has \(u\in E_K(b)\) and \(v\in W_K\).
- If \(y=c\) and \(x\) has low part 0, the canonical columns have low parts 0 and 3, both in \(B_c\). With low part 1 of \(x\), \(u\in E_x(c)\) is already a blank. If \(x\) has low part 2 or 3, use the later row \(a\) and \(v=u\oplus x\oplus a\). Here the high part of \(x\) is a proper subset of \(K\), since \(x<a\). All high bits of \(K\setminus x\) are set in \(v\). The high-bit increase guarantees \(v>u\). For low part 2 of \(x\) this sends low parts 0 and 2 to 3 and 1, both compatible with \(W_x\). For low part 3 of \(x\), \(W_x\) has no restriction on the low part. In both cases \(v\in W_x\) and both columns cover \(Q\), so they are in \(B_a\).

For acyclicity in a row with no additions, both columns of any arc would give a partner contained in \(x\), which is earlier. In a row with additions two columns of the same class cannot give an arc for the same reason. In an expanded row of low part 0, a mixed pair has low parts 1 and 3, and its prospective partner has low part 2 and is a subset of \(b\). A partner other than \(b\) is ordinary and must omit some bit from the high part of \(x\). Along that arc the count of set bits in the high part of \(u\cap x\) strictly decreases: every such bit belongs to the source in \(W_y\) and is toggled to zero. If the partner is \(b\), no high bit of \(x\) changes, and only the low part 3 of the pair is in \(B_b\), since both columns cover \(Q\). Thus placing 3 above 1 breaks ties in the count.

In an expanded row of low part 1, a mixed pair takes a column of low part 2 or 3 and one of low part 0 or 1. Its partner is contained in \(c\) and has low part 2 or 3. If its high part differs from \(K\), it is ordinary and omits some high bit of \(x\): the partner contains every high bit of \(K\setminus x\) by the definition of the extra class. Again the high count strictly decreases along that arc. Otherwise the partner is \(b\) or \(c\), and no high bit of \(x\) changes. Partner \(b\) gives only the low-part arcs \(3\to0, 2\to1\), while partner \(c\) gives only \(0\to2, 3\to1\). These are all descending in the tie order \(3>0>2>1\). Thus all row digraphs are acyclic. For rows after the special rows the two basic rules give witnesses and no arcs as before.

This proves both certificate conditions for every swap of distance at most two and hence all three clauses of Conjecture 6.1.

The Lean proof uses the numerical value of the intersection mask wherever the written proof uses a count of retained bits. The required comparison follows because each such arc clears at least one bit and sets none in that intersection. The aligned odd-start case separates the bottom two bits from the remaining mask. Its finite calculations in `LatinLowCases` concern only those two bits. The high-bit arguments and the assembly of the certificates quantify over all orders.

## The displayed formula at order four

The source's proof of Lemma 3.4 agrees with bottom-to-top deletion. It needs every cell inspected before \((x,y)\) to lie in a lower row, or in the same row and to the right. Corollaries 3.5 and 4.2 also agree: no clue lies in the last row or column, and \(\operatorname{gcs}(L_s)=P_s\). Under the displayed formula both corollaries fail already at order four. Every greedy critical set printed in the source equals the bottom-to-top output of Algorithm A, with uniqueness tested over all Latin squares, and none equals the output for the displayed order. These are the six tables of §5.1, the two order-8 tables of §5.2, the nine order-8 tables of Appendices B and C and the order-16 table \(\operatorname{gcs}(\alpha_{12,14}L_4)\). The arXiv TeX source also contains, after `\end{document}`, ninety order-32 tables, which appear to be output of the author's computer search. All ninety also equal the bottom-to-top output. The printed \(P_3\) has one extra entry, symbol 7 at cell \((4,3)\), which is a separate typographical slip. At order four, for rows 0 and 1 swapped, the displayed formula instead gives

\[
 \begin{pmatrix}
 \cdot&\cdot&\cdot&\cdot\\
 0&\cdot&2&\cdot\\
 2&3&\cdot&\cdot\\
 \cdot&2&1&\cdot
 \end{pmatrix}.
\]

The Lean module `LatinPrinted` verifies its private intercalates relative to the printed scan and a descending column rank when filling in reverse row order. The generic certificate identifies the displayed set with Algorithm A's output over all Latin squares. Row 0 is empty, and the respective columns have two, two, two, and zero occupied entries, so row 0 cannot begin with a forced fill. Even if one tries to fill the whole row at once using row and column constraints, both \((1,0,3,2)\) and \((3,1,0,2)\) are compatible with the occupied entries. Thus the printed order also makes Theorem 5.1 false. The failure concerns only the direction of completion. Reversing the row order maps \(L_s\) to itself up to a relabelling of symbols, and it maps a swap at distance \(d\) to another swap at distance \(d\). So under the displayed formula the sets are still 2–critical and strong, but they complete bottom up rather than top down.

## Significance and prior work

The result is modest. It settles a conjecture from the concluding section of a 2006 paper with very few citations, about one explicit family of critical sets. Hämäläinen proved the case in which the two indices lie in the same aligned block of four in Theorem 5.1, using recursive templates. He reported checking the remaining cases by computer through order 32. The masks above also cover the aligned cases, so the proof gives Theorem 5.1 again by a uniform argument. Odd adjacent swaps across a block boundary follow easily from the ordinary masks because the swapped values are incomparable under bit containment. The substance of the extension is the pair of crossing distance-two families, \((4m+2,4m+4)\) and \((4m+3,4m+5)\), where the new masks and ranks account for binary carries across the block boundary.

Hämäläinen's Lemma 3.4 reproduces the least-trade characterization from Cavenagh, Hämäläinen, Donovan, and Khodkar (AWOCA 2004). The aligned templates of Theorem 5.1 do not extend across a block boundary, and the review found no order-preserving reduction by XOR translation or bit permutation. The review found no resolution in the indexed citing works, the searched Lean repositories and issue trackers, or the nearby literature. Zaker's *More results on greedy defining sets* studies a different notion, and Bean's thesis predates the conjecture. The 2026 paper of González-Regadera, Falcón, and Frau (arXiv:2609.21532; Des. Codes Cryptogr.) cites the source only for the greedy algorithm. Hämäläinen's later arXiv papers (2007–2010) concern latin bitrades, cyclic transversals and multi-latin squares, not greedy critical sets. Hämäläinen's 2007 PhD thesis, *Latin bitrades and related structures* (doi:10.14264/158725), was not read. Its repository page refused automated access (HTTP 403), and an earlier PDF link was dead. It may contain a version of the source. The journal version, also from 2007, still states Conjecture 6.1 as open.

## Provenance

GPT-6.2 Sol lanes found the proof and wrote the Lean formalization and this paper. Two Claude Opus 5.5 lanes reviewed the work: one before the Lean work, and a final check of the source reading, the Lean definitions and prior work. Each checked the masks and the source's tables by its own computation. This final revision of the paper was edited by the Claude Opus 5.5 final-check lane, and the mathematics and Lean statements are unchanged. This is all AI work. No human has checked it.
