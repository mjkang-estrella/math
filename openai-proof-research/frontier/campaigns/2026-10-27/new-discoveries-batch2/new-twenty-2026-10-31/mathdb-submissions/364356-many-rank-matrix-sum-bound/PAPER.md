# A uniform upper bound for sums of matrices of prescribed rank

## Abstract

Let \(F\) be a finite field of cardinality \(q\). If independent uniform \(n\times n\) matrices have prescribed ranks whose sum is at least \(2n\), the probability that their sum equals any given matrix is at most \(32768q^{-n^2}\). This proves Conjecture 5.5 of Nick Gill, Noam Lifshitz, László Pyber, and Endre Szabó with \(K(\epsilon)=\lceil 2/\epsilon\rceil\) and an absolute constant. The proof counts full-rank factorizations, bounds a fiber of unrestricted rectangular matrix multiplication, and uses a convolution inequality to handle tuples of arbitrary length. The counting theorem and its application to the conjecture are formalized in Lean 4 and Mathlib.

## 1. The source conjecture

Write \(\operatorname{Mat}^{n\times n}_q\) for the additive group of matrices over \(F\). In [1, Definitions 5.18–5.20], vectors are columns and matrices act on the left. The count \(\mathcal R^{n\times n}_q(r)\) is the number of \(n\times n\) matrices of rank \(r\). For a fixed \(T\) of rank \(t\), the count \(\mathcal N^{n\times n}_q(r_1,\ldots,r_k;t)\) is the number of ordered \(k\)-tuples of the indicated ranks that sum to \(T\). We write \(R_n(r)\) and \(N_n(\mathbf r;T)\) for these counts, keeping the target matrix in the notation.

To verify that the latter count depends only on \(t\), take a basis \(u_1,\dots,u_t\) of the image of \(T\) and choose lifts \(v_j\) with \(Tv_j=u_j\). Complete the \(v_j\) with a basis of \(\ker T\). These vectors form a basis because applying \(T\) to a linear relation forces the coefficients of the lifts to vanish, and the number of vectors is \(n\) by rank–nullity. Complete the \(u_j\) to a basis of the codomain. In these bases the matrix of \(T\) is \(\operatorname{diag}(I_t,0)\). Two targets of rank \(t\) therefore have the form \(T\) and \(LTR\) for two invertible matrices \(L,R\). The map \(X_i\mapsto LX_iR\) preserves each rank and sends the sum to \(LTR\). Its inverse uses \(L^{-1},R^{-1}\), so the two tuple counts agree.

Conjecture 5.5 in [1, §5.1] opens with “For all \(\epsilon>0\) there exists a number \(K(\epsilon)\) with the following property”. In symbols the hypotheses are \(n\in\mathbb Z_{>0}\), \(0\le s\le n\) with \(s\) integral, \(k\ge K(\epsilon)\), and \(r_i\in\mathbb Z\) with \(\epsilon n\le r_i\le n\) for every \(i\). Its displayed estimate is
\[
\mathcal N^{n\times n}_q(r_1,\ldots,r_k;t)
=\operatorname{O}(1)\,
\frac{\mathcal R^{n\times n}_q(r_1)\cdots\mathcal R^{n\times n}_q(r_k)}{q^{n^2}}.
\]
The printed hypotheses use \(s\) where the displayed estimate and the definitions use \(t\). We quantify over all target matrices, equivalently all \(0\le t\le n\). Each such \(t\) is realized by \(\operatorname{diag}(I_t,0)\). Question 5.22 repeats the conjecture. Its big-O specifies an upper bound, as used for the same counts in [1, Theorem 5.3 and Lemma 5.21]. We prove the absolute convention in which a single constant works before the choice of \(\epsilon\), uniformly in the field, dimension, tuple length, ranks and target. This implies every weaker reading of the big-O, in particular one whose constant may depend on \(\epsilon\). [Gill, Lifshitz, Pyber, and Szabó, arXiv v2, §§5.1 and 5.6](https://arxiv.org/pdf/2408.07800v2)

Theorem 5.3 and Lemma 5.21 of [1] prove the three-summand estimate when each rank is at least \(2n/3\). Their Lemma 5.26 gives a two-summand upper bound with the extra factor \(q^{(2n-r_1-r_2-t)^2/4}\), and gives an absolute bound in the range \(r_1+r_2+t\ge 2n\). Fact 5.23 records injective-map, subspace and rank-class counts, together with the bounds \(I_q(d,D)\ge q^{dD}/4\) and \(S_q(d,D)\le4q^{d(D-d)}\). The argument below reproves the instances of these two bounds that it needs, \(p_n\ge1/4\) in §3 and \(G(n,d)\le4q^{d(n-d)}\) in §5, from the ordered-independent-column count underlying Fact 5.23, and gives a uniform bound once the total rank reaches \(2n\). [Gill, Lifshitz, Pyber, and Szabó, arXiv v2, §5](https://arxiv.org/pdf/2408.07800v2)

## 2. The uniform theorem

**Theorem.** Let \(F\) be any finite field, \(q=|F|\), and \(n,k\ge0\) integers. Let \(\mathbf r=(r_1,\ldots,r_k)\) be a tuple of nonnegative integers with \(\sum_i r_i\ge 2n\). For every \(T\in\operatorname{Mat}^{n\times n}_q\),
\[
q^{n^2}N_n(\mathbf r;T)\ \le\ 32768\prod_{i=1}^k R_n(r_i).
\tag{1}
\]
If some \(r_i>n\), the corresponding class is empty and both sides vanish. If \(n=0\) and all ranks are possible, there is one matrix and one admissible tuple with that target, including when \(k=0\). Thus (1) holds in both cases. In what follows \(n\ge1\) and \(0\le r_i\le n\).

For those possible ranks, the diagonal with \(r_i\) initial ones belongs to the \(i\)-th class. In the product of the uniform distributions on the classes, the sample space has cardinality \(\prod_i R_n(r_i)>0\), and exactly \(N_n(\mathbf r;T)\) outcomes sum to \(T\). Division of (1) gives the probability formulation in the abstract.

## 3. Independent columns and the cost of the rank restrictions

Let \(I(n,r)\) count injective maps \(F^r\to F^n\) for \(0\le r\le n\). A matrix is injective exactly when its ordered columns are linearly independent. After \(j\) independent columns have been selected, every vector of their span has a unique \(j\)-tuple of coefficients, so the span contains \(q^j\) vectors. There are \(q^n-q^j\) possible next columns. Multiplying the number of choices at each step gives
\[
I(n,r)=\prod_{j=0}^{r-1}(q^n-q^j),\qquad
p_r=\frac{I(n,r)}{q^{nr}}
=\prod_{j=0}^{r-1}(1-q^j/q^n).
\tag{2}
\]
For \(r=0\) both products are \(1\). Transposing gives the same count for surjective maps \(F^n\to F^r\), since a matrix has equal row and column rank and surjectivity is full row rank.

We first prove \(p_n\ge1/4\), allowing \(n=0\) for later use with subspaces. For fixed \(n\), the inequality \(p_r\ge1-q^r/q^n\) follows by induction for \(0\le r\le n\). At \(r=0\), \(p_0=1\) suffices. For a successor, put \(x=q^r/q^n\). Since \(r<n\) and \(q\ge2\), \(0\le x\le1\), so multiplying the induction hypothesis by \(1-x\) is valid. This gives
\[
p_{r+1}\ge (1-x)^2=1-2x+x^2\ge1-qx.
\]
For \(n\ge1\) it follows that \(p_{n-1}\ge1-q^{-1}\). Multiplying by the last factor \(1-q^{-1}\) gives \(p_n\ge(1-q^{-1})^2\ge1/4\). At \(n=0\), \(p_0=1\).

We next prove \(p_r^n\ge p_n^r\). Put \(a_j=1-q^j/q^n\) for \(0\le j\le n\), where \(a_n=0\) is useful when the tail is empty. These factors are nonnegative and nonincreasing. Write \(B=\prod_{j=r}^{n-1}a_j\), so \(p_n=p_r B\). Every head factor is at least \(a_r\) and every tail factor is at most \(a_r\). Thus \(p_r\ge a_r^r\) and \(B\le a_r^{n-r}\), which also hold for empty products. Taking powers on nonnegative numbers gives
\[
p_n^r=p_r^r B^r
\le p_r^r a_r^{r(n-r)}
\le p_r^r p_r^{n-r}=p_r^n.
\tag{3}
\]

For a rank tuple with total \(R=\sum_i r_i\le 3n\), multiply (3) over the tuple. Since \(p_n\ge1/4\), this gives
\[
\left(\prod_i p_{r_i}\right)^n\ge p_n^R\ge 4^{-R}\ge 4^{-3n}.
\]
The map \(x\mapsto x^n\) increases strictly for \(x\ge0\) and \(n>0\), so \(\prod_i p_{r_i}\ge 4^{-3}\). Squaring and substituting (2) gives the count inequality
\[
q^{2nR}\le 4096\prod_i I(n,r_i)^2 .
\tag{4}
\]

## 4. Factorizations of prescribed ranks

Fix \(X\) of rank \(r\). For \(X=UV\) with \(U:F^r\to F^n\) injective and \(V:F^n\to F^r\) surjective, surjectivity gives \(\operatorname{im} U=\operatorname{im} X\). Thus \(U\), with codomain restricted to this image, is an isomorphism. Conversely, for any isomorphism \(U:F^r\to\operatorname{im}X\), view \(U\) as a map into \(F^n\) and set \(V=U^{-1}X\), where \(X\) takes values in its image. This \(V\) is surjective. It is the unique map giving \(UV=X\) for that \(U\) because \(U\) is injective.

The cardinality of the isomorphism set is \(I(r,r)\). Indeed, composing with the inverse of any fixed isomorphism identifies the set with the automorphisms of \(F^r\), and every square injective map is an automorphism. There is at least the identity automorphism, so \(I(r,r)>0\). The argument includes \(r=0\). Every full-rank pair \((U,V)\) yields a matrix of rank \(r\). Counting the pairs directly using (2) and by their image under multiplication gives
\[
I(n,r)^2=R_n(r)I(r,r).
\tag{5}
\]

Let \(D=\prod_i I(r_i,r_i)\) and let \(M_{n,R}(T)\) count unrestricted pairs \(W:F^R\to F^n,\ Y:F^n\to F^R\) with \(WY=T\). For every tuple counted by \(N_n(\mathbf r;T)\), independent choices of the factorizations above give exactly \(D\) tuples of rectangular factors. In the direct sum \(F^R=\bigoplus_i F^{r_i}\), concatenate the \(U_i\) to form \(W\) and stack the \(V_i\) to form \(Y\). There is no loss of data since the coordinate blocks recover the factors. Applied to \(v\in F^n\) this product gives \(WYv=\sum_i U_i(V_iv)=Tv\). The resulting pairs belong to the unrestricted fiber. This proves
\[
N_n(\mathbf r;T)D\le M_{n,R}(T).
\tag{6}
\]

## 5. Unrestricted rectangular multiplication

Fix \(n,R\) with \(R\ge2n\). For each \(W\), set \(H=\operatorname{im}W\), \(d=\dim H\) and \(s=n-d\). There are at most \(q^{dR}\) possible \(W\) with this image, since each of the \(R\) columns must lie in \(H\), a space with \(q^d\) vectors.

For fixed \(W\), a column \(y\) of a solution \(Y\) must map to the corresponding column of \(T\). If one solution \(y_0\) exists, the solutions are exactly \(y_0+\ker W\), since \(Wy=Wy_0\) exactly when \(W(y-y_0)=0\). The kernel has dimension \(R-d\) by rank–nullity and contains \(q^{R-d}\) vectors. The \(n\) column equations involve separate columns, so the total number of possible \(Y\) is at most \(q^{(R-d)n}\), with count zero when an equation has no solution.

Let \(G(n,d)\) be the number of \(d\)-dimensional subspaces of \(F^n\). The map taking an injective \(F^d\to F^n\) to its image has \(I(d,d)\) maps over each such subspace. The fiber consists of the isomorphisms onto that subspace, and composing with a fixed inverse gives the automorphisms of \(F^d\) as in §4. Hence \(G(n,d)I(d,d)=I(n,d)\le q^{nd}\), the latter bound counting all linear maps. By (2) and \(p_d\ge1/4\) in ambient dimension \(d\), \(I(d,d)\ge q^{d^2}/4\). This applies also to \(d=0\), so for all \(0\le d\le n\),
\[
G(n,d)\le4q^{d(n-d)} .
\]
The three counts bound the contribution of codimension \(s\) to \(q^{n^2}M_{n,R}(T)\) by \(4q^a\), where
\[
a=n^2+ds+dR+(R-d)n,\qquad
a+s^2+(R-2n)s=2nR .
\]
The identity follows by replacing \(d\) with \(n-s\) and expanding. Because \(R\ge2n\) and \(s^2\ge s\) for every nonnegative integer \(s\), \(a+s\le2nR\). Using \(q\ge2\), we obtain \(q^a\le q^{2nR}2^{-s}\). All possible images are included among the codimensions \(0\le s\le n\). The finite geometric sum \(\sum_{s=0}^n2^{-s}=2-2^{-n}\) follows by subtracting half of the sum from the sum. Consequently
\[
q^{n^2}M_{n,R}(T)\le 4q^{2nR}\sum_{s=0}^n 2^{-s}\le8q^{2nR}.
\tag{7}
\]

## 6. Assembly and the source quantifiers

If \(2n\le R\le3n\), combine (6), (7), (4) and (5), in that order, to obtain
\[
\begin{aligned}
q^{n^2}N_n(\mathbf r;T)D
&\le q^{n^2}M_{n,R}(T)
\le 8q^{2nR}\\
&\le 8\cdot4096\prod_i I(n,r_i)^2
=32768D\prod_i R_n(r_i).
\end{aligned}
\]
Each factor of \(D\) is positive, so cancellation proves (1) in the indicated range.

For arbitrary \(R\ge2n\) with \(n>0\) and all ranks valid, induct on the tuple length \(k\). An empty tuple cannot satisfy the rank-sum hypothesis. For a nonempty tuple, put \(\mathbf r'=(r_2,\ldots,r_k)\). If its total rank is at least \(2n\), the induction hypothesis bounds each \(N_n(\mathbf r';T-A)\) uniformly in the target \(T-A\). Summing these bounds over \(A\) in the rank-\(r_1\) class gives (1), since choosing \(X_1=A\) leaves precisely the tail-sum equation \(\sum_{i\ge2}X_i=T-A\). If the tail total is less than \(2n\), adding \(r_1\le n\) gives \(R\le3n\), and the preceding case applies to the whole tuple. Together with the cases in §2, this proves the theorem for all its stated parameters.

To prove Conjecture 5.5, choose \(K(\epsilon)=\lceil2/\epsilon\rceil\) for each \(\epsilon>0\). If \(k\ge K(\epsilon)\), multiplication by the positive \(\epsilon\) gives \(k\epsilon\ge2\). If every \(r_i\ge\epsilon n\) and \(n>0\), summing the rank inequalities gives \(\sum_i r_i\ge k\epsilon n\ge2n\). Divide (1) by \(q^{n^2}>0\) and use the fixed-target interpretation of §1. The constant is \(32768\) for every \(\epsilon\).

## 7. Exact checks

The table gives exact maxima of \(q^{n^2}N_n(\mathbf r;T)/\prod_i R_n(r_i)\) over every target and over rank multisets of length \(1\) through the indicated limit with total rank at least \(2n\). Permuting ranks just permutes the coordinates of a tuple. In every row an attaining tuple is \((n,n)\) with \(T=0\). At that target \(Y=-X\) gives a bijection between the single full-rank matrix class and the summing pairs, so the counts in the last column also follow from (2).

| \(q\) | \(n\) | Max. \(k\) | Rank multisets | Exact maximum | \(N_n((n,n);0)\) |
|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 6 | 15 | \(2\) | 1 |
| 2 | 2 | 6 | 51 | \(8/3\) | 6 |
| 2 | 3 | 5 | 68 | \(64/21\) | 168 |
| 2 | 4 | 4 | 51 | \(1024/315\) | 20160 |
| 3 | 2 | 5 | 29 | \(27/16\) | 48 |

The script of the independent adversarial review of the hand proof, written before formalization, obtains these maxima by modular row reduction and exact convolution. For \(q=2\), the additive group has coordinates in \(\mathbb F_2\). The Walsh–Hadamard procedure applies the integer butterfly \((a,b)\mapsto(a+b,a-b)\) along each coordinate. Its rows are the sign functions \(x\mapsto(-1)^{b\cdot x}\) for binary indices \(b\). The transform of an additive convolution is the pointwise product because the sign evaluated at \(x+y\) is the product of the two signs. Applying the transform twice multiplies by the group order, since the square of each coordinate butterfly is twice the identity. For \(q=3\) the script uses the direct convolution recurrence by adding each possible next matrix to each current sum. A separate script enumerates the rectangular factorization fibers, image fibers, and product fibers in small dimensions, including widths up to \(4\) over \(\mathbb F_2\) in dimension \(2\). The checks supply examples. The theorem follows from the finite-set proof.

## 8. Lean correspondence

The declarations below are in namespace `MatrixSum`. The Lean proof uses rational inequalities for normalization and natural-number cardinalities for the theorem. The following table identifies the main proof steps and differences in presentation.

| Step | Lean declarations and implementation |
|---|---|
| Definitions and target rank | `Mat`, `RankClass`, `SumClass`, `rankCount`, and `sumCount` use Mathlib's `Matrix.rank` and the natural cardinalities of subtypes. `sumCount_eq_of_rank_eq` uses Mathlib's `Matrix.exists_rank_normal_form` and a simultaneous reindexing to reach a common block matrix. Section 1 proves the normal form directly by choosing bases. |
| Independent columns and transposition | `injective_iff_rank`, `surjective_iff_rank`, `injective_iff_cols`, `injectiveCount_eq`, `surjectiveCount_eq`, and `injectiveCount_normalized` prove (2). Lean uses Mathlib's `card_linearIndependent` for the ordered-column count. |
| Conditioning bound | `proportion_ge_sub`, `proportion_square_ge_quarter`, `proportion_pow_ge`, `proportion_tuple_ge`, and `injective_tuple_bound` prove (3)–(4). Section 3 matches the Lean argument. The original reviewed proof bounded the square proportion by a geometric tail and compared all head–tail pairs. Here the recurrence \(p_r\ge1-q^r/q^n\) and the single threshold \(a_r\) give the corresponding estimates. |
| Fixed-rank fibers and packing | `rangeFiberEquiv`, `card_rangeFiber`, `range_product`, `factorFiber_card`, and `card_factors` prove the factorization identities. `blocks_bound` uses the block coordinate type \(\sum_i\mathrm{Fin}(r_i)\), meaning a dependent sum of index types, and injects admissible factor tuples into the unrestricted product fiber to prove (6). The original proof expressed the same comparison as conditioning independent uniform choices. |
| Uniform rectangular product bound | `subspace_count_le`, `left_count_le`, `linearFiber_le`, and `right_count_le` prove the three counts in §5. Lean uses injections for the two fiber upper bounds. `product_stratum_le` groups first by codimension, then by image and left factor. `exponent_le`, `halfGeom_le` and `product_bound` prove (7) by nonnegative powers and rational comparisons. |
| Window, all tuples, and conjecture | `totalRank_sum_bound_window` performs the cancellation. `sumCount_cons` and `extend_bound` sum a uniform tail estimate. `totalRank_sum_bound_pos` uses the tail induction in §6, whereas the reviewed proof takes a shortest prefix of total rank at least \(2n\) and averages over its complement. `totalRank_sum_bound` includes dimension zero and impossible ranks. `manyRanks_explicit` supplies the ceiling and constant. `manyRanks_equidistribution` inhabits `SourceConjecture`. |

The complete Lean text is in the source appendix. The build report gives the endpoint signatures, clean-build record, and kernel axiom audit.

## 9. Scope and sources consulted

The theorem supplies a uniform upper bound for the point probabilities. It gives no matching lower bound, optimal constant, or estimate of an error relative to the uniform distribution. The source statement and the earlier matrix estimates were checked against arXiv v2 of [1]. ArXiv v1, any journal version of [1], and the full texts of the companion paper and of the related work located by that review's literature search, which the review read only in abstract or snippet, were unread for this manuscript. The literature observations are limited to that review and the cited preprint. The argument and formalization establish the stated implication from the total rank hypothesis.

## References

1. Nick Gill, Noam Lifshitz, László Pyber, and Endre Szabó. *Initiating the proof of the Liebeck–Nikolov–Shalev conjecture*. arXiv:2408.07800v2 [math.GR], 24 September 2024. [Preprint](https://arxiv.org/abs/2408.07800v2)
