# Excerpts (verbatim pdftotext -layout) for review of MathDB 334207

## Kurz, arXiv:2507.07728v1 (10 Jul 2025), sha256 ffaca521ef8bdf298b41480d075b74f03f3df3adad6706f1a48f1c90f774c0ca
Lemma 3.3 Let G1 be a generator matrix of an [n1 , k, d1 ]bq code and G2 be a generator
matrix of an [n2 , k, d2 ]bq code. If the first b − 1 columns of G1 and G2 coincide, then
appending G2 to G1 is the generator matrix of an [n1 + n2 , k, d1 + d2 ]bq code.


                                               11
Definition 3.4 We call an [n, k]bq code C faithful if the restriction of the codewords to
the coordinates i, i + 1, . . . i + b − 1 (read modulo n) form an [b, b]bq code for each index
0 ≤ i ≤ n − 1.

    In other words, an [n, k, d]bq code is faithful iff the projective b − (n, k, n − d)q system
is faithful, where the generator matrix can be chosen arbitrarily. If S is an arbitrary h −
(n, k, s)q system, then we can obtain a faithful h − (n, k, ≤ s)q system S ′ by replacing
each element S ∈ S with dim(S) < h by a b-space S ′ with S ≤ S ′ . A similar results also
holds for [n, k]bq codes.

Lemma 3.5 Let C be an [n, k, d]bq code with k ≥ b. Then, there exists a faithful [n, k, ≥ d]bq
code C ′ .
Lemma 3.5 Let C be an [n, k, d]bq code with k ≥ b. Then, there exists a faithful [n, k, ≥ d]bq
code C ′ .

P ROOF. We iteratively construct a generator matrix Gi of an [n, k, ≥ d]bq code such that
i subsequent columns span an i-space for all 0 ≤ i ≤ b, where the column indices are
read modulo n. Going from Gi to Gi+1 we modify just one column, so that the length
remain n during our entire construction. The improvement property we maintain during
the construction is the following. On the way from Gi to Gi+1 we assume that we have
already constructed a generator matrix U of an an [n, k, ≥ d]bq code such that i subsequent
columns span an i-space. In the next step we construct a generator matrix U ′ of an an
[n, k, ≥ d]bq code such that i subsequent columns span an i-space, ⟨uj , uj+1 , . . . , uj+i ⟩ ≤
 u′j , u′j+1 , . . . , u′j+i for all 0 ≤ j ≤ n − 1 and that the dimension increases at least once,
where u0 , . . . , un−1 are the columns of U , u′0 , . . . , u′n−1 are the columns of U ′ , and the
indices are read modulo n. Let us denote the index where we change a column by h, i.e.,
we have uj = u′j for all 0 ≤ j ≤ n − 1 with j ̸= h. Let us first observe that U ′ generates
an [n, k]bq code if U does. To this end we consider

     ⟨u′0 , u′1 , . . . , u′n−1 ⟩
   = ⟨u′h , u′h+1 , . . . u′h+i , ⟩, ⟨u′j |0 ≤ j ≤ n − 1, j ∈
                                                            / [h, h + i], j ∈
                                                                            / [h − n, h + i − n]⟩
   = ⟨u′h , u′h+1 , . . . u′h+i , ⟩, ⟨uj |0 ≤ j ≤ n − 1, j ∈
                                                           / [h, h + i], j ∈
                                                                           / [h − n, h + i − n]⟩
   ≥ ⟨uh , uh+1 , . . . uh+i , ⟩, ⟨uj |0 ≤ j ≤ n − 1, j ∈  / [h, h + i], j ∈
                                                                           / [h − n, h + i − n]⟩
   = ⟨u0 , u1 , . . . , un−1 ⟩.

We can perform the same computation for the span of b subsequent columns of U and U ′
to conclude that the minimum b-symbol distance does not decrease.
   As G0 we can take an arbitrary generator matrix G of C. For the construction of G1
we iteratively replace each occurring zero vector by an arbitrary non-zero vector. Clearly,
we have ⟨uj ⟩ ≤ u′j for all 0 ≤ j ≤ n − 1 since uj = u′j if j ̸= h and u′h is the zero

                                                12
vector. Moreover, we have dim(⟨u′h ⟩) = 1 > 0 = dim(⟨uh ⟩). Here we assume that we
directly set Gi+1 = Gi , if Gi already has the desired property of Gi+1 , and do not consider
modifications from U to U ′ .
      Now we assume that we have a generator matrix U such that all i subsequent columns
span an i-space and that there exists a index 0 ≤ j ≤ n − 1 such that the columns
uj , . . . , uj+i also span an i-space and indeed not span an (i + 1)-span. So, we have
⟨uj , . . . , uj+i−1 ⟩ = ⟨uj+1 , . . . , uj+i ⟩. Since the span of all n columns has dimension k,
we can assume ⟨uj+1 , . . . , uj+i ⟩ ̸= ⟨uj+2 , . . . , uj+i+1 ⟩ for i < b ≤ k by possibly increas-
ing the initial index j. With this we choose h = j + i (modulo n) and set u′h = uh + uh+1 .
For brevity we set Sl := ⟨ul , . . . , ul+i−1 ⟩, Sl′ := ⟨u′l , . . . , u′l+i−1 ⟩, Tl := ⟨ul , . . . , ul+i ⟩, and
Tl ′ := ⟨u′l , . . . , u′l+i ⟩ for all 0 ≤ l ≤ n − 1, so that e.g. Sj = Sj+1 ̸= Sj+2 and dim(Tj ) = i.
Since ⟨uh , uh+1 ⟩ = ⟨u′h , u′h+1 ⟩ we have Sl = Sl′ for l ∈        / {j + 1, j + 1 − n} and Tl = Tl ′
l ∈/ {j, j − n}. Since Sj+1 ̸= Sj+2 we have Tj′ > Tj , dim(Sj+1                ′
                                                                                   ) = i, Sj′ ̸= Sj+1   ′
                                                                                                            , and
  ′            ′                 ′
Sj+1 ̸= Sj+2 . Thus, U satisfies the required property.                                                        □

    We remark that the code constructed in Proposition 3.2 is faithful.

## Ding–Zhang–Ge, arXiv:1609.09236v1, Theorem 2.6 and Lemma 3.12
Theorem 2.6. There exists a linear MDS (n, d + 2b − 2)q b-symbol code C if there exists a matrix with
d + b − 2 rows and n ≥ d + 2b − 2 ≥ 2b columns over Fq , denoted by H = [H0 , H1 , · · · , Hn−1 ], where
Hi (0 ≤ i ≤ n − 1) is the i-th column of H, satisfying:
   1. any d − 1 columns of H are linearly independent;

   2. there exist d linearly dependent columns;

   3. any d+b−2 cyclically consecutive columns are linearly independent, i.e., Hi , Hi+1 , · · · , Hi+d+b−3
      are linearly independent for 0 ≤ i ≤ n − 1, where the subscripts are reduced modulo n.
Proof. Let C be the linear code with parity check matrix H. Then the first two conditions in-
dicate that C is an [n, n − d − b + 2, d] linear code with size q n−d−b+2 . For an arbitrary code-
word c = (c0 , c1 , · · · , cn−1 ) ∈ C, if there exists j such that cj = cj+1 = · · · = cj+b−2 = 0 and
cj+b−1 6= 0, where the subscripts are reduced modulo n, then one can consider the vector v =
(cj+b−1 , · · · , cn−1 , c0 , · · · , cj+b−2 ). Rewrite v as v = (v0 , v1 , · · · , vt , 0, · · · , 0) for some t ≤ n − b, where
v0 , vt 6= 0. We also have t ≥ d + b − 2, since any d + b − 2 cyclically consecutive columns are linearly
independent. Moreover, there are at least d nonzero elements in the set {v0 , v1 , · · · , vt }. It is easy to
see wtb (c) = wtb (v) ≥ d + 2b − 2. If there does not exist j such that cj = cj+1 = · · · = cj+b−2 = 0 and
cj+b−1 6= 0, then it is easy to see that wtb (c) = n. Hence db ≥ d + 2b − 2.
Lemma 3.12. There exists a linear MDS (n, 2b)q b-symbol code C if there exists a set S of n ≥ 2b
vectors of V (b, q) satisfying:
   1. there exist 2 linearly dependent vectors;
   2. any b cyclically consecutive vectors are linearly independent.

## Shi–Zhu–Helleseth, arXiv:2109.13764, Theorem 23
Theorem 23. A cyclic code C with parameters [n, k]q is a b-symbol MDS code if b = k.
Moreover, db (C) = n if b ≥ k.
Proof. Every nonzero codeword in C is generated by recursion of degree k and thus has
at most k − 1 consecutive zeros. According to Lemma 20, we get the desired result.

## Liu–Pan, arXiv:2103.16299, Corollary 5.3 and Example 5.4
