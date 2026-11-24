# MathDB 348549 — sparse 0–1 determinants

**Complete proof and Lean formalization. Both unconditional endpoints compile; the final audit and fresh printed-appendix replay are recorded in REPORT.md.**

## Printed statement and definitions

Araujo–Balogh–Wang, *Maximum determinant and permanent of sparse 0-1 matrices*, arXiv:2011.01892v1, Conjecture 1, states:

> Conjecture 1 (Bruhn, Rautenbach). If $A \in \{0, 1\}^{n\times n}$ has at most $3n$ non-zero entries, then $\det(A) \le 24^{n/7}$.

This transcribes the supplied source PDF’s Conjecture 1, page 20 (the cached text is `sources/det-source-v1.txt`, line 1273 in the discovery lane); superscripts are restored from the PDF text extraction. The source alphabet is exactly $A \in \{0, 1\}^{n\times n}$ and the sparsity requirement is “at most $3n$ non-zero entries.”

The MathDB record reads verbatim:

> Let $A\in\{0,1\}^{n\times n}$ have at most $3n$ non-zero entries. **Bruhn–Rautenbach's conjecture.** The determinant of $A$ is at most $24^{n/7}$.

There are no further source definitions: the objects are square matrices with entries 0 or 1, and sparsity counts nonzero entries. In Lean they are literal `Matrix (Fin n) (Fin n) ℤ`, with `∀ i j, A i j = 0 ∨ A i j = 1` and `(Finset.univ.filter (fun p : Fin n × Fin n => A p.1 p.2 ≠ 0)).card`. The paper uses the number of ones m; with this alphabet it is exactly that nonzero-entry count. `SparseStatement.lean` defines these objects directly, not via a surrogate Boolean model.

We prove the stronger absolute-value assertion for every natural n, including n=0:

    A in {0,1}^{n×n}, number of ones m <= 3n
      implies |det A| <= 24^(n/7).

For integer matrices, an endpoint equivalent to this stronger absolute-value assertion and avoiding fractional powers is

    |det A|^7 <= 24^n.

No row-degree, column-degree, regularity, connectedness, or nonsingularity hypothesis is added.

## Constants

All logarithms are natural. Set

    L = log(9/2),
    g = (81/49)(L - 7/2),
    b = 9/2 - 4g/9,
    a = -L - 1 + 4g/81,
    lambda = 5/4,
    eta = (2/3)log 3 - 1/3 + g/81,
    c = (a + 2lambda)/2,  d = eta/2.

Useful approximate values, not used as proofs, are

    g = -3.299382262..., b = 5.966392116..., a = -2.667009854...,
    eta = 0.358341744..., c = -0.083504927..., d = 0.179170872....

We shall use eta>0, c+d>0, and

    c+3d = log(24)/7.                                      (1)

The last identity follows by substituting g=(81/49)(L-7/2), and log(9/2)=2log 3-log 2. The scalar inequalities below include a rational way of verifying the signs; no decimal approximation is assumed.

## Lemma 1: logarithmic quadratic majorant

For 0<x<=1,

    log x <= a + b x + g x^2.                              (2)

Proof. Before rescaling, put q=(log(9/2)-7/2)/49, B=1/2-4q and A=log 2-1+4q. The quadratic A+Bt+qt^2 agrees with log t at t=2 and t=9, and their derivatives agree at t=2. Its difference from log t has derivative

    B + 2qt - 1/t = 2q(t-2)(t+1/(4q))/t.

Here q<0, and the second root t=-1/(4q) lies strictly between 2 and 9. Consequently the difference decreases to zero at 2, increases until the second root, and then decreases to zero at 9. Its limit as t tends to zero is positive infinity. Thus it is nonnegative throughout 0<t<=9. Substitute t=9x and subtract log 9 to get (2). The elementary sign bounds needed here follow, for example, from -33/10<g<-329/100.

## Lemma 2: the integer-degree inequality

For integers r,s>=2 put x=1/r, y=1/s,

    u_r = (x+1/3)/2,  u_s = (y+1/3)/2,

and define

    Q(r,s) = 2u_r/(rs) - u_r^2/r
             +2u_s/(rs) - u_s^2/s - 1/(r^2s^2),

    F(r,s) = (log r)/r + (log s)/s + b/(rs) + g Q(r,s).

Then

    F(r,s) <= eta + lambda(1/r+1/s).                       (3)

Proof. Write F(x,y) for the same expression in reciprocal variables. Expanding gives

    Q = xy(x+y+2/3) - (x^3+y^3)/4
        -(x^2+y^2)/6 -(x+y)/36 - x^2y^2.

An exact factorization yields

    (F(x,x)+F(y,y))/2 - F(x,y)
      = (x-y)^2 [b/2+g(x+y+1/3-(x+y)^2/2)].               (4)

Since 0<x,y<=1/2, t=x+y is in (0,1], and t+1/3-t^2/2<=5/6. As g<0, the bracket in (4) is at least

    b/2+5g/6 = 9/4+11g/18 > 0.

It therefore suffices to prove the diagonal case. Define, for real k>=2,

    H(k) = (log k - 5/4 - g/36)/k
           +(9/4-g/18)/k^2 + 3g/(4k^3) - g/(2k^4).

Then H(k)=F(k,k)/2-lambda/k and eta=2H(3). Direct scalar checks give

    H(2)<H(3),  H(4)<H(3).                                (5)

For completeness, H is strictly decreasing on [4,infinity). Put D=9/2-g/9 and J(k)=k^2 H'(k). Then

    J(k) = 9/4+g/36-log k-D/k-9g/(4k^2)+2g/k^3,
    J'(k) = -P(k)/k^4,
    P(k) = k^3-Dk^2-(9g/2)k+6g.

For k>=4,

    P'(k)=k(3k-2D)-9g/2>0,

because 2D<12 and g<0. Moreover

    P(4)=-8-92g/9>0,
    J(4)=9/8-2log 2-31g/576<0.

Hence P>0, J'<0, J<0, and H'<0 on [4,infinity). Together with (5), this proves H(k)<=H(3) for every integer k>=2, and (4) proves (3).

All sign checks in this proof are strict with ample rational margin. One may use

    69314/100000 < log 2 < 69315/100000,
    109861/100000 < log 3 < 109862/100000

and substitute g=(81/49)(2log 3-log 2-7/2). These log bounds follow directly from

    log z = 2 sum_{j=0}^{M-1} t^(2j+1)/(2j+1) + R_M,
    t=(z-1)/(z+1),
    0<R_M<2 t^(2M+1)/((2M+1)(1-t^2)),

with M=20 and z=2,3. This formula and its remainder follow by integrating the finite geometric expansion of 2/(1-t^2) from zero to t. The rational audit script checks (5), the other signs, eta>0 and c+d>0 using interval arithmetic, not floats.

## Lemma 3: a universal determinant estimate when degrees are at least two

Let A be a nonsingular n×n 0–1 matrix, with row degrees r_i>=2, column degrees s_j>=2, and m ones. Then

    log |det A| <= c n + d m.                              (6)

Proof. Set R=diag(r_i), S=diag(s_j), and

    B = R^(-1/2) A S^(-1/2),   K = B B^T.

Weighted Cauchy–Schwarz shows that B is a contraction: for every real vector z,

    ||Bz||^2
      = sum_i (1/r_i)(sum_{j:a_ij=1} z_j/sqrt(s_j))^2
      <= sum_i sum_{j:a_ij=1} z_j^2/s_j
      = ||z||^2.

The identical argument with rows and columns exchanged shows that B^T is also a contraction. Thus z^T K z=||B^T z||^2<=||z||^2, and all eigenvalues of the positive-definite matrix K lie in (0,1]. Applying (2) to them, and using the spectral theorem, gives

    log det K <= a n + b tr K + g tr(K^2).                 (7)

Also

    2 log |det A| = sum_i log r_i + sum_j log s_j
                    + log det K,
    tr K = sum_{(i,j):a_ij=1} 1/(r_i s_j).                 (8)

Write

    D_i = (1/r_i) sum_{j:a_ij=1} 1/s_j,
    E_j = (1/s_j) sum_{i:a_ij=1} 1/r_i.

Expanding the square of each entry of K and dropping the nonnegative cross terms for distinct common columns gives

    tr(K^2) >= sum_i D_i^2 + sum_j E_j^2
                - sum_{(i,j):a_ij=1} 1/(r_i^2 s_j^2).      (9)

In detail, the diagonal contribution is sum_i D_i^2. For i!=k the term K_ik^2 is at least sum_{j:a_ij=a_kj=1} 1/(r_i r_k s_j^2). Summing those terms is sum_j E_j^2 minus the last edge sum, proving (9).

For every i apply D_i^2 >= 2u_{r_i} D_i-u_{r_i}^2, and similarly for E_j. Rewriting the resulting vertex sums as edge sums yields

    tr(K^2) >= sum_{(i,j):a_ij=1} Q(r_i,s_j).               (10)

Because g<0, substituting (10) into (7) reverses the direction for that term exactly as required for an upper bound. Combining (7)–(8) and converting the row/column logarithms to edge sums, we obtain

    2 log |det A|
      <= a n + sum_{(i,j):a_ij=1} F(r_i,s_j)
      <= a n + eta m + lambda sum_{(i,j):a_ij=1}(1/r_i+1/s_j)
       = (a+2lambda)n+eta m.

The last equality uses that the two reciprocal-degree sums are each n. This is (6).

## Theorem: remove low degrees and conclude the full conjecture

We prove for every square 0–1 matrix A with n rows and m ones the stronger uniform bound

    |det A| <= exp(c n+d m).                               (11)

Induct on n. For n=0 both sides are one. A singular matrix satisfies the assertion since the right side is positive. Suppose A is nonsingular. All row and column degrees are positive.

If a row has degree one, expand along that row. If its nonzero entry lies in a column of degree t>=1, the remaining square 0–1 matrix A' has n-1 rows and m-t ones, and |det A|=|det A'|. By induction,

    |det A| <= exp(c(n-1)+d(m-t)) <= exp(cn+dm),

because c+dt >= c+d>0 and d>0. The case of a degree-one column is identical by transposition. If no such row or column exists, every degree is at least two, and (11) follows from Lemma 3.

Finally m<=3n, d>0 and (1) imply

    |det A| <= exp(cn+dm) <= exp((c+3d)n)
             = exp((n/7)log24) = 24^(n/7).

This proves the printed conjecture throughout its full range. In particular it includes matrices with unequal row or column sums. Blocks of Fano incidence matrices attain the bound whenever 7 divides n.

## Nonvacuity and equality examples

For each n the identity matrix has exactly n nonzero entries, so the
hypotheses are satisfiable. At n=0 the determinant is the empty product 1,
and the bound is 24^0=1. The literal Fano matrix used in the Lean source is

```text
1 1 0 1 0 0 0
0 1 1 0 1 0 0
0 0 1 1 0 1 0
0 0 0 1 1 0 1
1 0 0 0 1 1 0
0 1 0 0 0 1 1
1 0 1 0 0 0 1
```

It has 21 nonzero entries and determinant +24. Each row has three ones and
any two different rows meet in exactly one column, giving AAᵀ=2I+J and
|det A|²=9·2⁶=576. Direct determinant evaluation fixes the displayed ordering’s
positive sign. Thus |det A|⁷=24⁷, and det A=24^(7/7); the asserted constant is
sharp. The corresponding Lean lemmas are `identity_satisfies`, `order_zero`,
and `fano_attains`.

## Formalization status

`SparseDet.mathdb_348549` is the literal real-power conclusion on integer
matrices, with exactly the alphabet and nonzero-entry-count hypotheses above.
`SparseDet.mathdb_348549_integer` proves `|A.det|^7 ≤ (24:ℤ)^n` with those
same hypotheses; the real-power endpoint is derived from this integer
companion. No extra analytic hypothesis remains. `SparseDet.universal_potential`
proves (11) for every square zero-one integer matrix, without a sparsity
restriction. The three separate kernel lemmas `identity_satisfies`,
`order_zero`, and `fano_attains` establish nonvacuity in every order, the empty
case, and sharpness at order seven. All these declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Significance and limits

The shortest published route identified in the supplied discovery and independent review is Araujo–Balogh–Wang's Theorem 3, which at total sparsity 3n gives 2^(2n/3), approximately 1.5874^n, above the Fano constant 24^(1/7), approximately 1.5746. The distinctive step in this argument is the irregular-degree envelope: two-sided normalization, degree-dependent square-completion centers, the two-degree factorization, and a linear edge/vertex potential that survives leaf deletion. The regular-case quadratic spectral majorant is reused. No additional discovery credit is sought for helpers or the Fano example. The kernel certificate establishes the mathematical assertion; it does not establish a literature priority claim. The supplied independent review found no mathematical gap, but publication novelty remains subject to its bounded searches and access limits.

## Bounded prior-art discussion (refreshed 2026-11-20)

The final reviewer independently checked the arXiv statement and version history,
Bruhn–Rautenbach's Fano discussion, Scheinerman's total-sparsity bound, and
Semonsen's fixed-row-sum results (arXiv:2002.02482). No full proof of the
unrestricted 3n assertion was located. The arXiv source has only v1.
Indexed journal introduction excerpts retain the Fano conjecture, but the
reviewer could not retrieve the complete journal text: the publisher returned
403 and the open NSF copy failed with transport errors. No refusal was bypassed.

Fresh Semantic Scholar and OpenAlex citation lists for both the source and
Bruhn–Rautenbach were read. Both lists identify five later papers citing the
source. The reviewer inspected the theorem statements of Du–Xue
(arXiv:2607.15549), the ABW-bound application in the LDPC paper
(arXiv:2610.15893), the causal-learning paper (arXiv:2406.05937), and the
indexed determinant-bound statement of Hu–Zuo
(doi:10.1016/j.laa.2026.08.017). These do not supply the unrestricted 3n
Fano bound. Sarma's 2026 paper concerns adjacency determinants of k-cyclic
graphs with a unique perfect matching; its full text was not inspected.

The final reviewer also searched the supplied Principia, mio-qwq, Omega and
openai/math clones, the Principia id list, GitHub code, and Omega issues and
pull requests, with no matching resolution located. This is a bounded
literature and registry search, with the access limits above; it establishes
no unconditional priority claim. Details and reproducible independent
arithmetic checks are in the final review lane's FINAL-REVIEW-348549.md.

## References

1. I. Araujo, J. Balogh, Y. Wang, *Maximum determinant and permanent of sparse 0-1 matrices*, arXiv:2011.01892v1 (2020), Conjecture 1; LAA 645 (2022), 194–228.
2. H. Bruhn, D. Rautenbach, arXiv:1711.09935 (2017), LAA (2018).
3. D. Scheinerman, arXiv:1902.09644 (2019), especially Sections 7 and 9.

## Mapping to the Lean proof

`SparseStatement` encodes literal integer matrices, the printed nonzero-entry
predicate, and the integer-to-real-power bridge. `SparseSanity` certifies the
explicit Fano equality matrix. The universal identity and empty-order checks
are in `SparseStatement`. `SparseDeletion` proves the complete leaf-removal
induction from the minimum-degree-two estimate; no total-sparsity hypothesis
enters that induction. `SparseConstants`, `SparseMonotonicity`, `SparseDegree`,
and `SparseMajorant` prove all scalar constants, the integer degree envelope,
and the logarithmic quadratic majorant. `SparseSpectral` proves the spectral
trace-square identity, the eigenvalue upper bound from a quadratic contraction,
and (7) for an arbitrary positive-definite contracting real matrix.
`SparseMoments` proves the general nonnegative Gram fourth-moment inequality
(9), and square completion. `SparseNormalization` defines the literal two-sided
normalization and proves its entry-square formula and Hermitian Gram symmetry.

`SparseEdges` supplies the exact vertex-to-edge conversions and sums the full
integer envelope. `SparseGramDet` proves invertibility of the normalization,
positive definiteness of K, and its determinant/logarithm identity (8).
`SparseContraction` proves weighted Cauchy–Schwarz for the literal normalized
transpose, and hence the quadratic contraction of K. `SparseTrace` proves
the trace identity and (10) using the degree-dependent square-completion
centers. `SparseAssembly` retains the stage 1 conditional reduction lemmas;
`SparseFinal` supplies their matrix input unconditionally, proves (11), and
instantiates both fixed endpoints. The entire source of every module is
printed byte-for-byte in LEAN-SOURCE-APPENDIX.md in import order.

The endpoint axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
Compilation, standalone kernel-checking and fresh appendix-replay receipts are
listed in REPORT.md. They depend on the supplied Lean 4.34.1 and pinned Mathlib
installation; the upstream olean provenance limit is stated there. The complete
certificate, rather than a finite sample of matrices or degrees, establishes
the theorem for all n.
