# Independent mathematical review

Reviewer role: separate mathematical construction and adversarial check.
Date: 2026-10-25. This review does not assert human peer review or priority.

## Exact problem match

The local MathDB response `sources/mathdb-336488.json` identifies entry 336488,
with no posted solutions or Lean formalizations in the retrieved response.
The target is Teknomo's Conjecture 7.2. In the original paper, Definition 4.3
defines premagic by equality of the corresponding row and column sums;
it does not require symmetry, zero diagonal, or nonsingularity.
Conjecture 7.2 in the arXiv v2 and published 2019 article asserts
diagonalizability and full rank of the eigenvectors.

The proposed matrix

```
M = [4 4 1
     2 2 5
     3 3 3]
```

has positive integer entries, so it also defeats a restriction to positive,
irreducible, nonnegative real matrices. Every row and every column sums to 9.

## Independent proof

Set `u=(1,-1,0)`, `v=(1,1,-2)`, and let `J` denote the all-ones matrix.
Then `M=3J+uv^T`. Both `u` and `v` have coordinate sum zero and `v^Tu=0`.
Thus `Mu=0`, whereas `Mv=6u` is nonzero. Equivalently, for the smaller
integer witness `x=(1,0,-1)`, `Mx=(3,-3,0)` is nonzero and `M²x=0`.

For any diagonalizable linear map over a field, `ker(M²)=ker(M)`: after
conjugating to a diagonal matrix, each coordinate satisfies
`d_i² z_i=0`, hence `d_i z_i=0` because a field has no nonzero nilpotents.
The displayed witness contradicts this equality. This proof applies over
both R and C, and indeed over every characteristic-zero field. It needs
no numerical eigensolver and no theorem from the research corpus.

The characteristic polynomial is `lambda²(lambda-9)`. The eigenspace at
zero is one-dimensional while zero has algebraic multiplicity two; the
eigenspace at 9 is spanned by `(1,1,1)`. Thus all eigenvectors together span
only a two-dimensional space. This addresses both sentences of the conjecture.

## Robustness and optional extensions

The singularity of the primary example is not essential. `A=M+I` is positive,
premagic, invertible, has determinant 10 and characteristic polynomial
`(lambda-10)(lambda-1)²`; the same witness applies to `A-I`.
More generally, with `u,v` extended by zero coordinates,
`A=I+cJ_n+uv^T` works in every dimension `n>=3` for each integer `c>=3`.
Its determinant is `1+nc`. These are optional mathematical extensions,
not a claim that the main Lean file certifies them unless explicitly added.

Dimension three is minimal among **real** premagic counterexamples: in
dimension two equality of the corresponding sums forces the off-diagonal
entries to be equal, and a real symmetric matrix is diagonalizable. Do not
remove the word real. Over C a symmetric matrix may be defective: the
nonzero premagic matrix `[[i,1],[1,-i]]` squares to zero.

## Diagonalizability definition audit

The formal definition `exists P Q d, P*Q=I and Q*P=I and
M=P*(diagonal d)*Q` is exactly similarity to a diagonal matrix. The
two inverse equations imply `Q=P^{-1}`. Multiplying on the right by P
gives `MP=P*diagonal d`, so the columns of P form a basis of eigenvectors.
Conversely an eigenvector basis gives such a P and its inverse Q. Therefore
this explicit definition neither weakens the conjecture nor assumes the
desired obstruction. The kernel-square lemma is the essential bridge.

## Independent computations and search limits

`verification/independent_check.py` uses only Python's exact fractions and
integer operations. It checks positivity, corresponding row and column
sums, both Jordan-chain equations, ranks of M and M², and the characteristic
polynomial at four points (sufficient for equality of two degree-three
polynomials). It also checks 30 nonsingular higher-dimensional family cases.
These finite checks are diagnostics, not the universal proof.

Searches for the combinations premagic/diagonalizable,
premagic/diagonalizability/counterexample, premagic/Jordan and
premagic/nondiagonalizable returned the original paper and its copies,
with no located earlier counterexample. This bounded search is not evidence
of worldwide priority. Defective positive stochastic matrices are standard
linear-algebra constructions; the project contribution is the explicit,
checked disproof of this named conjecture and its Lean certification.

Primary sources examined:

- https://arxiv.org/html/1706.08856v2, Definitions 4.1–4.5,
  Theorem 5.12 and Section 7 / Conjecture 7.2.
- https://talenta.usu.ac.id/JoCAI/article/download/621/394/2194,
  published Conjecture 7.2, p. 44.
- https://talenta.usu.ac.id/index.php/JoCAI/article/view/621,
  journal citation metadata (2019, volume 3 issue 1, pp. 35–45).

Mathematical verdict: PASS for the proposed concrete counterexample, over
both R and C. Compiler acceptance and final artifact byte integrity require
their separate build records.
