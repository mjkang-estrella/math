# Source and claim review: MathDB 336488

Review date: 2026-10-25 (America/Los_Angeles; retrieved files are timestamped in UTC).

## Exact target

MathDB record [336488](https://mathdb.com/p/336488), UUID `4c3903af-7f72-48b6-864c-83c19bfc34fd`, is titled *Diagonalizability conjecture for premagic matrices*. The retrieved API record reports status `open`, zero Lean formalizations, and no listed solutions. This is a report of the observed database state, not independent proof of research priority.

The primary source is Kardi Teknomo, *Premagic and Ideal Flow Matrices*, arXiv:1706.08856v2 (6 May 2018), Section 7, Conjecture 7.2, PDF page 5. The later journal version is *Data Science: Journal of Computing and Applied Informatics* **3**(1) (2019), 35–45, DOI [10.32734/jocai.v3.i1-621](https://doi.org/10.32734/jocai.v3.i1-621); its Section 7, page 44, retains the same conjecture:

> Premagic matrix is diagonalizable. The eigenvectors of a premagic matrix has full rank.

Definition 4.3 (arXiv PDF p.2; journal p.37) means that the row-sum vector equals the corresponding column-sum vector. In coordinates, a square matrix is premagic precisely when, for every index i,

    sum_j M[i,j] = sum_j M[j,i].

Definition 4.5 expresses the same requirement as `(M − transpose M) 1 = 0`. Neither definition imposes stochasticity, symmetry, nonsingularity, or zero diagonal. Conjecture 7.2 has no nonnegativity restriction either. The neighboring Conjectures 7.1 and 7.3 explicitly say nonnegative; that qualification is absent from 7.2. Nevertheless our proposed counterexample is strictly positive, nonsingular, and has all row and column sums equal, so none of positivity, irreducibility, primitivity, or normalization to a doubly stochastic matrix rescues the claim.

No upstream theorem is needed for the proposed counterexample; source dependencies establish the historical claim and terminology only. The finite-dimensional linear algebra proof is independent.

## Explicit counterexample and stronger variants

Let J denote the 3 by 3 all-ones matrix, u=(1,-1,0)^T, and v=(1,1,-2)^T. The proposed main witness is

    A = I + 3J + u v^T = [[5,4,1],[2,3,5],[3,3,4]].

Every entry is a positive integer. Every row and every column sums to 10. The vectors satisfy sum(u)=sum(v)=u^T v=0 and v^T v=6. Hence

    A u = u,
    (A-I) v = 6u != 0,
    (A-I)^2 v = 0.

The last two statements prohibit diagonalizability over R or C: in an eigenbasis, the kernel of the square of A-I equals the kernel of A-I. Also A 1=10 1, and the basis (1,u,v) gives a 1 by 1 block [10] and a length-two Jordan block at 1. In particular det(A)=10 and its eigenvectors span only a two-dimensional subspace. Dividing A by 10 gives a strictly positive, invertible, doubly stochastic counterexample.

A simpler singular witness is A-I = [[4,4,1],[2,2,5],[3,3,3]], whose eigenvalues are 9,0,0. Dividing this by 9 yields a positive stochastic matrix P with P^2=J/3: exact mixing after two steps is compatible with a nonzero nilpotent part at eigenvalue zero.

The least possible dimension over R is three: dimensions one and two are diagonalizable, since a 2 by 2 premagic matrix necessarily has equal off-diagonal entries and is real symmetric. This minimality assertion should only appear as formally verified if the Lean artifact proves it; it is not needed for the main disproof.

For every n>=3 the same construction with zero-padded u,v produces A_n=I_n+3J_n+uv^T. It is strictly positive and premagic, has row and column sum 1+3n, and retains (A_n-I)v=6u and (A_n-I)^2v=0. This family is an optional written extension; distinguish its written proof from the exact scope of the Lean artifact.

## Prior-art and companion check

Live web searches were run for the exact phrases `"premagic" "diagonalizable"`, `"premagic" "counterexample"`, `"Premagic and Ideal Flow Matrices" conjecture 7.2`, `"premagic" "Jordan"`, `"premagic" "diagonalizability"`, and `"premagic" "7.2" counterexample`. Results found the arXiv and journal originals and their mirrors; no resolution of Conjecture 7.2 was located. Searches are discovery evidence, not a worldwide-priority certificate.

A later related source exists: Teknomo, [*Premagic Patterns and Network Topology*](https://doi.org/10.1007/978-981-95-4727-2_12), in *Ideal Flow Network for Transportation Research* (2026), pp.339–347, first online 6 February 2026. Its accessible publisher abstract concerns premagic matrices, and its bibliography cites the 2017 paper. The chapter body is subscription-only and was not read; its landing page has been preserved. Therefore this review cannot exclude an unindexed or paywalled prior observation. Do not state that the counterexample is the first in the literature.

A targeted scan of the existing project finding records, current campaign index and 2026-10-14 campaign Markdown found no prior result for `premagic` or `336488`. This supports treating it as new to this project.

## Reproduction and provenance

The sibling `sources/source-manifest.json` records retrieval URLs, UTC timestamps, SHA-256 hashes, and byte sizes for six retrieved primary/database files. The two PDFs have extracted text companions for easy source verification. All calculations above are exact symbolic identities; no approximate eigenvalue computation or simulation is used as proof.

Recommended publication language: an explicit, Lean-checked counterexample to the conjecture as stated in the cited source, independently obtained in this project, without a worldwide novelty claim. Do not equate the presence of a database entry with an assurance that the problem remained unresolved in all literature.
