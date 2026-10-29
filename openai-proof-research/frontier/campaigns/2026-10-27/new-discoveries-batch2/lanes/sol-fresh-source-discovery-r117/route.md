# Excluded all-cut padding route, not a discovery

Pan–Skandera–Wang, EPTCS445 (2026),139–147, abstract and Section1, explicitly ask for every real totally nonnegative n by n matrix A, n>=2, and every 1<=h<n:

    per A[[1,h]] per A[[h+1,n]] >= per A[even] per A[odd].

All submatrices here are principal; empty permanents equal1. Totally nonnegative means every increasing square minor has nonnegative determinant. The experimental HTML's isolated prose “each of its minors is negative” contradicts its immediately following >=0 definition and the rest of the manuscript; it is not used as a source refutation. Likewise odd-size endpoint typos in (7.2) do not define a new question.

The balanced version for every even order implies the full displayed inequality by a routine identity padding argument. This is NOT a new contribution: the frozen public registry already contains exactly the full claim and this reduction. The following ordinary derivation only records why this lead must be excluded rather than re-nominated.

For 2h<=n set d=n-2h, N=n+d=2(n-h), B=I_d direct-sum A. Then N/2=d+h. Every square minor of B either vanishes (unequal selected row and column counts in its ordered diagonal blocks), or factors as the corresponding identity minor and A minor. Both are nonnegative. Thus B is TNN. The first balanced principal block is I_d direct-sum A[[1,h]], and the second is A[[h+1,n]]. The product of their permanents equals the original consecutive-block product. Each parity principal block of B splits into an identity block and a parity principal block of A. The original parity classes are either preserved or exchanged according to d modulo2; their product is unchanged. Apply the balanced inequality to B.

For 2h>=n instead put d=2h-n, N=2h and B=A direct-sum I_d. The balanced cut at h is the original cut; parity again is unchanged up to identity factors. TNN and permanent-factorization arguments are identical. This handles every n>=2 and every strict cut, including n2,h1. Simultaneous reversal followed by left-padding is an equivalent route, and is the route in the actual public endpoint body.

Strongest objections/falsifiers: arbitrary row/column permutation does NOT preserve TNN, so moving an arbitrary subset to the initial block is invalid; this proves nothing for arbitrary nonconsecutive cuts. Dropping TNN invalidates the inequality: A=[[1,0,1],[0,1,0],[1,0,1]],h1 has defect-1 and minor rows(1,2),columns(2,3) determinant-1 (one-based). Zero blocks in padding preserve TNN but not strict total positivity. A strict-positivity-only balanced premise would need an additional approximation proof; the pinned public theorem is explicitly TNN, so no such bridge is silently assumed.

The independent executable check uses literal permutation expansion and subset-DP permanents, and 224 deterministic exact-integer padding comparisons on products of elementary nonnegative bidiagonal matrices for n2..8 and every cut. It also checks the non-TNN negative control. These computations validate indexing and diagnostics; they are not an all-order proof or discovery credit.

Pinned prior:
https://raw.githubusercontent.com/the-omega-institute/trureturing/1b999d9fda71df7537b62327147496d64a6f66ef/D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.lean

Actual `PSW.claim` and `PSW.result` have precisely the all-n, all-real-matrix, all-cut scope above, with the TNN premise. `lower_half` invokes balanced plus `tnn_padLeft`, `parity_padLeft`, and `split_padLeft`; the upper half uses reversal. The Blueprint matches that scope. It was already present in the frozen baseline retrieved18:13UTC, before this worker's21:51UTC source retrieval. No later counterpart is being mislabeled prior. No local Lean compile or transitive-axiom audit of this external development is claimed. The actual source-cited method is Theorem7.1 (Drake–Gerrish–Skandera monomial Bruhat comparison), used to obtain the balanced polynomial inequality from a source-map bijection; Algorithm7.5/Conjecture7.8 are already public in the corresponding Bruhat modules. This work neither re-proves that general theorem nor asserts a fresh endpoint from it.
