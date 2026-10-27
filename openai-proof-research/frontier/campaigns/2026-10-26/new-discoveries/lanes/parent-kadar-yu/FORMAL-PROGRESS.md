# Formal progress — no discovery credit

A fresh isolated strict replay passes **116 declarations in 13 modules** with
pinned Lean 4.34.1/mathlib and hash-checked dependencies. Every declaration type
and axiom report was read; only propext, Classical.choice and Quot.sound occur.
The latest audit/report are verification/partial116-*. Historical partial14,
partial40, partial44, partial54 and partial103 receipts remain separately named.
The accepted campaign tally is controlled by ledger.json, currently 16/30.
This lane has credit 0.

## Supporting formal work completed

- JacobiSimple: Hermitian upper-band-one matrices with nonzero superdiagonal
  have simple eigenvalues and squarefree characteristic polynomials, including
  dimension zero. First-coordinate uniqueness and orthogonality are proved.
- PathBorder and JacobiDeterminants: literal border determinant and characteristic
  polynomial recurrences, nonzero-coupling consecutive coprimality, squarefreeness.
  The border proof adapts the Apache2 mathlib Cartan determinant argument, credited
  in the file and LICENSE-APACHE. The source's MINUS recurrence is used.
- ReducedIdentification: common monic factor uniqueness and full reduced-series
  cancellation under explicit determinant-decomposition premises. Multiplicities
  are retained; F and P_N are NOT assumed coprime. The boundary transfer is proved.
- UnitPath and PathGrid: literal path characteristic polynomials are rescaled
  Chebyshev S_n, with exact cosine-grid roots in (-2,2). A single sufficiently
  fine grid supplies arbitrarily many DISTINCT roots in any interior interval.
- SpectralCount, SumCompression and LowerSpectralCount: direct positive-eigenspace
  dimension proofs for both sides of every threshold. A block matrix has counts
  between the tail count and that count plus the head dimension. Empty spectral
  sets and repeated eigenvalues are covered.
- PrincipalCompression: explicit linear isometric extension for ANY injective
  index map, exact quadratic-form identity, principal-submatrix count comparison,
  and invariance under an actual equivalence of indices. No reindexing premise
  remains in the later Jacobi applications.
- TailStabilization and RootCounts: the literal free-tail submatrix identity;
  monotonicity and bounds by the fixed head size; eventual constancy of the ACTUAL
  polynomial root multiset count outside [-2,2], including multiplicities.
- DensityTransfer: enough distinct tail roots in an interval force a full-matrix
  root there by the two count bounds. Metric closure and closure(Ioo)=Icc prove
  density at both endpoints as well. jacobi_root_distribution packages all-degree
  squarefreeness, eventual exterior counts, and closed-band density for every
  Jacobi head with nonzero couplings and an eventual zero-diagonal/unit-off-diagonal
  tail. Its natural hypotheses are explicit and completely discharged internally.

These are CLASSICAL supporting facts, not new discoveries or a complete literal
source proof. They do not justify increasing the accepted tally.

## Outstanding load-bearing obligations

Construct the literal one-tail mixed Gram family for arbitrary source Specht
partitions; prove its principal/path structure and fixed monic factorization;
identify the actual source reduced polynomials and boundary k=-1. An explicit
cyclic Jacobi compression remains one route. COUNTING-ALTERNATIVE.md records a
potential shorter proof via principal-submatrix eigenvalue multiplicities and
fixed-factor cancellation. That alternative is not formalized or independently
reviewed yet. Generic head-family hypotheses alone are NOT the source endpoint.

The independent preliminary review of the full hand proof is complete, with
SOURCE/MATH PASS and bounded conditional NOVELTY/ELIGIBILITY support. Its three
requested explanatory repairs were integrated; see REVIEW-INTEGRATION.md.
No full source endpoint, manuscript, final review or packet acceptance yet.
