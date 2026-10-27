# Formal progress — no discovery credit

A fresh isolated strict replay passes **190 declarations in 22 modules** with
pinned Lean 4.34.1/mathlib and hash-checked dependencies. Every declaration type
and axiom report was read; only propext, Classical.choice and Quot.sound occur.
The latest audit/report are verification/partial190-*. Historical partial14,
partial40, partial44, partial54, partial103, partial116 and partial174 receipts remain separately named.
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

## Arbitrary-head Gram/gcd implementation

The new route does NOT require the finite head to be cyclic or tridiagonal:
HeadTail implements every entry of an arbitrary symmetric head plus one path;
PrincipalMultiplicity proves codimension-one multiplicity differences and
squarefreeness after removal of a common factor. HeadTailSpectral/Density prove
exterior stabilization and closed-band density without a Jacobi-head hypothesis.
ReducedHeadTail/Density transfer the conclusions through fixed factors.
GcdHeadTail defines the ACTUAL normalized gcd of the first two determinants and
PROVES its nonzero monicity, divisibility of all determinants, monicity and
consecutive coprimality of all quotients, and the complete root-distribution
endpoint with no residual decomposition premises. GramModel constructs the
literal alpha*I+G polynomial matrix and proves the characteristic-matrix/sign
identification, real splitting and boundary splitting. ComplexGram defines the
ACTUAL complex gcd quotient, proves normalized-gcd/scalar-extension agreement,
transfers every root with multiplicity, proves all complex roots real, and proves
the full complex squarefreeness/exterior-count/closed-density endpoint.
The generic monic factor-identification theorem also works over C.

## Outstanding source interpretation and acceptance

The closed endpoints quantify over EVERY finite real symmetric head, not over a
Lean Specht-partition type. SOURCE-BRIDGE.md explains the proposed exact
instantiation using source equations(3.2.3)/(3.2.4)/(3.2.17), construction(3.2.12),
and Proposition3.25. The complex field issue is formally bridged; no real-
coefficient assumption on the source factorization is hidden in the complex
identification theorem. GRAM-PROOF.md gives the full new multiplicity argument.

Independent review must assess the new mathematics and the exact source scope,
including whether the universal head model and already-proved source structure
adequately certify all source partitions, or identify a precise missing Lean
instantiation/reindex. The new route has NOT inherited the earlier preliminary
review's verdict automatically. All generic spectral/gcd results are classical
and earn no separate credit. Only a fully eligible literal source resolution
could count as ONE outcome, after renewed prior art, manuscript/final review,
packet and fresh extraction replay. Those gates remain pending.
