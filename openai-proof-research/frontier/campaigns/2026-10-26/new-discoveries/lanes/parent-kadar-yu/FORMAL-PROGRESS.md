# Formal progress — no discovery credit

The accepted campaign tally is recorded in the ledger. A fresh isolated strict
replay passes 54 declarations in 6 modules with pinned Lean4.34.1/mathlib and hash-checked dependencies. Every
declaration type and axiom report was read; only propext, Classical.choice and
Quot.sound occur. The audit/report are verification/partial54-*. Historical
partial14/40/44 receipts remain separately named.

## Supporting formal work completed

- JacobiSimple: real Hermitian upper-band-one matrices with nonzero superdiagonal
  have simple eigenvalues and squarefree characteristic polynomials, including
  dimension zero. First-coordinate uniqueness and orthogonality are proved.
- PathBorder: appending one scalar node at the final coordinate has determinant
  d detM - c² detM_prefix, over any commutative ring. The corresponding genuine
  characteristic-polynomial recurrence is proved; unit coupling yields the
  source's correct MINUS recurrence. This adapts the Apache2 mathlib Cartan
  determinant argument, credited in the file and LICENSE-APACHE.
- JacobiDeterminants: explicit Jacobi matrices satisfy the border recurrence;
  their consecutive characteristic polynomials are coprime by a proved Bezout
  propagation argument. Simplicity is retained for all nonzero couplings.
- ReducedIdentification: the common monic factor in two polynomial families is
  unique when both consecutive reduced pairs are coprime. Cancellation recovers
  the complete reduced series and the k=-1 boundary. Multiplicities are retained;
  F and P_N are NOT assumed coprime. The matching determinant decompositions
  remain explicit premises, to be proved from the source structure later.
- UnitPath: the literal zero-diagonal unit-coupling path matrix has characteristic
  polynomial equal to mathlib's rescaled Chebyshev S_n. Its roots have the exact
  cosine-grid formula, and every eigenvalue lies strictly in(-2,2).

- SpectralCount: a direct positive-eigenspace dimension argument bounds the
  number of eigenvalues above any threshold by the dimension of a projection
  target whose kernel has a quadratic-form bound. It also proves spectral-count
  monotonicity under a linear isometry with quadratic-form domination. Repeated
  eigenvalues and empty positive spectral sets are included. These are proved
  classical variational facts; the source head-tail application is still pending.

These are CLASSICAL supporting facts, not new discoveries or a complete source
proof. They do not justify increasing the accepted tally.

## Outstanding load-bearing obligations

Construct the cyclic Jacobi compression from an arbitrary real symmetric head
with its distinguished attaching coordinate; prove the source mixed-tail Gram
structural facts for arbitrary Specht partitions, including the fixed monic
factorization; derive the literal source identification. Prove principal-submatrix
interlacing/count bounds, eventual exterior-count stabilization, and interior
root density including both endpoints. The generic path/cancellation theorems
alone do not discharge these obligations.

The independent preliminary review of the full hand proof is complete, with
SOURCE/MATH PASS and bounded conditional NOVELTY/ELIGIBILITY support. Its three
requested explanatory repairs were integrated; see REVIEW-INTEGRATION.md.
No full source endpoint, manuscript, final review or packet acceptance yet.
