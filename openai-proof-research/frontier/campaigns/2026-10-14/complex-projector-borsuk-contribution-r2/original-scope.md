# Frozen target B8C: the Borsuk number of the complex projector plane

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

Frozen after source/primary screening and before writing any proof text,
diagnostic, or candidate. Later files may report a proof, a refutation, or
an exact unpaid operation for THIS statement; they may not narrow, widen
or re-quantify it.

## Exact statement

Let Herm_3 be the real vector space of complex 3x3 matrices A with A*=A,
with the Frobenius norm ||A||_F^2 = tr(A*A) = tr(A^2). Its trace-one
affine hyperplane T = {A in Herm_3 : tr A = 1} is a real Euclidean space
of dimension 8. Put

    X = { u u* : u in C^3, ||u|| = 1 }  (a compact subset of T),

the set of rank-one orthogonal projectors of C^3. For a bounded set Y of
positive diameter, b(Y) is the least number of subsets of Y, each of
diameter STRICTLY less than diam(Y), whose union is Y.

**B8C.** diam(X) = sqrt(2) and b(X) = 9. Explicitly, both of:

1. (upper) there EXIST nine subsets A_1,...,A_9 of X, with union X,
   each of Frobenius diameter strictly less than sqrt(2);
2. (lower) for EVERY family of at most eight subsets of X with union X,
   some member has diameter sqrt(2) (equivalently, not < sqrt(2)).

No regularity (closedness, measurability, connectedness, convexity) of
the covering subsets is assumed in part 2. Part 1 requires actual sets,
not a numerical near-cover or a cover up to measure zero.

A refutation must show b(X) >= 10 (then X would be a counterexample to
Borsuk's assertion in dimension 8) or b(X) <= 8. A cover by sets of
diameter <= sqrt(2), a cover with one non-strict member, a finite
subset of X, or a cover of a proper subset does not settle B8C.

## Source family and the operation chosen before sustained work

Source family 156 at openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb:
preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/.
Its thm:main proves b(X_4^R) > 10 for the REAL projector set of R^4 in
dimension 9; prop thm:label-bound proves m >= N_k labels for real
admissible maps; thm:equality-complex derives pure facet cycles at
equality; the six/ten-label combinatorics kill N_4 = 10 labels. The
source states that it does not determine the smallest failing dimension
and treats only real projective space. Truth of these statements is
stipulated, not audited.

The natural lower-dimensional candidate of the same mechanism is the
complex projective plane: its projector image lies in dimension 8, one
below the source. B8C asks whether it is a counterexample. Screening
facts (to be proved, not assumed, in later files):

- A Hermitian analogue of the source's odd extension should give the
  lower bound 9; the source's real lemmas are not applied verbatim.
- The source's ten-label combinatorial endgame has no analogue that
  obviously kills nine labels: the expected facet structure (pure
  4-dimensional, all edges) is consistent with known 9-vertex
  triangulations of CP^2. This is motivation only, not a proof input.
- The obvious upper construction, closed Voronoi cells of the Hesse SIC,
  FAILS: each closed cell contains orthogonal pairs (at the twelve
  mutually-unbiased-basis "holes"), so has diameter exactly sqrt(2).

Concrete nonroutine operation identified before sustained work: resolve
the twelve holes, where six cells meet and every cell contains an
orthogonal pair of holes, by a perturbation that removes EVERY orthogonal
pair from EVERY cell while still covering, OR prove that no nine-set
cover exists (giving Borsuk failure in dimension 8). Moving the nine
SIC points themselves is suspected not to suffice at first order, since
a point cannot approach both members of an orthogonal hole pair; the
operation must be a non-geometric, hole-dependent weighting or a
genuinely different cover, or else a topological obstruction.

This is a research target, not a theorem claim or an assertion of
worldwide novelty. No independent proof/contribution PASS, nomination,
count increase, manuscript or Lean package is claimed by this freeze.
