# W005 C disposition — exact algorithm, failed speed target

Date: 2026-10-08. Verified new complete factoring improvement: **NONE**.

The parent read the complete [independent report](W005-strip-validation.md)
and checked its exact enclosure, signed floor-sum recurrence, search invariant,
widths, node obstruction, resonant family and line-recovery computation.
Accept these scoped deductions. No numerical experiment or Lean proof is implied.

The literal tangent/secant, empty-wedge, left-first algorithm is sound and
complete, with conservative O(sqrt(N)*log^3 N) bit time and O(log^2 N) space.
Every discarded interval has O(N^(1/4)) integer abscissae. Before finding
the least prime p, the program must cover all p-2 preceding candidates;
balanced distinct semiprimes therefore force Omega(N^(1/4)) visited nodes.
This excludes the desired one-fifth improvement for this program even if its
floor sums cost nothing. It does not constrain all geometric factoring.

The small-area heuristic is not a deterministic lattice-count estimate.
The exact N=H^8+1, [H^4-H,H^4] family has vanishing wedge area yet
unbounded spurious lattice count. The fixed-line sliding identity is useful
only when the actual rational lines are unchanged; new secants/tangents do
not inherit it.

Retain the concrete replacement: enumerate levels c=u*x+v*y and test
c^2-4uvN for a square, with integrality and interval checks. One such level
rejects the displayed resonant family. This is known weighted-sum/Lehman
territory, not a novel factorer. Its total slope selection, interval coverage,
level enumeration and extraction costs remain the research question.

No finite screen is selected: the exact node lower bound already decides the
literal speed claim. Original brief, report, source scope and input identities
remain unchanged. Parent brainstorming continues on the orthogonal-pair
generation problem while the point and quaternion reviews run.
