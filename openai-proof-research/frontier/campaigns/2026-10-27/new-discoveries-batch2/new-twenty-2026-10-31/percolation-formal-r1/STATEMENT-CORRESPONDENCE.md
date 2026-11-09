# Primary-source correspondence

Source: Gerbner, Keszegh, Mészáros, Patkós, Vizer, *Line Percolation in Finite Projective Planes*, cached arXiv:1608.00531v1 text. The cached text identifies v1 but has a November 7, 2018 body date. No published-version or prior-art claim was checked in this offline implementation lane. `evidence/source-333709.txt` is the exact text read; hashes accompany the evidence.

Line numbers refer to that text, not PDF line labels.

| Source | Formal object | Correspondence |
|---|---|---|
| Lines 64–71, PDF page 2 | `Plane.inc`, `countOn`, `step` | Incidence structure and at least r infected points. Every line is tested against the previous state. |
| Lines 69–73 | `rounds` | Round zero is the initial set; a successor is one synchronous step. |
| Lines 73–76 | `Percolates`, `percolates_iff_full_stable` | A full round is a stable closure and a full closure is a full round. No bounded-round surrogate is used. |
| Lines 75–77 | `TimeIs`, `time`, `time_is_least`, `time_unique` | Percolation time is the least natural round attaining the entire point set. |
| Lines 77–78 | `Minimal` | None of the proper subsets percolates. Not minimum size; not minimal among sets with a specified time. |
| Lines 158–161, PDF page 4 | `Plane` | q²+q+1 points and lines; degree q+1; unique joins and intersections. Also includes q ≥ 2 and explicit quadrangle nondegeneracy. |
| Lines 100–102 | `PG5`, `incidence_dot` | The canonical normalized-vector dot-product incidence presentation over arithmetic modulo 5. |
| Lines 674–675, PDF page 14 | `Conjecture20` | For every q and every finite plane of order q, for every r with 4 ≤ r ≤ q, a minimal percolating set has time exactly two. |
| Negation of lines 674–675 | `not_conjecture20` | CONDITIONAL on precisely `NoMinimalTwoRound5`. This is not yet the unconditional negation. |

Arbitrary finite point and line types can be labeled by `Fin (q*q+q+1)` using their cardinalities. The self-contained structure quantifies over every labeled incidence presentation, so it includes both Desarguesian and non-Desarguesian planes. No coordinatizability assumption occurs in `Conjecture20`. Transport from an alternative external geometry library is not implemented or needed by the displayed conditional theorem; only the counterinstance uses coordinates.

The positive controls use exactly these same definitions and the same PG5. The threshold-4 control has time 2; the threshold-5 control has time 3. The three-round control certifies the concrete numeric witness supplied as evidence, without claiming it is the literal Proposition 18 construction.
