# Fair-discrepancy propagation for fully balanced matrices

Problem: [MathDB340783](https://mathdb.com/p/340783).

Refuted for every positive tolerance by a strictly positive matrix with equal row and column squared energies.

The complete formal statement is `FairDiscrepancy.every_reflexive_interpretation_counterexample` in `formal/Discrepancy.lean`. The paper is `main.tex`; a release includes `paper.pdf`.

This source is integrated from the independently produced matrix discovery lane. All mathematical claims and the source interpretation require the independent review before counting. The balanced-matrix construction is explicitly credited to Shivam Patel; no new-disproof priority is claimed.

From the campaign root, run `python3 verify_outcome.py outcomes/fair-discrepancy`. From a standalone archive, run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. The pinned dependencies are in `pins.json`.

Status: independent review, full Lean compilation and two-page paper QA passed.
