# Graph/matrix source screen

Research date: 2026-10-26. No discovery credit.

## Exclude MathDB 367192

The live record says open, but its cited source itself solves the precise conjecture. Csikvári–Harangi, *The least balanced graphs and trees*, latest arXiv:2502.13939v3 (March 25, 2026), Conjecture 1.2 and Theorem 1.3, printed p.2, explicitly identify K4 with a pendant path as the minimizer for every n>=6. Theorem 1.4 also resolves the analogous tree claim. Actual full PDF retrieved and definitions/target/theorems read. Do not count a new proof, endpoint, or formalization of this known result. Source URL https://arxiv.org/pdf/2502.13939 ; SHA-256 81d850f6c32723438a3d54a6a021fd6442883c7c1138e8603b6cc8b3c974fba5.

## MathDB 373707, no counterexample

Bogdanov–Petrov–Sadovnichiy–Ushakov, arXiv:2603.18253v1, Conjecture 5. The actual source HTML was read, including the repeated-row/column generality and the special case proved in Theorem 5/Section 3.5. Literal zero entries must be distinct as cells, but their row and column indices may repeat. The target is sum_(i,j) M_(x_i,y_j) M_(x_j,y_i) <= (t-1)||M||infinity||M||1 for odd t. The four existing proofs in Section 3.5 apply to the source's special case with distinct row and column indices and are not a full solution.

screen_zero_entries.py tests actual integer matrices with row/column repetitions allowed in the selected cells. It greedily searches odd subsets of the zero cells; every reported objective is an exact integer. The deterministic search found no violation in 31128 subset tests, with best ratio exactly 1. This is finite heuristic evidence only. It neither exhausts matrices/subsets nor establishes universal validity. The full live MathDB JSON has no posted solution or progress.

Other records were retrieved for triage only: 361424's interval is an interval of eigenvalue **values**, despite the MathDB prose's erroneous index wording; 359959 has an asymptotic sufficiently-large-n quantifier. No loophole, theorem, or counterexample is claimed for either. The initial permutation-trinomial record 365581 cites a paper whose title announces a proof; its full latest theorem scope still needs inspection before a definitive exclusion.

MathDB 345259 is now being investigated in the separate parent-partitions lane. Its exact strict-valley candidate is unaccepted pending full formal source/count bridge and other gates. The univariate Dousse–Kim conjecture is not refuted.
