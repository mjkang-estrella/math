# Next discovery lane: two complete candidates

This lane produced two distinct full MathDB outcomes, ready for independent parent review:

| ID | Full outcome | Lean result |
|---|---|---|
| 372794 | Every coefficient of the Fill–Janson polynomial is nonnegative for every natural exponent | `CoefficientPositivity.all_coefficients_nonnegative` |
| 350342 | Inputs 677 and 401 produce at least 38 distinct prime outputs, refuting both the MathDB bound 10 and original bound 13 | `OvaCount.prime_count_counterexample` |

Both are honest verifications of earlier posted results, not new-discovery claims. Each directory contains the full single-module Lean proof, source record with solution credits, detailed paper, scope/novelty notes, and pinned build receipts. Both main proofs pass Lean 4.34.1 and the canonical forbidden-token/axiom audit. Independent review is pending. No git, shared index, or accepted ledger was modified.

## Important source facts

- MathDB 372794 has a prior proof by Shivam Patel and an existing public Lean dossier by Machina Mathematica / Korea Superintelligence Labs. The local proof uses a compact triangular recurrence and fully proves the source-formula identity.
- MathDB 350342 states the bound 10. Its linked 2021 arXiv source refers to the construction in a 2020 publication whose Conjecture 1 actually states 13. Both are refuted. The local theorem certifies **at least 38**, not an exhaustive equality.

## Next action for parent

Review `coefficient-positivity/main.tex` with `formal/CoefficientPositivity.lean`, and `ova-count/main.tex` with `formal/OvaCount.lean`. The exact fetched MathDB records and source PDFs are under `sources/`; hash inventories are in each `primary-reference.json`. If accepted, integrate each as one outcome; supporting closure/recurrence/count lemmas are not separate outcomes.
