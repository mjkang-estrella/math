# Fresh source screening, 2026-10-26

No bounded scan is counted as a discovery. Work in this lane is restricted to uniquely owned files; shared campaign indexes are managed by the parent.

## Active substantive candidate

**All-odd randomized subtraction nonconvergence.** Exact source arXiv:2405.19593v1, Section3 opening paragraph and Question3.4; source reached through MathDB363319. The neighboring polynomial-root simplicity conjecture extracted as363319 remains open. The new candidate bypasses simplicity and proves that winning probabilities do not converge for every finite nonempty set of positive odd moves. See `SUBTRACTION-PROOF-CANDIDATE.md` and the frozen Lean modules `formal/GameRecurrence.lean`, `formal/GameZigzag.lean`, and `formal/GameDefinition.lean`. The parent is authoring the independent finite-window invariant and nonconvergence bridge. Independent mathematics/source/prior-art review is in the matrix agent lane. No novelty credit is assigned by this screening note.

## Excluded known-result connection

**364606 centered exponential-tail coefficient positivity.** Complete elementary mathematical argument was found and retained in `STIRLING-PROOF-CANDIDATE.md`. Independent review found that Skorski2023, Corollary3, already implies the full source conjecture through centered Beta(1,r) moments. The proposed optimal shift classification is an immediate consequence of the same stronger prior. Strict credit0. `formal/StirlingPositivity.lean` contains only a warning-free partial formal development (exact formal-series definitions, derivative identity, and first/below-leading coefficient lemmas); it is not a complete certificate for the coefficient-positivity theorem, and no such certificate is claimed.

## Negative exact screens

- **367768:** Mu–Welker coefficient comparison in the canonical binomial recursive decomposition, exact original arXiv:2503.24076v1 Section3.2 Conjecture3.8. A deterministic seeded scan of250,000 products of positive integer linear factors and integer quadratics with nonnegative discriminants, degree3–24, found no coefficient-comparison violation. These input products are rigorously real-rooted; the scan uses exact integer coefficients and binomial decomposition. It does not prove the conjecture. The adjacent real-rootedness-preservation question3.10 is already refuted in Liu–Wang–Zhang arXiv:2609.23694v3, whose Section1 explicitly distinguishes the remaining coefficient comparison; no new claim on that question is made. Script `screen_recursive.py`.
- **363319:** Exact polynomial gcd scan over every nonempty subset of positive even exponents below each odd leading degree3–37 (524,268 polynomials), plus100,000 deterministic seeded random sparse cases with odd degree39–999, found no repeated roots. Script `screen_subtraction.py`. This is evidence only and is not a root-simplicity proof.
- Exact rational checks of the new all-odd probability argument checked the prefix/suffix TOTAL identity for every four-element subset of odd3–27 and both zigzag inequalities through heap299. Individual suffix sums need not equal individual prefix sums: the argument uses a recurrence-derived equality only after summing over moves.

Other source snapshots fetched for possible triage:363608,364842,362667,362899 and small tags power-series, polynomial-inequalities, recurrence-sequences. No result on these is claimed.
