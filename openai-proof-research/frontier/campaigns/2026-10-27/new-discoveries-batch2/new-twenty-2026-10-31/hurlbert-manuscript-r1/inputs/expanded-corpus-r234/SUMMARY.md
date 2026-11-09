# Expanded corpus r234

**One Lean-certified candidate refutation: MathDB 356266. Zero accepted credit claimed.**

The candidate is a cyclic Euler ordering of all 24 permutations of four letters that cannot be realized as the window order of any cyclic word over a linearly ordered alphabet. Nine forced inequalities form a strict cycle. The literal Lean endpoint `MathDB356266.counterexample` includes permutation coverage, distinctness, cyclic overlap and nonrealizability. A fresh extracted strict build, all-local declaration/axiom audit and local `leanchecker` replay pass. See `CANDIDATE.md`, `replay-result.json` and `proof-packet-v2.zip`.

Exactly 20 ID-keyed entries, including exact statements, raw/chunk/statement SHA256 provenance and per-source receipts, are in `results.json`. All original raw lines retain their newline in `raw/`.

Six records are excluded as already resolved:

* 355511: source Theorem 2 proves its own Wang–Sun conjecture.
* 355710: source Theorem 3 proves the rooted-path walk determinant conjecture.
* 355828: the reserved source already refutes the Ramsey deletion conjecture.
* 355905: Annabel Ma's arXiv:2409.17123 proves the M-triangle formula.
* 356072: Binner's source proves the reserved Chern double-series claim.
* 356214: Nambi–Kumar arXiv:2406.05960 already refutes the unicyclic claim.

Thirteen are parked. Material source gaps: 355635 copies the definition of MP_nu in place of the source's M_nu; 356350's supplied source contains no symmetric-group conjecture or Example S3. Neither defect is counted as a new mathematical outcome. Famous/structural/analytic targets receive honest dispositions rather than dummy endpoints.

Exact diagnostic work besides the candidate:

* 355761: every labelled connected graph on 4 and 5 vertices (38 and 728), with a found valid two-colour, multiplicity-1-or-2 assignment in every case.
* 356308: all subsets for nine specified generalized dihedral groups through order 20, including two noncyclic rotation groups. MSTD outnumbers MDTS in each case; full counts retained.
* 356002: integer membership-atom Hall-violation searches for n=4, b<=6 and n=5, b<=3 over all relevant a and three thresholds around the predicted interval. Seven subproblems reached the 100000-node cap; they are **unknown**, not verified. No counterexample to the interval was found.

* 356405: 600 sampled simple connected cubic graphs across orders 14–30; 9/8/7-color strong-coloring attempts gave no obstruction. Seven capped subproblems remain unknown; seven girth-at-least-5 samples were 7-colorable. This is diagnostic sampling, not a beyond-literature-range result.

The candidate and its literature neighbourhood were sustained through proof construction, 1992/1996/2019/2022 primary-body checks, both versions of the two closest companions, printed-example comparison, current public-registry screening and strict formal replay. No exhaustive corpus-wide technical or literature clearance is asserted. The 1990 thesis body remains unread and must be checked independently. No descendants were launched; no git operations, external messages, publication, shared ledger edits or writes outside this lane were intentionally performed.

Network receipts are immutable and retained, including a TLS failure, a 404 guessed thesis URL and one unrelated arXiv identifier guessed during lookup (explicitly excluded from evidence). No 403/429/challenge retry or TLS bypass was used. Initial Lean thread creation failed; `-j1` solved it. The first extracted audit failed only on references to generated auxiliary names; the v2 audit explicitly disables that name linter and passes all strict proof checks. Prebuilt dependency caches remain trusted; no full upstream rebuild is claimed. The `leanchecker --help` discovery call unexpectedly began default project inspection and was interrupted; final checking used the explicit local module under the cap. Earlier wrapper RSS measurements around a Python subprocess underestimate the child; final replay directly execs Lean and reports about 1.9 GiB peak.

Review priority: independent fidelity and novelty/significance review of 356266. Other parked targets have explicit remaining gaps in `results.json`; no new result is asserted for them.
