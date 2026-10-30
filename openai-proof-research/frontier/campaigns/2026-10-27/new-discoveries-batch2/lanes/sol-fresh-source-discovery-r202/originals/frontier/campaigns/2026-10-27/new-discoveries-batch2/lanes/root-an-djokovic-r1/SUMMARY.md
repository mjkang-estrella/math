# astra-discrete-r3 handoff

**One candidate mathematical resolution; zero accepted credit.**

Candidate: full An–Đoković Conjecture3.6 (MathDB381028), for every n≥2 and 1≤k<n:

⟨χ_(J_(k,n)), Δ_n⟩ = (−1)^(n−1) C(n,k) C(n−2,k−1).

The exact source, quantifiers, complete written proof, and a self-contained proof of the needed restricted divided-symmetrization lemma are in **discovery.md**. This is an all-n claim, not the already public n≤12 verification or Narayana observation.

## Core idea

Cancel the adjacent Vandermonde factors to obtain the degree n−1 numerator
P=∏_(j≤k)(x_n−x_j) ∏_(k<i<n)(x_i−x_1).
Its internal exponents are at most one, so the negative-prefix set of each monomial is a terminal interval. The classical monomial DS value is therefore the signed binomial weight w_r=(−1)^(n−r)C(n−1,r−1). For the cumulative coefficient mass C_j, specialize x_1,…,x_j=t and all later variables to1. The whole product vanishes unless j=k, when it is (1−t)^(n−1). Thus only first-deficit classes k and k+1 survive; an alternating-binomial-tail identity and Pascal give the exact result.

## Saved validation

- `checks/exact_check.py`, `checks/exact_check.json`: literal sparse source pairing, 15 cells n2..6; independent direct Fraction permutation sum, 28 cells n2..8; coefficient/deficit identities, 120 cells n2..16. All pass. Not proof substitutes.
- `formal/TwoLevel.lean`: seven definitions, nine proved initial lemmas. Literal source pair set/polynomial/Vandermonde/pairing definitions; universal two-level specialization, prefix monotonicity, signed tail, actual numerator evaluation, final signed binomial arithmetic.
- `formal/replay.log`, `formal/verification.json`: exact types/definitions, passing user-pinned Lean replay and only propext/Classical.choice/Quot.sound.
- `formal/README.md`: exact intended missing theorem and explicit missing bridges.
- `provenance.md`, `sources/*manifest.json`, primary PDFs/text: URLs, timestamps, SHA256, primary theorem-body comparison and access failures.
- `checks/self-review.md`: adversarial worker checks, explicitly not independent.

## Root gates still required

1. **First decide substantive eligibility / novelty.** Postnikov's monomial DS theorem and edge-splitting are classical. The additional two-level coefficient cancellation may be judged routine under this campaign's unusually strict rule. The worker does not claim that decision is settled. No all-n public resolution was found in a bounded search; that is not absolute priority evidence.
2. Independent exact-source mathematical review, including source normalization and the supplied self-contained lemma.
3. Full literal Lean endpoint: alternation-to-pairing, product/support bridge, restricted DS evaluation, and finite coefficient regrouping are not yet formalized. The nine lemmas do not certify the conjecture by themselves.
4. Final-source/publication comparison as desired, paper, independent formal review and final extracted replay.

No git, children, shared files, old accepted result, external message/post, or ledger edits. BBK positivity remains unresolved; its no-hit floating LP probe is retained without credit. Recommended next action: root review of this short complete written proof and the routine-corollary objection before investing in full formalization.
