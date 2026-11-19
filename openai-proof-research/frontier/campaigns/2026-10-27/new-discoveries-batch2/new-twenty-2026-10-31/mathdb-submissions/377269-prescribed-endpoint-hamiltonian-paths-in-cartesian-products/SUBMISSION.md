# MathDB 377269: Prescribed-endpoint Hamiltonian paths in Cartesian products of directed cycles

- Problem: https://mathdb.com/p/377269
- Source: https://mathdb.com/p/377269; https://arxiv.org/abs/math/0110073v1
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Torus377269.expanded_unconditional`, `Torus377269.expanded_distinct_unconditional`, `Independent377269.literal_refutation`, `Independent377269.literal_distinct_refutation`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v1.md`
- Lean source: `directed-torus-accepted-proof-packet-20261115-v1.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Bounded SUBSTANTIAL: the mixed-length fiber-coverage obstruction uses forced vertical counts and the four-step square projection to obstruct prescribed endpoints. Inspected native arc-forcing subgroup tests are vacuous here; two-generator and equal-length positive theorems do not give this negative three-factor endpoint result. No complete inspected old-method specialization or exact public counterpart was authenticated. Short finite witnesses do not require a new named framework or unbounded counterfamily; worldwide priority is not certified. not_claimed: worldwide absence of prior proof; clean historical/current process; unread journal-final body equality; audit of trusted upstream theorem truth
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the prescribed-endpoint Hamiltonian-path characterization for Cartesian products of directed cycles. With three factors of lengths 2, 2 and 3, the distinct vertices at directed distance 1, which satisfies the characterization's congruence modulo the greatest common divisor 1, are joined by no directed Hamiltonian path; both the displayed universal statement and its distinct-endpoint reading fail. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Refutes the prescribed-endpoint Hamiltonian-path characterization for Cartesian products of directed cycles: even for k=3, lengths(2,2,3), and distinct vertices u=(0,0,0),v=(0,0,1), directed distance1 satisfies distance congruent to -1 modulo gcd(2,2,3)=1, but no directed Hamiltonian path exists from u to v. Vertices are the actual dependent Cartesian product and arcs advance exactly one coordinate modulo its length; directed digons include both arcs. The result refutes both the displayed universal statement and its distinct-endpoint interpretation, with all factors of size>=2.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in directed-torus-accepted-proof-packet-20261115-v1.zip.
