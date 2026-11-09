# Proof dossier: MathDB 333709

Draft, AI-assisted. The precise theorem is nonexistence of an inclusion-minimal percolating set of exact synchronous time 2 in PG(2,5) at threshold 5. Taking q = r = 5 refutes the read universal Conjecture 20. No acceptance or priority is claimed.

The complete readable reduction is in paper.md, Sections 3–5. Its steps are:

1. Construct the 31-point plane by normalized F5 vectors and dot-product lines. Verify all plane axioms.
2. Inflationarity and monotonicity force stabilization by 31 rounds. Minimality supplies canonical closed deletion separators that omit the deleted point. Conversely such separators exclude every proper percolating subset.
3. Initial state, first state, exact line activations and separators form a finite Boolean system equivalent to a target set. Nonfull first state and full second state enforce exact time 2, including exclusion of time 0.
4. A percolating set cannot lie in a line and contains a noncollinear triple. The 86 checked incidence permutations normalize the triple to indices 0,25,30, preserving all dynamics and minimality.
5. Local forbidden-row clauses encode the finite constraints; the semantic bridge is proved in Lean. The 14,695 base clauses plus three positive units give the exact 14,698-clause normalized formula.
6. Each RUP addition is a consequence of original or earlier derived clauses. The final empty clause refutes the normalized formula. This dossier freshly checks all 129,671 additions using the included data and independent arithmetic code.
7. The supplied 830-module Lean packet establishes the unconditional endpoint Percolation.not_conjecture20_unconditional : ¬ Percolation.Conjecture20. Its proof uses the general proved bitmask RUP checker, kernel-reduced finite equations, concrete input entailments and named earlier clause proofs. The expression builder is audited too. Only propext, Classical.choice and Quot.sound are reported in the endpoint closure.

The Lean packet is EXTERNAL and hash-bound, never duplicated in these ZIPs. See packet-reuse-receipt.json for its absolute path, SHA-256 and safe-extraction result. Source code presence and Python checking do not themselves constitute a fresh Lean replay. The developer's supplied full fresh replay passes; this manuscript lane ran no Lean or solver. Root completion receipts remain pending unless recorded in root-status.json.

The independent adversarial review independently derived a different normalized encoding and checked its certificate. It reviewed an earlier partial formal packet; it did not independently replay the final unconditional endpoint. Historical encodings and counts are separated in the paper and paper-number-audit.json.

The original arXiv source, exact raw MathDB line, review, all formal-round documentation and root rulings are copied under evidence/. The source has the accented author names given in the bibliography. The journal version remains unread; root ruling r2 records positive author-side retention evidence with a qualified limitation. No odd-order obstruction or short human proof is asserted.
