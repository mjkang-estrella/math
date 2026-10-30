# MathDB 372496: full counterexample certificate

The universal conjecture is false. The source is Teng Zhang, arXiv:2601.07286, Conjecture 5.5. The primary HTML and full MathDB post are saved in `../sources`; `source.json` records UUID, posted solution identifier, author credit and hashes. The k=5 counterexample was already posted by Shivam Patel. This package asserts no discovery or worldwide priority.

For Hermitian complex matrices the source defines H=A+B, Q_k=Σ_{j=0}^k binom(k,j) A^j B^(k-j), and R_k=(Q_k+Q_k*)/2. In `formal/WeakMajorization.lean`, Q and R are these exact definitions, including every binomial term. Take A=[[0,0],[0,-2]] and B=[[0,1],[1,0]]. They are Hermitian. Exact multiplication gives H^5=[[-12,29],[29,-70]], Q_5=[[0,1],[121,-122]], R_5=[[0,61],[61,-122]]. Hence tr(H^5)=-82 while tr(R_5)=-122.

`WeakMajorized` is the usual initial partial-sum inequality applied to the eigenvalues in decreasing order. The Lean theorem uses mathlib's actual `IsHermitian.eigenvalues₀`, whose antitonicity is established upstream by the spectral theorem; no proposed spectral values are inserted as hypotheses. `trace_real_eigenvalues` derives the sum of those ordered eigenvalues from mathlib's trace identity and its explicit reindexing equivalence. `weakMajorized_sum` takes the full-rank partial sum. The strict trace reversal proves the negation of weak majorization, and `source_counterexample` bundles both Hermitian hypotheses and admissible exponent 5.

This is a full refutation of the quantified source conjecture, not a bounded verification of it. The different singular-value question in the source is outside the outcome. The posted stronger every-odd-exponent failure is also outside the claimed theorem.

Replay: from repository root, run `python3 openai-proof-research/frontier/campaigns/2026-10-25/twenty-proof-campaign/verify_outcome.py openai-proof-research/frontier/campaigns/2026-10-25/extension-matrix-lane/weak-majorization`. All declarations are compiled and audited with the pinned Lean 4.34.1 dependencies. Only standard logical axioms are permitted. Independent source-fidelity review remains the parent's integration gate.
