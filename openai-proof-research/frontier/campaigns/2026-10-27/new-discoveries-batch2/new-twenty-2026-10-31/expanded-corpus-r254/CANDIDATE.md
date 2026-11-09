# Pi handoff: 331498, conditional exact coefficient search

Status: executable mechanism, **no witness**, no novelty/significance clearance, zero credit. Root must not describe this as a resolved problem. This is the preferred next experiment among the reserved twenty; it is not an authorization to skip source gates.

Read ATTEMPTS.md for the exact recurrence and ordinary proof of its soundness. Read the original ABM P2, not the secondary source's undefined a,b,c,d. The endpoint is a negative coefficient of G1(y-1) for a positive balanced vertical word V, summing over **all** quarter-plane loops with that projection and fixed horizontal semilength m.

Before heavy work: finish version/journal/citing-work and printed-figure checks for the original and secondary sources. A DOI landing response is not the journal proof body. In particular, rule out a later complete P2 proof, and preserve the source's negative N1-N3 examples as exclusions. Current registry screen has bounded nonfindings, not global clearance.

Pi model required by the user: spark/GLM-5.3-Flash-EXL3 through Pi, high thinking. Root assigns it; this research lane has not delegated or executed the search.

Suggested bounded first task after source qualification:

1. Implement integer-vector dynamic programming in the y basis, with the state and recurrence in ATTEMPTS.md. Independently implement the x-basis version and binomial transform as a control.
2. Positive controls: m=0 gives G=1 for every V; V empty gives the m-th Catalan number. Confirm the original paper's tested range on a small sample, not as a new result. Reproduce its fixed-both-projections N2 polynomial **in a separate control mode** to prevent silently changing the quantified family.
3. Try only n=6, m=6, then n=6,m=7 and n=7,m=6 if resources remain, with vertical Dyck words ordered by multiple runs. Skip the already tested n,m<=5 range except controls. Cap at two CPUs, CPU 120 seconds, wall 140 seconds, sampled RSS 6 GiB. Stop at the first negative coefficient or the cap. Do not infer truth from a negative search result, and do not start an unbounded sequence of jobs.
4. If negative: output V, m, coefficient index k, b_k, the x coefficient vector, y coefficient vector, and the entire DP state table with deterministic order and hashes. This table has at most 5(2n+1)(m+1)^2 states, each a short integer vector. Independently replay the table by the second recurrence.
5. Only after an ordinary/source/novelty review of an actual witness, formalize the finite recurrence and the bijection between paths and transition sequences. Prove quarter-plane constraints from both prefix heights and count NW/ES adjacency explicitly. The literal Lean negation must quantify over all horizontal projections, not a chosen horizontal word. Prove uniqueness of expansion in powers of x+1 by polynomial substitution. Audit every bridge and allowed axioms; no native_decide, sorry, axioms, or numerical assumptions.

Alternative 331097 is a complete ordinary proof but likely excluded as routine; do not spend Pi time on it without root's concrete significance ruling. The soliton routes are parked because a source-faithful finite mechanism is not yet specified well enough for a useful bounded task.
