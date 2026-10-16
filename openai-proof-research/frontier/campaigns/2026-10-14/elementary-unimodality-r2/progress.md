# Progress

- Scope frozen before sustained proof work. Read project AGENTS.md. Authenticated r8 seal and both manifest digests; full entry/pinned-blob authentication next. No frozen code executed.

- Authenticated all 24 r8 inputs and 19 outputs, exact 47-file tree (including manifest/seal metadata), and all ten pinned Git blobs against the complete tree. No frozen code executed. Private source/context copies retained here.
- Read all of graph section and witness section; exact source labels graph:digits, graph:kernel, graph:reciprocity, route:switch, route:history-recursion, route:history-series, route:parity, route:exact, route:witness. Reviewed main:hessenberg and its explicit lack of cup-product compatibility.
- Active route: trim the history recursion to states/transitions that genuinely contribute to a fixed (u,x_lambda) target. Global polynomial support may force relevant individual jump series to be finite Laurent polynomials; then isolate what still prevents centered Lefschetz strings. No claim that finite support alone proves unimodality.

- Proved the live-history finite-support lemma and rational bar invariance of every jump via incoming uniqueness. Thus every live jump for a nonzero target is a finite centered positive polynomial; centered-string positivity is still unpaid. Full arguments saved in checkpoint.md.
- Read Davison (2018) primary source Section 2.1, including compatible pairs, toric frames, Laurent expansion and mainThm (= published Theorem 2.4). This removes acyclicity only for cluster monomials, not arbitrary source sections.
- Examined the actual D=2 section Theta_(d1)=U. Its natural two-arrow specialization is the regular function (x^2+y^2+1)/(xy), not a cluster monomial; all-mutation proof uses the complete rank-two recurrence, not a bounded search. Does not exclude arbitrary larger realizations.

- Completed the full-scope report: no proof or counterexample. The unpaid step is nonnegative centered-string multiplicities of the entire partition-specific finite path sum. Local live-jump Lefschetz positivity is a sufficient stronger unproved operation.
- Proved parity via the quadratic-refinement automorphism v->-v and bounded every live jump's radius by |E(G)|. Source rationality is essential to the bar proof; no reversal of an arbitrary Laurent completion is used.
- Authored exact standard-library supporting checks; immutable receipt passes ten cleared-denominator dilogarithm identities, 65 simple jumps, 729 quadratic identities and 18 rank-two exchange identities. No actual cyclic-chart jumps or full witness implementation/census claimed.
- Wrote read-only verifier and disposable-copy rejection controls. Final sealing/verification next.

- Completed the three disposable-copy rejection controls. Candidate corruption and missing-source cases reject before checker execution; the resealed disposable checker-failure case reaches the authenticated subprocess and rejects with both trees unchanged. Copies removed.
- The first rejection-test invocation redirected stdout into its already-inventoried receipt, invalidating that provisional inventory and preventing its failure branch from being reached. Corrected the invocation to capture stdout in memory and save only after the test completes, then reran successfully. No frozen-r8 writes or code execution occurred.
- Final disposition remains UNRESOLVED with full original scope, campaign 4/10 and no nomination. No further source/witness implementation, mutation search, graph census, formalization or manuscript effort is claimed.
