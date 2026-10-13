# Parent obstruction: the natural block measurements are Bell local

2026-10-13. Technical parent observation for the projection construction of the pinned zero-key manuscript. This is not a new accepted finding and does not prove that its state is Bell local for all measurements.

Use the source notation: Q contexts, disjoint label sets I_q, and projective decompositions (P_i)_{i in I_q} of the identity on C^D. The normalized Choi state rho=C/(Q²D) from the projection criterion satisfies

    C_(i,a),(i,a)=tr(P_i P_a).

For external setting q, Alice measures computational basis labels i in I_q and reports failure for the complement. Bob does the analogous measurement for r. Then

    Pr(i,a | q,r)=tr(P_i P_a)/(Q²D),  i in I_q, a in I_r.

The probability of both passing is 1/Q², and conditional successful outcomes are the familiar projective-overlap correlations tr(P_i P_a)/D. These conditional correlations do not by themselves constitute a Bell violation, since the filters depend on the requested setting.

Indeed, the entire behavior INCLUDING failures has the following explicit local model. Choose q0,r0 independently uniformly among the contexts; conditional on them choose labels (i0,a0) with probability tr(P_i0 P_a0)/D. Send the shared variable (q0,r0,i0,a0) to both parties. Alice reports i0 if q=q0 and failure otherwise; Bob reports a0 if r=r0 and failure otherwise. Both-pass probabilities agree with the displayed formula. For the Alice-only-pass outcome i, summing over Bob contexts r0 != r and their outcomes gives (Q-1)tr(P_i)/(Q²D); the quantum probability is the same because each context resolves the identity. The Bob-only probabilities agree symmetrically. Both-failure probabilities are then fixed by normalization and equal (1-1/Q)². Thus all output probabilities agree.

No numerical computation is used. This rules out a particular immediate measurement proposal, not a different POVM, coherent erasure of the block labels, or all Bell nonlocality. It is the usual setting-dependent detection loophole written explicitly for this source state. Do not count postselected contextual correlations as the requested unconditional bipartite Bell theorem.

Source identity and reading are in sources/i329_parent_zero_key_bell/reading.md; the relevant projection-criterion Choi entries were read in projection.tex lines 1–220 in the preceding parent context. Independent audit is still required before using this calculation elsewhere.
