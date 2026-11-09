# An observable stopping event: proposed focused route, not a source resolution

Work under the literal move-type law and split-indicator convention in the bound r279 report. The worker must confirm those conventions against the primary body before relying on this note. No novelty or discovery credit is claimed; counts remain 9/39/next40.

Let T be the terminating game length and C=N-Z(N), where Z(N) is the number of tokens in the terminal Zeckendorf representation. Each combining move reduces the token count by one; each splitting move preserves it. Therefore every complete game has exactly C combining moves. Let X_i be one for a split at step i and zero for a combine, with X_i=0 after termination. Put S_m=sum_{i=1}^m X_i.

For every integer m>=1 there is the exact identity of events

    {T<m} = {m-S_m>C}.

Proof: if T<m, the total split count is T-C and S_m=T-C, giving m-S_m=C+m-T>C. If T>=m, the quantity m-S_m counts actual combines among the first m moves, hence is at most C. This does not assume that using all C combines immediately terminates the game: a remaining all-split suffix is allowed. The strict inequality handles T=m correctly.

Let L be the time of the last split, with L=0 if there are none. For any k>=0, B={L>=m+k} is the suffix event that some X_i=1 for i>=m+k. A={T<m} is measurable in the first m indicators by the preceding identity. A and B are disjoint. Thus, with the source's temporal-cut convention,

    alpha_N(k) >= P_N(T<m) P_N(L>=m+k).

This is an exact lower bound on the full sigma-algebra mixing coefficient, not just a covariance estimate for a selected pair of individual indicators. It is unaffected by padding to the deterministic maximum game length.

Consequently, if one can find N_j, m_j and k_j tending to infinity with P(T<m_j)>=a>0 and P(L>=m_j+k_j)>=b>0, then for every 0<=k<=k_j the same cut gives alpha_N_j(k)>=ab. For every fixed delta>0, the source's weighted sum is then at least (ab)^(delta/(4+delta)) sum_{k=0}^{k_j}(k+1)^2, which diverges. That would refute Question 6.5 for every choice of delta and C at once.

What is missing: those two uniform positive-probability tails with growing separation. Existence of long and short legal paths is insufficient; their probabilities under uniform legal move types might vanish. A variance lower bound alone need not give the required separated quantiles. Nor can a CLT or a short combine-only terminal suffix be assumed. The new focused task should attack precisely this probabilistic statement using local random diamonds, conditioning or regeneration with quantified probabilities, and compare source partition laws with the actual move-type law. If it fails, retain this lemma only as a reduction.

No Lean, manuscript, registry clearance, full ordinary endpoint, acceptance or shared edit is supplied.
