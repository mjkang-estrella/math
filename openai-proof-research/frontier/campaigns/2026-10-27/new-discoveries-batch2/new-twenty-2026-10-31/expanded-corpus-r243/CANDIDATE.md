# Candidate disposition

No eligible candidate survives this lane. No Lean packet is submitted, and no acceptance is requested.

Three strongest unresolved mechanisms, ranked by potential endpoint cost:

1. **344055, mixed-rank hypergraph power domination.** A genuine counterexample would have a finite closure certificate and relatively low Lean cost. Uniform rank-3 and rank-4 cases already have published bounds. The completed mixed-rank searches found none; a useful next search would optimize sparse mixed-rank configurations rather than resample dense hypergraphs. Any candidate must first be compared against all source L_q constructions and the Bjorkman uniform counterexamples. Those constructions do not themselves refute n/4.
2. **344313, geometric multi-chain enumeration.** The exact root-height model passes millions of cases and correctly uses complements in T_n. For heights a_ij in {0,...,m}, filter conditions and each split i<k<j impose max(a_ik,a_kj) <= a_ij and min(m,a_ik+a_kj) <= a_ij <= min(m,a_ik+a_kj+1). Roots with j<=t have height zero. A uniform bijection or counting proof is still missing; finite counts are not a theorem of the reserved scope. Lean cost is substantially higher than a finite obstruction.
3. **343214, quadratic image designs.** The finite centroid reduction makes a stabilizer search cheap: because the image size is nonzero in characteristic p, every affine stabilizer fixes the image centroid. Translating it to zero reduces the affine search to all scalar multipliers. Searches through GF(3^9) pass. The source already supplies the orbit and size machinery, so only a genuinely substantive uniform stabilizer theorem could qualify; an elementary parameter extension would not.

The apparent Morse-link discrepancy at n=785 is explicitly **not** an eligible candidate. The source supplies the weighted path model and the exact finite-height truncation algorithm that computes it. It therefore falls within the user's source-formula exclusion, irrespective of whether the literal discrepancy has appeared elsewhere. See MORSE-DIAGNOSTIC.md and the exact logs.

The exact-source fidelity and literature limits of the other 16 records are in results.json. In particular, an old full-Fin/full-Wing result must not be confused with the arbitrary-submodel conjecture, a cofactor maximality theorem must not be confused with generic rigidity maximality, and finite incidence or Ramsey censuses must not be substituted for asymptotic or infimum claims.
