# Parent lead — a non-EB entropy remainder

2026-10-13. Research target only; no new theorem or acceptance. I289 pays arbitrary-state stability in the entanglement-breaking region by a short combination of older results. Its independent contribution review is still running and currently leans technical. Merely extending it within the EB region is not a separate target.

## Classical input actually checked

[King, quant-ph/0103156v2](https://arxiv.org/html/quant-ph/0103156v2), Theorems 1–3, proves unital-qubit additivity using balanced rank-one measurement ensembles. The parent read the complete convex-decomposition and Epstein arguments (Sections 3–4), plus the entropy differentiation in Section 2. In the notation of equation (49), for pure input psi and a tail channel Omega the bound is

    S((A_s tensor Omega)Ppsi)
      >= h((1+s)/2) + sum_j c_j [S(Omega Pchi_j+)/2
                                      +S(Omega Pchi_j-)/2].

The measurement bases depend on the root marginal; both outcomes are balanced and their conditioned tail inputs are pure. All coefficients are chosen before applying Omega, from the root marginal alone. This is credited old material. The authenticated raw body was read in memory, not retained.

## Exact unpaid strengthening

For a compact s interval inside (sqrt(2)-1,1), can one choose such a King decomposition with an additional remainder

    kappa_s (1-Tr rho_root²),       kappa_s>0,

uniform in the tail dimension, the pure bipartite input and every CPTP Omega? Here A_s has Bloch action (s,s,s²). The residual is relative to the SAME measurement ensemble in the old inequality, not to the tail minimum or a separately optimized ensemble. A proof or a counterexample is needed. This is not assumed from additivity or strictness at fixed dimension.

If true, iterate the residual with the arbitrary-ensemble product-test drift from I289 to obtain F_n <=2D_n/kappa_s. Old global product-test soundness and the already-paid amplitude KL/Hellinger argument would then give the unital GAD theorem outside the EB region. Thus this strengthening is a concrete sufficient bridge, not the conclusion itself.

The Epstein/phase-damping step alone cannot pay this remainder. For a maximally entangled root and identity tail channel, balanced phase damping gives entropy h((1+s)/2), while its dephased state has entropy log 2, saturating the old phase-damping entropy bound. A successful proof must retain the mixture/Jensen losses as well, or use a different mechanism. Conversely erasing the tail makes those Jensen differences vanish but introduces slack in the phase-damping bound. Trading these two losses uniformly is the suggested new operation.

## Alternative mixture and its missing step

For s>=1/3, A_s=(1-s)D_s+s B_s, where B_s has Bloch action (s,s,2s-1), with Pauli probabilities (s,(1-s)/2,(1-s)/2,0). Both components have maximal output length s and additive minimum entropy by the old unital theorem. This is a routine channel identity, not a finding. I284 already has a related mixture valid for every s; selecting only an all-depolarizing tensor branch loses exponentially with n.

One would need a quantitative bound using all heterogeneous branches. Randomly selected local symmetric-projector tests have a useful elementary inequality: if Pi_S=product_(j in S) Sym_j and sites are selected independently with probability p, then 1-E Pi_S >= p(1-product_j Sym_j), because these projectors commute. But no entropy-deficit bound for those partial tests is supplied here. Do not substitute this projector identity for the missing channel estimate.

The full GAD target, any stronger King remainder, and heterogeneous-branch stability remain open in this note. The prior false sum of original marginal determinants remains excluded; the intended costs would be conditional along a common adaptive tree. No numerical scan or inverse-channel argument has been used.
