# Frozen target T008M

Author-side freeze: 2026-10-17, during r28. This document is written after the prefix/suffix construction has been sketched in reasoning and announced to the parent, and after reading the pinned main theorem, weighted free-Lie/PBW interface, and the operative introductory/construction statements of Cagliero–Rojas and Burde–Eick–de Graaf. It is written before a complete checked proof, implementation, formal-interface assessment, or contribution decision. It is not a claim that the target was chosen before any successful mathematical insight. The initial family200 rigidity assertion was rejected before any freeze and is separate.

For every field F of characteristic zero, let W_F be the rational Grothendieck–Teichmüller Lie algebra of the stipulated source after scalar extension to F, with its Ihara bracket and weight grading. For every integer N≥3 let g_N,F=W_F/(direct sum of weights>N). Write mu_F(g) for the minimum dimension of a faithful F-linear representation, and mu_nil,F(g) for the minimum dimension of a faithful representation by simultaneously strictly upper triangular matrices over F.

Prove absolute constants c,C>0 and an absolute integer N0 such that, for all characteristic-zero F and all N≥N0,

    c rho^(N/2)/sqrt(N) ≤ mu_F(g_N,F)
       ≤ mu_nil,F(g_N,F) ≤ C rho^(N/2),

where rho>1 is the real root of rho^3-rho-1=0. In particular both minimum dimensions have Nth-root limit sqrt(rho). The upper representation must be given by an explicit finite matrix-state construction, whose generator matrices have entries0 or1 in free homogeneous generators. The source does not canonically choose these generators, and no claim of a polynomial-time conversion from arbitrary Ihara coordinates is included.

All N and all characteristic-zero fields remain in scope; no bound on nilpotency class, number of generators, or allowed weights may be added later. The target is the displayed two-sided bounds and exact exponential rate, not an exact leading constant or polynomial correction. Those stronger claims have never been proposed as the task. No restriction to a bounded generator alphabet is allowed.

Potential new operation: a representation of the full associative word algebra truncated by weight using prefix-deletion states and suffix-creation states with integer gap markers. A generator crossing the chosen weight threshold must be represented by one transition; no assumption that the threshold lies between letters is allowed. Three adjacent truncation caps may jointly detect weights with different residues modulo3. Faithfulness, the precise dimension estimate, and the primary-operation comparison still require a complete checked writeup.

Already paid and not claimed new: the source freeness theorem, Hall/PBW embedding, the weighted Witt dimension formula, dimension-count lower bounds, and general Ado/enveloping-algebra constructions. The earlier algebra_geometry proposal expressly declined a dimension-formula corollary. The proposed gain must reside in the compressed matrix construction, not those ingredients. Independent contribution review may still find it technical or known; no acceptance is claimed.
