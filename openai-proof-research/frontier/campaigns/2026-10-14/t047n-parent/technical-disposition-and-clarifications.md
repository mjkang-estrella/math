# T047N: full proof pass, technical contribution

The parent adopts PASS_FULL_T047N from the independent proof review and TECHNICAL from the separate contribution review, for the entire unchanged frozen target. No result is counted; the campaign remains 13/20. No marked, finite-n, neighboring-family or other narrowed variant is substituted. Formal support, manuscript and release work are not escalated for this technical candidate. All frozen author and review bytes are preserved.

## Required contribution attribution

The exact DK/divisor/reduced-staircase calculation is a technical transfer, not a new mechanism. Source047's `deg:graded-injection` and `prop:graded` already give the n=2 reduced staircase by taking homogeneous components; `lem:induced-lnd` and `prop:extracted-lnd` already give the per-LND upper containment DK(A_2) contained in S_2. The all-n changes preserve the same torsor, cubic and rigidity theorem. The lower DK containment uses standard denominator clearing and a quadric LND; divisor recovery uses the canonical affine modification; the staircase uses the homogeneous pieces of an extended Rees algebra.

Residual-coordinate theory, specifically Dutta–Lahiri Theorem 3.4 as deployed in the source introduction and identified by the contribution reviewer, also supplies the cylinder for every n: H_n modulo p is the same coordinate linear form, while away from p it is a coordinate. The explicit cylinder calculation is retained as a valid source adaptation. Neither reviewer nor parent claims to have read Dutta–Lahiri's primary body here; the source's deployment and the explicit calculation are the available evidence. General exponent recovery through DK/ML, modification divisors and contractions remains credited to Ghosh–Gupta and Ghosh–Pal.

The prior-primary issue is limited to the displayed higher-contraction step: omitted powers of G genuinely belong to the contraction in the unequal-exponent contradiction branch. This is not a counterexample to either theorem conclusion. The contribution reviewer checked an m=1 repair using the primary papers' admissible-filtration tools; m>1 was not checked. The repair is not credited as T047N's contribution. The parent checked the m=1 implication: fbar in (gbar^k), gbar in (fbar), k>=2, forces gbar to be a unit; a nonzero constant special fiber would make the distinguished x a unit in A, incompatible with DK(A)=B since LNDs kill units and x^-1 would then belong to the polynomial B. No whole-paper correctness claim follows.

The bounded search found no exact duplicate. Unread Danielewski-family bodies and other snippet-only leads remain unread; neither absence of a duplicate nor a changed coefficient ring establishes substantiality. The contribution review's optional extraction/rigidity interface question is answered by the independent full proof review.

## Optional proof clarifications retained for future use

O1–O2. The grading action on G fixes R and scales tau by lambda^-1. Its lift to the pulled-back line bundle fixes R-tilde and scales V by lambda^n. This preserves tau^n V=v, is linear on the line bundle, and commutes with fiber scaling. Conjugating the normalized additive lift and using its uniqueness gives the required degree-j homogeneity. This re-proves the argument for general n without assuming D_0 preserves R. The induced-LND and order lemmas require the exact-weight representatives already established, plus the characteristic-zero domain hypotheses; they do not require n=2.

O3. As an R-algebra, A/pA is (R/I)[M]: the determinant-one change of F,J turns its sole relation into L=0, and R/I is C[s,u]. Thus fibers over the center are affine lines over the residue field; fibers elsewhere in V(p) are empty. Isomorphism is local on the target, so the union of all opens over which the canonical morphism is an isomorphism is well defined and equals D(p), including nonclosed points.

O4–O5. After p is inverted, H_top generates the prime relation xy-z(z+1). Its reduction modulo p is nonzero. Unique factorization excludes any other factor becoming a unit on localization, because such a factor would be a power of p. Hence H_top is prime before localization. The local noetherian domain S_(pS) has nonzero principal maximal ideal (p), so is a DVR.

O6. The degree-r monomials in R[tau,I/tau^n] have the form f^a g^b tau^(i-n(a+b)) with i>=0 and n(a+b)-i=r. Their coefficient ideals sum to I^ceil(r/n), because powers of I decrease with the exponent and the minimum permitted exponent is attained. This is the precise upper-inclusion calculation for the reduced contraction staircase, using the exact graded ring rather than an assumed presentation bound.

O7–O8. The author verifier does not itself anchor the supplied source-tree file, and its original controls do not exercise that option. Parent separately anchored the canonical tree at eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b, replayed the proof reviewer's independent complete-tree comparison of 21 bodies and eight copied source-layer cases, and retained those limits rather than editing the frozen verifier.

O9. In A[p^-1], set T=xy-z(z+1), so u=T/p^(n+1). For any coordinate partial delta in x,y,z,

    delta u = (delta T)/p^(n+1),
    delta s = delta y + (u^3-2x) delta x + 3xu^2 delta u,
    delta F = (delta x-2s delta s-3u^2 delta u)/p^n,
    delta J = (delta z-s delta x-x delta s)/p^n.

All numerators apart from these displayed denominators are in A. Thus p^(2n+1) delta preserves all generators of A. Since p is invariant, this multiplier preserves local nilpotence. Treating u as an independent coordinate would omit a necessary chain-rule term. The candidate's sufficiently-large-power argument is correct; this makes a sufficient power explicit.

## Parent validation limits and review independence

Parent read both full reports, proof re-derivation, reading limits and executed verifier/control scripts. Review anchors, positive checks and wrong-anchor checks pass. Parent replayed the proof packet's 16 copied integrity cases, independent blob comparison and eight source-layer cases, and the contribution reviewer's 23 copied author-packet cases. The proof reviewer's finite algebra checker was not rerun by parent and remains reviewer support evidence. Contribution-packet extra-object/link controls beyond the recorded parent subset remain reviewer-reported evidence.

The primary-formula clarification was written after proof-review dispatch; that reviewer did not read it or the contribution report. Neither primary contraction formula is used as a premise of T047N's proof, so this timing does not change the full proof gate. The contribution reviewer did receive and assess the clarification, without reading the parallel proof packet. Parent and discovery-agent discussions were author assistance, not independent review.

Hashes and finite tests are not mathematical proofs. Original prose Myeongjin Kang, CC BY 4.0. Uploads remain stopped.
