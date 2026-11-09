# Sustained routes and remaining lemmas

## 327574, lex ideals

Recovered the actual conjecture: Conjecture 4.1 extends Theorem 1.2 of arXiv:1404.0118. It asserts equality of the length-1 and length-2 tails (including coefficients) in the Boij–Söderberg decompositions of L and (L,x); it does not assert equality of their entire diagrams. The paper excludes L=x(x,y,z^t)+J with J not a pure (y,z)-power and 1<t<k-1 from its proved theorem.

Implemented enumeration of all lex initial segments in each degree, forced upward closure and a terminal full degree. Minimal generators feed the exact Eliahou–Kervaire formula beta_(i,d+i)=sum binomial(maxvar(m)-1,i). Greedy decomposition uses Fraction-valued pure diagrams, not float comparisons. All 4,139 proper Artinian lex ideals containing the entire degree-7 component were tested, including all smaller terminal degrees. No mismatches. A second depth-first sweep reached 213,155 ideals with terminal degree at most 11 before its 105-second self-cap; that traversal is incomplete and strongly weighted towards degree 11. Raw coverage by terminal degree is retained.

Ordinary proof attempts: the EK identity gives beta(L) from generator distribution, while adjoining x deletes every generator involving x. The pure-diagram algorithm's first-column residual changes at each length-3 step. Agreement of the short tail would follow from invariance of the residual two-column table when the last length-3 entry vanishes. Neither equality of Hilbert numerators nor positivity alone gives this invariant: both lose the intermediate pivot choices. The paper's proof handles these choices by degree inequalities and the exceptional x(x,y,z^t) family is exactly where their ordering is not controlled. Remaining lemma: prove those pivot/residual relations in that exceptional family, uniformly over the y,z staircase. No proof and no Lean endpoint claimed. The 2021 published manuscript and the author's thesis are identified by saved web receipts but not fully compared; novelty is not cleared.

## 330606, stable second hypersimplices

Recovered cyclic r-stability (two 1 positions separated by cyclic distance at least r) from Braun's survey, the Braun–Solus source arXiv:1408.4713, and its subsequent journal lead r-Stable hypersimplices. The search uses the nonnegative cyclic-window H-description: total coordinates 2t and each cyclic r-window sum at most t. For n>2r the polytope has dimension n-1. For every n=3..9 and r=1..floor((n-1)/2), enumerated ALL integer vectors at dilations t=0..n-1, and applied the exact numerator transform h_i=sum_j(-1)^j binomial(n,j)L(i-j). All 16 vectors are unimodal. The even n=2r degeneracy is not run through the wrong dimension formula. Lattice-point computation is a diagnostic, not a Lean Ehrhart bridge.

Proof attempts: the shelling expresses h* using graph independence polynomials; known claw-free real-rootedness immediately handles specified boundary cases but not arbitrary stability. Hibi–Solus' Gorenstein framework gives n=kr+k and the near-maximal stability cases, not every r. Gorenstein symmetry is rare, so that framework cannot simply close the full question. No proof of arbitrary-r real-rootedness or a global coefficient injection was found. Remaining lemma: a coefficient matching/unimodality mechanism for the non-Gorenstein intermediate r family. The source already reports computations and partial cases, so reproducing those gets no credit.

## 331705, Cassinian balls

The third route reaches a full refutation. See CASSINIAN-ORDINARY-PROOF.md and the kernel-checked source packet. The source boundary supremum was bounded on its full continuum, not inferred from the sampling grid. No credit or literature-priority assertion is made.
