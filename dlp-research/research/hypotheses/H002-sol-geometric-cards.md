# H002 independent geometric-transfer cards

Native Sol `/root/h002_geometry_transfer`, fresh initial brief without other
proposal reports, completed four speculative cards. No experiments or edits.
Root condensed below; no accepted gain. q denotes subgroup order, ordinarily ≍p.

## V1: Marked quotient surface and a short quadratic relation

Construct E²/⟨(G,Q)⟩ with its input marking and induced (1,q)-polarization.
An integer matrix [[a,b],[c,e]] preserves the kernel exactly when
`b*d²+(a−e)*d−c = 0 mod q`. A non-scalar marked endomorphism could thus give
at most two candidates, verified against Q. After removing scalar matrices,
the relation lattice has rank3, indexq, and a nonzero O(q^(1/3)) coefficient
vector by pigeonhole. Existence is not an algorithm for finding it.

Conditional target: ~q^(1/3) TOTAL work, including target-dependent quotient
construction, marked ring extraction, compact evaluation, auxiliary torsion,
polarization operations, failures and memory. Dense component maps already
have degree about q^(2/3); compact evaluation is essential. No such algorithm.
Unpolarized quotient is isomorphic to (E/⟨G⟩)×E by the unknown shear involving d;
abstract invariants alone discard d. Prior art distinguishes abstract endomorphism
rings from evaluable generators: [Anni et al.](https://arxiv.org/html/2503.08925v1).
[Square-root Vélu](https://arxiv.org/abs/2003.10118) supplies no sub-square-root
surface construction. Novelty unknown. Cheapest gate: inspect required input
representation/extraction; reject a procedure already enumerating the q-kernel
or costing sqrt(q), not every possible compact representation.

## V2: Relative divisor sieve with certified Prym residue

For explicit f:C→E of degree m coprime to q, use f_*f^*=[m]. Decompose
f^*(aQ+bG) into a small divisor factor base plus an explicitly certified element
of ker(f_*). Projection yields maQ+mbG+Σ n_i P_i=0. Known base logs and a≠0
give d. Hope: complementary dimensions aid RELATIVE decomposition without full
Jacobian smoothness. For target q^(1/3), B=q^(1/6), sparse algebra ≈B², obtaining
B relations needs success ≥q^(-1/6) if each trial is polylog. These are target
requirements, not established probabilities. Charge genus, cover, Riemann–Roch,
factorization, kernel certificates, rank, target descent, projections and memory.
[Standard genus index calculus](https://eprint.iacr.org/2004/153.pdf) does not
by itself help an order-q≈p embedded subgroup. Cheapest gate: push principal
divisors through `f_*div(h)=div(Norm(h))`; determine whether all proposed savings
collapse to ordinary elliptic divisor smoothness. No relative generator supplied.

## V3: Arithmetic-surface sieve on closed divisors

Lift E as the p-fiber of a low-height arithmetic model. Use bounded-degree
horizontal closed divisors as a fixed factor base, specializing their degree-zero
trace classes to E(F_p). Sieve principal divisors with smooth horizontal support,
accounting for vertical corrections; target descent plus linear algebra recovers d.
Aspiration: NFS-like L_p(1/3) total time/memory, wholly conditional on useful
smoothness and descent. Count lift heights, number fields, factorization, every
specialization, corrections, failed sieve trials and descent. Compare the rational
lift route [Silverman–Suzuki](https://doi.org/10.1007/3-540-49649-1_10) and
[NFS-DL](https://epubs.siam.org/doi/10.1137/0406010); novelty unverified.
Cheapest falsifier: factor the candidate function's divisor and integer norm
separately. Smooth integer values/vertical primes need not imply fixed horizontal
factor-base support. No explicit relation generator yet.

## V4: Reciprocity and a readable local invariant

Construct an explicit global order-q cohomology class with nonzero local pairing
on G at p. Reciprocity would give d as the ratio of sums of invariants at other
places for Q and G. Polynomial work is only an aspiration if lift heights,
global descent objects, ramification, local precision, pairings and generator
conversion are all compact/cheap. [Frey §§5–7](https://numdam.org/item/10.5802/ambp.250.pdf)
already describes this transfer and a possible hidden DLP in converting the
cyclic-algebra generator to Frobenius. Novelty unverified. Cheapest gate: specify
class construction and local compatibility; reject a free invariant oracle or
generator choice encoding d. No concrete improved implementation exists.

Proposer prefers V1 representation gate. Other cards require algebraic bridges
before experiments. All compare to the strongest applicable square-root baseline;
no auxiliary-easy-problem result changes full-size ECDLP hardness by itself.
