# I199: structured Foulkes bridge

2026-10-12. **UNRESOLVED — NO SUBSTANTIAL NOMINATION.** Eight findings remain accepted; two remain. All corpus theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. This is an unsealed research record. Neither acceptance gate has been run.

## Exact target and its significance

The selected target was surjectivity, in every finite dimension over C, of

    mu_{7,8}: Sym^8(Sym^7 V) -> Sym^7(Sym^8 V).

It is sufficient to prove this in dimension seven. Transpose duality and McKay propagation would imply the entire ordinary seventh Foulkes case, including the automatic diagonal comparison at b=7. The accepted sixth-case theorem does not imply this canonical seed. The inspected primary literature does not settle it; this is not a claim that its worldwide open status has been established.

The [analytic record](../experiments/i199_foulkes_structured/analytic-attempt.md) develops two routes, proves their auxiliary assertions, and identifies exact gaps. Neither route proves or refutes the target. F210's bound b>=(a-1)^2 remains a paid technical deduction and is not renominated.

## Route A: actual annihilators, with a stronger restriction

For a symmetric seven-linear form T on Sym^8 V satisfying the original decomposable-diagonal condition, the source's first two steps give

    T((x^6 Q)^6,t^8)=0

for every decomposable quadratic Q and all x,t. The two derivative weights are positive: (8,6) and (7,6). The resulting six-linear form on Sym^2 V need not vanish by any available lower theorem. On ternary quadrics, polarization of det(Q)^2 is an explicit nonzero six-slot annihilator. It is not asserted to extend to a valid original T.

A further proved consequence uses the actual condition: if F(P)=T(P,...,P), then on every ternary quadratic subspace,

    F(x^6 Q)=det(Q)^2 L(x,Q),

with L of degree 42 in x and one in Q. The gradient of F vanishes at x^6 Q for decomposable Q; irreducibility of the rank-two determinant hypersurface forces the square. In dimension three, the possible nonzero restriction has only types (47,5,4) and (46,6,4) after the paid first-row certificate removes (48,4,4). These are possible restriction types, not claimed kernel constituents.

The kernel of restriction to x^6 Q remains uncontrolled. The analytic record gives explicit degree-seven catalecticant minors vanishing on that locus and proves one is nonzero by a Vandermonde construction. Those minors are not claimed to satisfy the original annihilator condition. Full all-slot jet identities are retained; they give coupled sums, and the attempt to free two slots produces additional derivative-distribution terms that were not eliminated.

## Route B: the normalization quotient itself

Let C=R/A be the finite-length normalization defect, considered as an A-module. The paid module-generation lemma gives

    C_j=A_1 C_{j-1} for j>=7,
    C_8=A_1^2 C_6.

Thus the exact missing estimate is **A_1^2 C_6=0**. F210 supplies only A_1^30 C_6=0. This is a multiplication question on the actual quotient, not a new name for ambient polarization.

C_6 already has a concrete nonzero determinant constituent (det V)^6 in dimension seven, absent from A_6 by the elementary Schur-length obstruction. Its nonzero products in R do not establish nonzero classes in C_8. Conversely, no proof of their membership in A_8 was found, and that one constituent would not exhaust C_6.

The chart proof still gives z(v)^36 in the conductor and its independent cubic range b>=252. It does not give two-step annihilation of C_6. In dimension seven the normalization has regularity 36. The exact sequence identifies C with H^1_m(A) and gives

    reg(A)=max(36,end(C)+1).

Since F210 already gives end(C)<=35, reg(A)=36 whether or not C_8 vanishes. The regularity theorem therefore does not supply the missing deficiency-module estimate. Brion's exact effective-bound statement was obtained from the publisher's sample and checked; its full proof was not obtained, and the displayed bound is not the seed.

## Reading, limits, and delivery

The [literature record](../sources/i199_foulkes_structured/literature.md) records full readings of Raicu–Sam–Weyman, Ikenmeyer, Cheung–Ikenmeyer–Mkrtchyan, and the full six-page Brion publisher sample. The sample contains Theorem 3.3's statement, not its proof. Relevant corpus files were read in the I198 directory and not duplicated. Known diagonal canonical kernels and ordinary representation comparisons were kept distinct. No claim of novelty is inferred from a failed keyword search.

The [authentication record](../experiments/i199_foulkes_structured/input-authentication.json) hashes actual inputs and retained external source bytes, with precise reading scopes. The [failure log](../experiments/i199_foulkes_structured/reading-and-failures.md) records retrieval limits and mathematical failures. Partial records were written early and replaced as the work developed.

Only the authorized I199 paths were written. No child agents, research code, parameter scans, numerical tests, certificate replay, snapshots, seals, staging, commits, or publication were used. I200/I201, I31, ancestor files, indexes, and unrelated historical files were not edited. The auxiliary lemmas are paid reductions and diagnostics, not a ninth nomination. Both independent acceptance gates remain with the parent.
