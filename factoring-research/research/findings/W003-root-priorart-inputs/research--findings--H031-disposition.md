# H031 — Adjacent-rotation trial: scoped acceptance and closure

2026-10-08. **ACCEPT the repaired finite trial, algebra and per-trial upper bound;
REJECT promotion to a new COMPLETE factoring improvement.**
Verified COMPLETE factoring complexity improvement: **NONE**.

The coordinator consumed all 702 independent-review lines. Before edits,
24 frozen records, 38 owned-artifact records and all 39 delivery entries verified.
Review SHA-256:
94f51518b1e9b13ffc99096ee529f453d47d3381872dec5bc13bc010f74e64d7.
Review provenance SHA-256:
4f0b1420bfae00639d4572c8010fce3e2d60d6fbe365a4b349a955040773ee42.
The identical original 553-line submission remains preserved at
d5a3b605756de25926bb34be6bb82bf2144a8de4b4aeae04b5623b1fa37abffb.
Original intakes, sources and manifests retain their historical identities.

## Accepted after completion

The input-only adjacent rotations, finite small-input branch, positive relation
stream, good-prime labels, separate ideal blocks and uniform joint-kernel
sampling are valid finite constructions on the promised distinct Blum
semiprimes. At most two exact field roots are attempted. Nonsquares fail;
ideal parity alone never supplies a root.

For a fixed valid retained space V_t, its actual-square subspace S_t has
codimension c_t. The productive Jacobi character chi_t is well defined on
S_t and is independent of field-root signs. Conditional useful probability
is 2^(-c_t-1) if chi_t is nontrivial, otherwise zero. The complete trial law
includes early gcd successes and the actual weights of all failed pairs.
It proves no favorable c_t, nontrivial character or positive uniform mass.

The accepted conservative pathwise work is O(B^3 poly(n)), equivalently the
upper envelope L_N[1/3,3+o(1)]. Field-product coefficients may have
O((R_i+1)poly(n)) bits, and both root calls pay for that size. For iid cold
trials with sigma_N>0 the expected work is E[T_trial]/sigma_N. No lower bound
on sigma_N is proved, so there is no successful factoring-time bound.

## Adopted review completions

1. Reduction occurs on Z[alpha][f'(alpha)^(-1)], with the derivative image a
   verified unit. Root-output rational denominators are canceled in the exact
   field before reduction; arbitrary field fractions or discriminant inverses
   are never assumed valid modulo N. The denominator-cleared overlap identity
   supplies the character proof.
2. Both defining polynomials are factored first. Reducible-factor gcds are
   inspected in fixed field/factor order before declaring unproductive
   reducibility a failure. Derivative tests and subsequent processing also
   have fixed order. A_N refers to this actual execution.
3. The current report includes Lenstra's variable dictionary, arithmetic and
   operand-width bounds, numerical auxiliary-prime size, root denominators,
   sequential access and empty-data control costs. Work is an upper bound,
   not an equality for each trial. No polynomial-in-n field input is assumed.
4. The productive-character issue is analogous to LV's for a different law.
   Neither its conjecture nor collection/success theorem transfers to this
   rotation pair and capped prefix. Global rational reconstruction is shared
   prior art, not a newly found parity mechanism.
5. Status is a reviewed finite on-paper construction. No implementation,
   experiment, Lean proof or machine refinement was executed.

The coordinator followed the cleared overlap equation, the fixed-order
probability partition and the displayed root-cost substitution before adopting
these completions. No equations for the success law or leading trial envelope
needed algebraic correction. The original submission is unchanged.

## Remaining positive-result obligations

A new result still needs a uniform useful-mass bound for the actual pair law,
including validation, smoothness/rejections, retained supply/rank, actual-square
codimension and productive-character nontriviality. A larger ambient set or
expected raw row count does not suffice. A matched improved cost would also
need an explicitly paid faster pipeline. The restricted semiprime promise
does not establish all-composite success or full general factoring.

This closure does not assert sigma_N=0 or impossibility for adjacent rotations,
other coupled fields or factoring. Reopening requires a new arithmetic
mechanism proving the missing mass, or a materially changed costed algorithm.
No experiment or replacement question is selected by this report.
Both H031 task handles are completed, with no pending runs.

[Corrected report](H031-coupled-field-roots.md),
[original submission](H031-submitted-draft.md),
[independent review](H031-independent-review.md),
[construction intake](H031-construction-intake.md).
