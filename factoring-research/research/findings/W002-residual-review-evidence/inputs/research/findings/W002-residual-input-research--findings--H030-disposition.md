# H030 — Exact polynomial-block realization closed after review

2026-10-08. **ACCEPT the scoped finite specification and representation
obstruction; REJECT this realization as a sub-1/5 RootProduct construction.**
Verified COMPLETE factoring complexity improvement: **NONE**.

The coordinator consumed all 615 lines of the independent review and its source
notes. All 36 frozen review inputs and 41 delivery entries verified before edits.
Review SHA-256:
7601b524bbfa347576432099db173b18d0ad5a476fccc3c7bbfbaf01d9bc61a4.
The identical 482-line submitted snapshot remains unchanged at
f66360ee379188f50b83fb1f11fff43536aa3c2beb18c6a05118d4986b864581.
Original manifests preserve those historical report bytes. No shared solver,
Lean source, finite experiment, benchmark or package changed.

## Accepted result

The Newton-cubic constructor, sufficient rational Bernstein certificates,
denominator clearing before reduction, and monic product/remainder routine
are exact on the unchanged all-M, all-modulus, all-interval interface. Its
setup plus worst-case query cost is M^(1/3)*poly(log M), with retained and live
scratch storage charged. Partial endpoints, failed certificates, repeated
leaves, composite nondivisor moduli and sequential record scans are included.

For U=M^(1/3) and J=[ceil(3U/4),floor(U)], the integer sequence
c(k)=ceil(2sqrt(Mk)) has second differences in {-2,-1,0,1}. A rational
degree-D polynomial agreeing on L consecutive positions in J satisfies
L<=max(8,4D-6). Hence the specified constructor must write at least |J|/8
terminal records, and costs Omega(M^(1/3)) even if its other work were free.
This closes the selected exact consecutive-cubic representation.

With e explicit exceptions, L<=4D+9e+8. Summing with actual degrees delta_b
gives W=sum_b(delta_b+1)+E_all>=|J|/9>=U/72. This implies an output-cost lower
bound only when each block separately materializes its dense coefficient list
and its exceptions. It does not count an unallocated declared degree or shared
coefficient arrays as if they were separate output.

## Adopted clarifications

1. V_short counts weighted scalar (k,t) pairs: sum_(short b) w_(j(b)) L'_b.
2. The constructor's lower bound comes from nonempty records actually written.
   O(n)-bit field upper bounds alone give no Omega(n)-per-field lower bound.
3. The growing-degree consequence uses actual degrees or genuinely allocated
   padded lists, with separate dense materialization and listed exceptions.

The coordinator checked and adopted these changes in the current report.
They clarify costs and notation; no algebraic repair was required. The review's
sequential processing schedule and monic reversal proof substantiate the
existing upper envelope without changing the mathematical interface.

## Scope and next action

No lower bound on RootProduct or factoring is proved. Implicit floor-bearing
expressions, sparse circuits, nonconsecutive blocks, implicit exceptions,
shared computations, direct pair products and modular-only generation remain
outside the obstruction. Reopening requires a concrete different algorithm
with all construction and query work paid, not a larger sweep of this one.

The known H029 cover/recovery reduction remains accepted with its fast product
missing. H031 has a separate live review. The parent is checking the previously
open batch-ECM branch for a distinct computation; no ECM candidate or experiment
is yet selected. H030's two task handles are complete, with no pending runs.

[Corrected report](H030-root-product-blocks.md),
[original submission](H030-submitted-draft.md),
[independent review](H030-independent-review.md),
[coordinator intake](H030-intake.md).
