# T004Q63 — smooth affine quartic rational solvability

Status at scope freeze: unresolved research target, no nominee and no proof claim.

Frozen UTC: 2026-10-18T19:00:08.312367+00:00.

The full target is that there is no algorithm which, on every input nonconstant integral polynomial F in N variables, where N is part of the input, of total degree at most four and with Spec Q[X_1,...,X_N]/(F) smooth and geometrically integral over Q, decides whether F has a rational zero. The algorithm is required to halt and answer correctly on every promised input. No bound is imposed on N or coefficient height. The promise concerns the entire affine hypersurface, not just the rational smooth locus; projective smoothness is not required. No higher-degree, complete-intersection, singular-point-existence, or fixed-input subcase replaces this target.

Source004, October6 and September24, consequences Corollary thm:degree-normal-form, supplies Turing degree0′ for unrestricted quartics and presented sums of quadratic squares. The source is stipulated at the fixed pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. It does not assert smoothness of the quartic normal form. No many-one completeness of H10(Q) is assumed.

Chronology: before this freeze, exploratory degree12 smoothing and two failure mechanisms were derived: square-sum circuit compression is singular at its rational zeros, and a degree4 aggregate-linear auxiliary guard has no evident way to retain arithmetic rigidity and smoothness. Poonen's actual Lemma4.1 was then read and the degree12 route declined as technical. This freeze precedes unified proof-attempt assembly; it does not pretend to precede those exploratory calculations. No feasible full proof has been identified.

Original prose: Myeongjin Kang, CC BY4.0.
