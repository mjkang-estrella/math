# Family 068: the anticanonical lc-complement obstruction

Author: Myeongjin Kang. No affiliation. 2026-10-16.

Status: **UNFROZEN_FULL_TARGET_OBSTRUCTION**. No candidate is nominated, no acceptance is claimed, and the campaign count is unchanged. This is an attempted stronger deduction from the stipulated family 068 source, not a challenge to its truth. The source revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The full target investigated was:

> For every smooth connected projective complex variety X whose anticanonical bundle L = −K_X admits a smooth Hermitian metric with semipositive curvature, there exist an integer m > 0 and an effective integral divisor D in |mL| such that (X,D/m) is log canonical.

Thus X would be of log Calabi–Yau type. The quantifiers are unrestricted in dimension, and no semiampleness, bigness, rational connectedness, or Euler-characteristic premise is added. A proof for surfaces, a conditional bridge, or numerical effectivity would not settle this target. I have no proof or counterexample under these full hypotheses and make no claim that its literature status is settled.

## Exact deduction still needed

Write A_X(v) for the log discrepancy of a prime divisor over X, with its normalized divisorial valuation v. For each nonempty |mL| let b_m be its base ideal. The target is equivalent to finding one such m for which

    v(b_m) ≤ m A_X(v)  for every divisorial v over X.                 (1)

Necessity follows from v(b_m) ≤ v(D). For sufficiency, resolve b_m, writing its fixed divisor as F and the transformed system as a free system. Condition (1) says (Y,F/m − K_{Y/X}) is sub-log-canonical. Choose a general member of the free system transverse to its simple-normal-crossing boundary. Its coefficient 1/m is at most one, so adding that member divided by m preserves sub-log-canonicity. Pushing down gives the required D/m. This familiar base-ideal reduction is bookkeeping, not a proposed contribution.

Neither a section nor separate choices of sections for individual valuations establish (1). Even bounds on asymptotic orders need a finite-degree attainment argument with all discrepancy inequalities retained.

The rigid case makes the missing step especially explicit. Suppose κ(X,L)=0 and take D₀ ∈ |m₀L|. Every nonempty plurisection space is one-dimensional: otherwise a ratio of two independent sections would give positive Iitaka dimension. If E ∈ |mL|, the sections defining m₀E and mD₀ are proportional in |mm₀L|, hence m₀E=mD₀. Therefore B=D₀/m₀ is the unique effective rational divisor rationally linearly equivalent to L. The full target in this case is exactly

    v(B) ≤ A_X(v)  for every divisorial v.                          (2)

Taking products or higher powers cannot improve B. Smoothness of a metric on L does not identify it with the singular divisor metric defined by B. No estimate proving (2) has been extracted here.

## Why the strongest inspected companion does not supply the estimate

The exact-orders companion proves attainment of **zero** order. With α a smooth semipositive curvature form of maximum rank ν and G ample, its null functional for ν<n is

    ℓ(Q)=Q·L^ν·G^(n−ν−1).

Its input is effective N_j ∼ m_jL+M, m_j→∞, with ℓ(N_j)=0 and v(N_j)/m_j→0 for the selected valuation. Its conclusion is one effective rational N∼Q L with v(N)=0. I read its actual endpoint, null-field, and exact-attainment proofs, not merely the headline. They construct a null-polar function field, obtain a correction ring on its base, select a generator for one valuation, and remove the exceptional correction before using nonnegativity.

For a fixed ample M, one instead has ℓ(N_j)=ℓ(M)>0 whenever ν<n. Indeed, M·L^ν·G^(n−ν−1)>0: the semipositive form α has rank ν on a nonempty ordinary open set and its wedge with the ample forms has positive integral there. This also holds at ν=0. Consequently, ordinary ample-twisted metric approximation does not satisfy the exact theorem's null-face hypothesis. An error that becomes small after division by m_j is not an error of exactly zero null intersection.

In the rigid case, the readily available untwisted sequence consists of multiples of B. At a valuation with v(B)>0 its normalized order stays positive; the zero-order theorem cannot even be invoked. In particular it supplies no comparison of that positive number with A_X(v). The ν=n big-and-nef case is already semiample by the standard basepoint-free theorem and has complements by Bertini; it is not the unpaid case.

The controlled-cone companion also does not repair this step. Its finite-cone proof retains linearized divisor **classes**; the selected monomial need not have the original zero divisor. Its generators need not be controlled. The signed klt boundaries used to produce its adjoint ring live on an auxiliary base, and the argument only removes supported corrections after pullback and pushforward. Neither a class-cone inclusion nor that removal supplies the discrepancy inequalities for the returned anticanonical divisor on X. I read the proof through the construction of this cone (lines 1–400 of the retained file); later invariant applications were not needed or read in this pass.

The other six introductions explicitly cover scalar nonvanishing, permitted poles, bounded-metric klt nonvanishing, invariant index, shifted-character conversion, volume metrics, and rank-preserving contractions. Those outputs were checked before selecting this target. None of the inspected statements asserts (1) or (2). This does not claim that all bodies of all seven papers have been exhausted.

## Primary comparison and controls

[Chen–Filip–Sun–Tosatti–Zhang, arXiv:2609.26716v1](https://arxiv.org/html/2609.26716v1), Theorem 1.3 and its actual proof in §6.2, already settle the surface case by classification. Semiampleness gives a general divided member; the remaining cases have either a smooth anticanonical curve, a reduced nodal cycle, or the two disjoint sections of a split degree-zero ruled surface. Each gives an lc rational anticanonical divisor. Their proof excludes the nonsplit elliptic ruled example via failure of Hermitian semipositivity. Thus a surface-only statement here would be a routine consequence of their work, not a discovery. Their rational examples also show why a semiampleness shortcut would change the target.

[Shokurov, Complements on surfaces](https://webhomes.maths.ed.ac.uk/cheltsov/shokurov/pdf/complement1.pdf), Example 1.1, gives a concrete failure under **nefness alone**: on the ruled surface of the nonsplit extension of O by O over an elliptic curve, −K∼2E and E is the only curve on its numerical ray. Hence all anticanonical plurisections give B=2E, violating (2) at E since A_X(E)=1. This is a useful check on the proposed inference from positivity to discrepancy control, but is not a counterexample to the smooth-semipositivity target. The preceding primary classification explicitly rules that example out.

The surface comparison is a primary-proof comparison, not a new proof of that classification. No other search snippet is used as a theorem premise. In particular, an inaccessible 2023 PDF and third-party generated digests are not evidence for this checkpoint.

## Result of the attempt

The unpaid mechanism would have to turn the smooth anticanonical metric into **one finite-degree system satisfying all discrepancy bounds**, including the rigid case (2). The exact null-face order theorem and the controlled-class cone do not provide it by the tested arguments. No route closing that gap has been found. The target stays unfrozen; the recorded reductions and rejected shortcuts must not be submitted or counted as an independent acceptance.
