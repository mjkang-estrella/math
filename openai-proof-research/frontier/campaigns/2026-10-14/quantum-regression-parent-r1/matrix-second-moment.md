# Matrix-valued exact projection: second moment and the higher-moment gap

Myeongjin Kang; no affiliation. Original prose CC BY 4.0, accompanying code MIT.
Parent author assistance, 2026-10-18. No target freeze, independent gate,
substantiality claim or nomination.

The structural author is testing a quantum-memory extension of the full
precision/memory tradeoff in family140. The required block estimate has moment
order proportional to the signal dimension. This note proves only a second
moment and identifies why the scalar iterative argument does not immediately
give those higher moments. It neither proves nor refutes the full extension.

## A finite-dimensional operator-valued projection estimate

Let Ω be a finite positive-semidefinite D×D complex matrix-valued Borel measure
on R^d, supported in B(z,R), R>0. Assume, in Loewner order,

    Ω(B(x,t)) ≼ H t^β I_D       (x∈R^d, t>0),

where H>0 and β>m≥1, with m an integer. Let γ_m be standard Gaussian measure
on m×d matrices and λ_m(dA,dy)=γ_m(dA)dy. Push γ_m(dA)Ω(ds) forward under
(A,s)↦(A,As), entrywise. Then the resulting positive matrix measure has a
jointly Borel positive density F with respect to λ_m, supported in

    E={ (A,y): y∈Az+A B(0,R) },

and

    ∫ Tr(F(A,y)^2) dλ_m
       ≤ D (2π)^(-m/2) [1+m/(β−m)] H² R^(2β−m).        (1)

The exponent β may be real. No commutation hypothesis on Ω is imposed.

Proof. Put ν=Tr Ω and write dΩ=W dν. In finite dimension the Radon–Nikodym
matrix W is positive and Tr W=1 ν-almost everywhere. A null ν-measure is
harmless. Since β>0, ν has no atoms. For every s, the scalar layer-cake identity,
tested against every fixed vector and then interpreted in Loewner order, gives

    ∫ |s−t|^(-m) dΩ(t)
      ≼ R^(-m) Ω(R^d)
          + m∫_0^R u^(-m−1) Ω(B(s,u)) du
      ≼ [1+m/(β−m)] H R^(β−m) I_D.                    (2)

Here Ω(R^d)≼HR^β I_D follows from the support ball. The first line is an
upper bound because the truncated layer-cake expression is R^(-m) when
|s−t|>R. The integral at zero converges because β>m. Using balls centered
directly at s avoids the unnecessary 2^β covering factor in the general
affine-plane estimate.

Let φ_δ be the N(0,δ²I_m) density and set

    F_δ(A,y)=∫ φ_δ(y−As) W(s)dν(s).

For positive matrices U,V, Tr(UV)≥0. Expanding the square therefore permits
Tonelli, and the source Gaussian difference identity with two points gives

    ∫Tr(F_δ²)dλ_m
      = (2π)^(-m/2) ∬ (|s−t|²+2δ²)^(-m/2)
                              Tr(W(s)W(t))dν(s)dν(t)
      ≤ (2π)^(-m/2) ∫Tr[W(s)∫|s−t|^(-m)dΩ(t)]dν(s).

Apply (2) against W(s)≥0. The last bound is at most

    (2π)^(-m/2)[1+m/(β−m)]HR^(β−m)Tr Ω(R^d),

which is the right side of (1). All integrals are finite; the diagonal is
ν⊗ν-null.

To remove smoothing, use weak compactness in the Hilbert space
L²(λ_m;S²_D), where S²_D is the Hilbert–Schmidt matrix space. Along a sequence
δ↓0, a weak limit F has no larger norm. Against a compactly supported continuous
matrix test, the smoothed pushforwards converge to the exact pushforward:
entrywise bounded convergence applies, with finite ν as a dominating measure.
The weak L² limit represents the same measure. Its positivity follows by
testing nonnegative scalar compact tests and fixed vectors in a countable dense
subset of C^D; it is supported in the closed Borel set E because the exact
pushforward is. Choose a Borel representative and set it to zero off E.
This proves the statement and (1).

## What this pays in a quantum block

For a future success effect H_future(s), assume the operator local bound
∫_{B(z,r)}H_future(s)dσ(s)≼(R_0 r)^a I_D. Apply (1) to its restriction to
B(z,r), converting sphere-centered to ambient balls as in the source.
The resulting bound has the form

    ||F||_{L²(S²_D)} ≤ sqrt(D) exp(Cd) R_0^a r^(a−m/2),

provided a>m and the source's proportional parameter margins hold.
For an arbitrary measurable routed quantum state ρ(A,y)≥0 with Tr ρ≤1,
Tr(ρ²)≤1. Hilbert–Schmidt Cauchy–Schwarz and the source projected-ellipsoid
volume estimate give

    ∫_E Tr(Fρ)dλ_m
      ≤ sqrt(D) exp(Cd) R_0^a r^(a−m/2) λ_m(E)^(1/2)
      ≤ sqrt(D) exp(Cd) (R_0 r)^a.                    (3)

This concerns a fixed incoming state and one continuation register; a full
stream with stopping instruments requires its own channel bookkeeping.
Formula (3) contributes (log D)/(2a) to the logarithm of the propagated scale.
For D=2^M and a proportional to d, this is O(M/d), whereas the intended
full source-scale extension requires O(M/d²). The second moment does not
provide that extension. It is not offered as a weakened substitute.

## Two exact failures of naive higher-moment iteration

The scalar source expands a p-th moment, keeps a nonnegative integrand and
integrates inverse affine distances successively. With noncommuting matrices,
the corresponding factor Tr(W_1⋯W_p) need not be nonnegative. Already the
rank-one orthogonal projections

    A=[[1,0],[0,0]], B=(1/2)[[1,1],[1,1]],
    C=(1/5)[[1,−2],[−2,4]]

satisfy Tr(ABC)=−1/10. Thus replacing a nonnegative Gaussian kernel by an upper
bound inside the trace-product expansion is not justified term by term.

Even obtaining an integrated last factor 0≼T≼I is insufficient for the next
scalar-style step: with the same A,B and

    T=(1/5)[[4,2],[2,1]],

one has Tr(ABT)=3/5 > Tr(AB)=1/2. The map X↦Tr(ABX) is not a positive
functional. The source's scalar successive integration therefore cannot be
copied with Loewner inequalities without a new argument.

These examples do not disprove an operator-valued higher-moment estimate.
Symmetrized trace inequalities, completely positive factorizations or other
methods might establish one. No such estimate is proved here. The companion
and primary quantum-learning comparisons remain the structural author's task.

## Source and reading scope

Pinned source: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/`.
The parent read `build/sections/blocks.tex` and `local-mass.tex` fully,
`projection.tex` lines1–345 and350–418 (including the full density theorem and proof,
Gaussian difference identity, compact-test passage and projected-volume estimate), and `streaming.tex`
lines1–105. These actual scalar operations are credited antecedents. The note's
second-moment transfer is routine author support, not a substantial result.
The parent has not read all six companions or the primary quantum-memory
literature in this calculation and makes no priority assertion. Source byte
identities against the canonical complete tree are recorded separately.

The structural author read this note in full and checked the operator layer
cake, weak-L² passage and rational examples, reporting no correction. This is
author collaboration, not an independent gate.
