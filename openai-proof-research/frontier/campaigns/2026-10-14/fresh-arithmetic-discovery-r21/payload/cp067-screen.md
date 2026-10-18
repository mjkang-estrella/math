# Sevenfold Campana–Peternell screen: unchanged full target, unresolved

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. No nomination or count.

The investigated target T0677 is: every smooth connected complex projective Fano variety X of complex dimension seven with nef holomorphic tangent bundle is isomorphic to G/P for a connected semisimple complex algebraic group G and a parabolic subgroup P. There is no Picard-number, index, pseudoindex, polarization-degree, deformation or VMRT restriction. This is a full-dimensional instance of the natural classification problem, not a claim about arbitrary dimension. No completed-candidate freeze is claimed. The target remains unproved and unrefuted here.

## Source and primary operations

Pinned family067, Theorem thm:main, proves dimension six. All mathematical sections and its exact certificate code were read. Its rho>1 branch invokes Kanemitsu 1505.02952v1, Theorem0.2 (rho>n−5). Its rho=1 branch leaves pseudoindices d=4,5. For d=4 it applies the dimension-independent factorization in Kanemitsu 1503.04579v1, Theorem3.3 and Proposition4.1, then uses Betti numbers and an odd-quadric characteristic number. For d=5, a rank-three evaluation tangent bundle E, the P1-fibration involution, fixed-part theory and relative GRR give a specific weight-nine matrix. Projection formula supplies bilinear product constraints; cubic prolongation and an exact finite certificate yield 32−20u+3u²=0. A separate nondegeneracy lemma, sectional genus, minimal-degree classification and VMRT recognition finish the proof. The matrix and geometric recognition are both dimension-specific.

The complete mathematical text of Kanemitsu 1503.04579v1 and 1505.02952v1 and Watanabe 1904.10185v1 was read. Kanemitsu's latter paper does not assert that knowing CP in dimension n−1 automatically proves all rho>1 cases in dimension n. Its lower-dimensional treatment classifies CP projective bundles by their slopes, and its final sixfold rho=2 case depends on those classifications. Watanabe's Theorem1.2 concerns **index** n−2 (coindex three), not pseudoindex n−2. Its sevenfold spinor-section exclusion first identifies the VMRT with V5 from the specified projective embedding, then transports its closed PGL2 orbit using second fundamental forms to create two P1-bundles. Neither the embedding nor index equality follows just from d=5. These are actual restrictions, not terminology differences.

Known reductions leave rho=2, and rho=1 with d=4,5,6, as obligations for T0677. The source/primary elementary exclusions of d=2,3 and large pseudoindex continue to apply; rho>=3 satisfies Kanemitsu's stated inequality. Merely classifying any one remaining branch would not prove T0677.

## Exact failure of the d=4 extension

The factorization branch has g:W→X a P1-fibration and q:W→Y with fibres P2,Q3 or K(G2). Here dim W=8. The source's relative-degree argument still gives −K_f·C=−K_g·f(C)=−1. Put h=g*(-K_X/4), c=c1(T_g), z=(h+c)/2. Then z is pulled back from Y, the g-involution fixes h and sends z to h−z, and it negates top integrals.

For P2 fibres, the sixfold contradiction from Hard Lefschetz no longer follows. With t recording cohomological degree two, the formal profiles

    P_X(t)=1+t+2t²+2t³+2t⁴+2t⁵+t⁶+t⁷,
    P_Y(t)=1+t+t²+2t³+t⁴+t⁵+t⁶

satisfy (1+t)P_X=(1+t+t²)P_Y. Both are palindromic, start with b0=b2=1, and increase weakly to the middle. Thus they pass precisely the Poincaré-duality and Hard-Lefschetz dimension inequalities used in the source argument. They are not asserted to arise from the required varieties or cohomology rings.

For Q3 fibres, dim Y=5. Write m_i=∫_W h^(8−i) z^i. Then m0=m6=m7=m8=0 and m1>0. The involution gives, for each i,

    Σ_{j=0}^i (−1)^j binom(i,j)m_j = −m_i.

The equations i=2,4,6,8 yield

    (m1,m2,m3,m4,m5)=(14,14,9,4,1)m5,  m5>0.

As in the source, write −K_q=3h−λz. Integrality of this divisor tested on a g-fibre implies λ∈Z. The odd-quadric orthogonal lift gives q*((−K_q)^4)=0. Intersecting with z^4 gives 81m4−108λm5=0, hence λ=3. This is compatible with integrality; in dimension six the identical step gave the contradictory 9/4.

The higher odd-Segre vanishings do not immediately repair this: with ζ=h−z, ∫ζ^4z^4=∫ζ^6z²=∫ζ^8=0 for the displayed moments. Every nonnegative mixed-intersection and adjacent log-concavity test also passes. The volume polynomial is

    ∫(a h+b z)^8 = 56m5 a³ b (a+b)³(2a+b).

These are exact algebraic consistency witnesses for these selected necessary equations, not a realization of a quadric bundle, a solution of all characteristic-class constraints, or a counterexample to T0677. The K(G2)-fibre branch has dimY=3; imposing m4=m5=...=0 in the same equations forces m1=0, so that particular branch is eliminated by the existing mechanism. This restricted elimination is technical support only.

The unpaid d=4 step is to exclude the P2 and Q3 factorization diagrams using more than the displayed Betti/moment conditions. The auxiliary W and Y are not asserted to have nef tangent bundles, so applying the lower-dimensional CP theorem to Y without proving that hypothesis is not valid.

## The d=5 equations and nondegeneracy both change

Even a known homogeneous sevenfold prevents reuse of the sixfold quadratic. For IG(2,6), a line direction at an isotropic two-plane can be written (a⊗b,c a²) in (A*⊗B)⊕Sym²A*, with dimA=dimB=2. Its VMRT is the smooth scroll P(O(1)⊕O(1)⊕O(2)) over P1 embedded by its tautological line bundle L in P6. One can see this directly from the coordinates

    (s b0,s b1,t b0,t b1,c s²,c st,c t²).

The projective-bundle formula gives L³=4 and c1(T_F)=3L−2f, where f is a fibre divisor and ∫fL²=1. Consequently u=(c1(T_F)L²)/L³=5/2, and 32−20u+3u²=3/4≠0. This does not dispute the sixfold source theorem. A correct sevenfold matrix must allow this legitimate homogeneous model. The rank-three GRR setup continues, but weight ten, base generators through x7, new dimension vanishings and a new elimination are required. No sevenfold elimination certificate was obtained.

There is a separate geometric obstruction even if an appropriate numerical relation is found. The source nondegeneracy lemma uses a proper span W of dimension at most five and a four-dimensional isotropic affine tangent space. In sevenfold dimension a proper W can have dimension six. In W=C^4⊕C² take

    ω=dx0∧dx3−3dx1∧dx2,
    Z={ (λ,λt,λt²,λt³,a,b) : λ,t,a,b∈C } with its closure.

The cone Z is irreducible, spans W, has dimension four, and its smooth tangent spaces on the dense λ≠0 chart are isotropic for the nonzero rank-four form ω. Indeed, for A(t)=(1,t,t²,t³), ω(A,A')=0; the last two coordinate directions are the kernel. This is the cone with a projective line vertex over the twisted cubic. Thus the source's dimension-only bivector-spanning inference is false at this dimension. It is NOT asserted to be a CP VMRT: global minimal-curve geometry may exclude it. The missing hypothesis is an argument excluding such degenerate tangent images in the actual family, not generic positivity or a longer scalar computation.

## The d=6 interface

Here E=T_e has rank four and the evaluation fibre has dimension four. Relative GRR must include Ω² in addition to O and Ω¹: duality pairs p with 4−p, so p=2 is an independent middle term. The source rank-three two-row-family computation is not this problem.

The source's explicit degree-one twisting line bundle uses d=5. That particular formula cannot simply be reused for even d, but rational shifted descent is not a fundamental obstruction. Both Sym²E⊗T_π and Λ²E⊗T_π restrict trivially to every π-fibre, so they descend by base change. Their difference has Chern character Σ_i exp(2e_i+c), where e_i are E's formal roots and c=c1(T_π). Hence the power sums in e_i+c/2 descend rationally. Since h−c/2=ℓ/2 descends, all symmetric polynomials in e_i+h descend rationally as well. This supplies a standard technical interface, not the missing rank-four elimination or VMRT classification. No partial even-pseudoindex theorem is nominated.

The already accepted family063/AGM063 result is prior work. It is not re-nominated here, and this packet does not infer a substantial contribution from a dimension increment alone. No use of that accepted theorem resolves the missing diagram or VMRT hypotheses above.

## Status and contribution limit

T0677 is unchanged and unresolved. Exact diagnostics certify only the stated finite polynomial and rational identities. No existence theorem for the formal profiles, no arbitrary-sevenfold classification, no new substantial theorem and no count are claimed. The concrete continuation would require new geometric constraints on the d=4 diagrams, a dimension-seven rank-three elimination plus nondegeneracy/recognition for d=5, a rank-four GRR/classification argument for d=6, and the rho=2 projective-bundle/other-contraction cases. Routine source transfers and the diagnostic obstructions are not substitutes.
