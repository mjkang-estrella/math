# I331 — proofs and exact unresolved estimate

## Scope and conventions

Throughout, Ω and Λ are bounded nonempty connected open subsets of R³. The given f:Ω→Λ is a homeomorphism, f∈W¹,²(Ω;R³), and h=f⁻¹∈W¹,²(Λ;R³). Matrix norms are Frobenius norms. Reflection allows an orientation-preserving convention; formulas with absolute determinants work in either orientation. Smoothness is on the open domains. All limits and energies below are global unless explicitly localized.

The family-368 statements at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Their one-sided convergence assertions are not strengthened by assumption. The new arguments below are validated independently relative to the identified source interfaces.

## 1. The proposed rank-one obstruction cannot occur in the input class

Primary dependency: [Csörnyei–Hencl–Malý, author preprint](https://www2.karlin.mff.cuni.cz/kma-preprints/2007-pap/2007-252.pdf), Theorem 4.5. Its hypothesis is a W¹,n−1_loc homeomorphism whose inverse belongs to W¹,¹_loc; its conclusion is finite distortion of the inverse. Here finite distortion means vanishing differential on the zero-Jacobian set, after orientation normalization.

Apply it first to f, and then to h. The second application is valid because h∈W¹,²_loc and f∈W¹,¹_loc. Thus

    Df=0 a.e. on {Jf=0},    Dh=0 a.e. on {Jh=0}.                 (1)

No global N or N⁻¹ property is inferred. The theorem’s coarea/ACL proof, read in the primary source, is why an arbitrary higher-dimensional bi-W¹,¹ statement is insufficient here. In particular, a positive-measure zero-Jacobian set with nonzero rank-one Df cannot be the suggested counterexample under the present hypotheses.

Independent matrix audit: if an invertible A has singular values s₁≥s₂≥s₃>0, then

    Φ(A):=|cof A|²/|det A|
         =s₁(s₂/s₃+s₃/s₂)+s₂s₃/s₁ ≥ 2s₁.                 (2)

This follows by summing the squares of s₁s₂,s₁s₃,s₂s₃ and applying t+t⁻¹≥2. The bound is correct, but (1) eliminates the proposed limiting stratum. Matrix algebra alone says nothing about image measures of exceptional sets.

## 2. Energy transport without assuming global Lusin N

Extend Φ by Φ(0)=0; matrices of intermediate rank are irrelevant almost everywhere by (1). For every Borel A⊂Λ,

    ∫A |Dh(y)|²dy = ∫f⁻¹(A) Φ(Df(x))dx.                       (3)

In particular Φ(Df)∈L¹(Ω). This is a deduction for the stipulated bi-W¹,² input, not a formal application of a global change-of-variables formula.

Proof. Sobolev approximate differentiability and the countable Lipschitz decomposition give Borel Lipschitz pieces covering Ω up to a null set N_f. These standard area-formula ingredients are explicitly recalled in CHM Section 2. On each piece weak gradients equal those of a Lipschitz extension a.e. Refine the full-rank subset into countably many bi-Lipschitz pieces R_k as follows. At differentiability points of the extension with invertible derivative, choose a nearby rational invertible matrix B and a small ε<σ_min(B)/4. Partition by a uniform radius for the differentiability remainder and by small cubes. For two retained points x,z in the same cube,

    |F(z)−F(x)−B(z−x)| ≤ (|DF(x)−B|+ε)|z−x|
                       < σ_min(B)|z−x|/2.

This gives a lower Lipschitz bound; the original extension supplies the upper bound. Countably many choices exhaust the full-rank points up to null sets. Make R_k disjoint. On the remaining nonexceptional set Z_f, (1) gives Df=0. Area formula on the Lipschitz pieces yields |f(Z_f)|=0, even if |Z_f|>0.

Perform the corresponding decomposition for h: the full-rank target points are covered up to a null set by bi-Lipschitz pieces T_l, and Dh=0 on the remaining nonexceptional points. For each l, h(T_l∩f(N_f))⊂N_f. The inverse of h|T_l is Lipschitz, so |T_l∩f(N_f)|=0. Hence Dh=0 a.e. on f(N_f), even if that image has positive measure. Together with the null image f(Z_f), this proves that Λ\f(∪R_k) carries no inverse derivative energy.

On f(R_k), derivatives of the Lipschitz extensions obey

    Dh(f(x))=(Df(x))⁻¹

for a.e. x∈R_k. To verify the relation, discard the inverse extension’s nondifferentiability set in f(R_k); it pulls back to a null set by bi-Lipschitzness. The composition equals the identity on R_k, so locality of derivatives at density points and the Lipschitz chain rule give the displayed relation. Apply the injective area formula **on R_k only** to the nonnegative Borel integrand |Dh|²1_A and sum. The result is (3), because |A⁻¹|²|det A|=Φ(A). Monotone convergence handles unbounded integrands. Null exceptional images have not been silently discarded: their energy was proved zero.

The same proof gives ∫Λ|Dh|=∫Ω|cof Df|. This identity is a statement about energy, not strong inverse convergence for an arbitrary sequence. In particular, strict convergence of BV variation would not itself prove strong convergence of gradients.

## 3. A smooth exact-target sequence with divergent inverse energy

This explicitly disproves the implication “strong forward W¹,² convergence supplies uniform inverse W¹,² control,” even with uniform convergence in both directions. It is **not a counterexample to the approximation target**: the limiting identity has the constant identity approximating sequence.

Let Q=(0,1)³. Fix a smooth bump ψ:R→[0,1], supported in (−1/2,1/2), equal to 1 on [−1/4,1/4]. For 0<δ<1/4 put

    ηδ(t)=ψ((t−1/2)/δ),   εδ=δ²,
    mδ=∫₀¹ηδ,   cδ=1−(1−εδ)mδ,
    aδ(t)=[1−(1−εδ)ηδ(t)]/cδ,
    Hδ(t)=∫₀ᵗaδ(s)ds,
    gδ(x)=(Hδ(x₁),x₂,x₃).

Here cδ≥1−δ, aδ>0 and ∫₀¹aδ=1. Therefore gδ is a smooth diffeomorphism Q onto exactly Q, with smooth inverse. Each individual map and inverse belongs to W¹,². We have

    ∫₀¹|aδ−1|²=O(δ),    sup|Hδ−Id|≤∫₀¹|aδ−1|=O(δ).

Indeed, off a set of length δ the derivative differs from 1 by O(δ); on that set it is uniformly bounded. Thus gδ→Id strongly W¹,². Also sup|Hδ⁻¹−Id|≤sup|Hδ−Id|, so inverse values converge uniformly. However, ordinary smooth change of variables gives

    ∫Q|Dgδ⁻¹|² = 2+∫₀¹1/aδ(t)dt
                ≥ 2+(δ/2)cδ/δ² →∞.                       (4)

There is a plateau of length δ/2 where aδ=δ²/cδ. This calculation is symbolic and exact; no numerical scan was used. It also gives strong inverse W¹,¹ convergence for this particular sequence, since its only nonconstant derivative entry satisfies

    ∫₀¹ |(Hδ⁻¹)'(y)−1|dy = ∫₀¹|1−aδ(t)|dt →0.

No general forward-W¹,²/inverse-W¹,¹ continuity theorem is asserted here.

## 4. Why the operational collapse estimate is one-sided

The pinned low manuscript, 03-low-tools.tex, Lemma `lt:collapse`, uses the radial profile

    q(r)=(1−δ)r/α                         for 0≤r≤α,
         1−δ+δ(r−α)/(1−α)                 for α≤r≤1.

Its admissible ball model F(rω)=q(r)ω is a bi-Lipschitz self-homeomorphism fixing the boundary. Piecewise smoothness suffices for the following a.e. calculation. At radius r the singular values are q'(r),q(r)/r,q(r)/r, and hence

    Φ(DF)=q(r)²/[r²q'(r)]+2q'(r).

For any fixed 0<α<1/2, the outer-shell inverse energy is at least

    4π∫α¹ q(r)²/q'(r)dr
       ≥ 4π(1−δ)²(1−α)²/δ →∞.                            (5)

Meanwhile the forward energy is

    4π∫₀¹[(q')²r²+2q²]dr.

Its inner part is 4πα(1−δ)²; its outer part stays bounded as δ→0. This is precisely compatible with a subcritical forward collapse bound. The ball calculation is an analytic model of the same radial mechanism, not an assertion that the pinned cell is spherical. The general polyhedral proof likewise sends the radial slope to zero without an inverse-energy bound. Thus inserting an inverse budget into that proof requires a different quantitative argument, rather than smaller δ in the existing argument.

## 5. Labeled partial result: simultaneous smoothing of a fixed locally bi-Lipschitz input

Additional hypothesis for this section only: f is locally bi-Lipschitz on Ω. It still belongs globally to W¹,² and its inverse to W¹,². Then for every ε>0 there is a smooth onto diffeomorphism g:Ω→Λ with

    ||g−f||W¹,²(Ω)+||g⁻¹−h||W¹,²(Λ)<ε.                    (6)

Dependencies: the operational proof of pinned Proposition `sm:bilip-pl` in 02-smoothing.tex, including its finite libraries, protected good cubes, and resolution selection; then [Campbell–D’Onofrio–Vítek](https://arxiv.org/html/2507.02854), Theorem A with p=q=2. The extra inverse accounting below is a deduction, rather than part of the pinned proposition’s stated conclusion.

Proof of the additional accounting. In its coarse neighborhood U_P the pinned construction fixes a bi-Lipschitz bound K_P for f, selects good cubes by affine value and derivative tests of tolerance δ_P, and installs the affine interpolation L exactly on every good cube. All bad-cube replacements come from finitely many normalized PL embeddings on compact patches. Besides their recorded upper bound M_P, these embeddings have finite inverse-derivative bounds B_P: each of their finitely many full-dimensional affine pieces is nonsingular. Fix the maximum B_P before choosing mesh resolution. Uniform normalization by equal source/target scale does not change either bound. Take locally enlarged constants to cover interacting coarse neighbors.

On a good cube Q, both Df and DG have inverse operator norms bounded in terms of K_P. The estimate |DG−D A_Q|≤Cδ_P and the test ∫Q|Df−D A_Q|²≤δ_P²|Q| give

    ∫Q |(DG)⁻¹−(Df)⁻¹|² |det DG| ≤ C(K_P)δ_P²|Q|.        (7)

The matrix inequality used here is A⁻¹−B⁻¹=A⁻¹(B−A)B⁻¹. Choose δ_P at the beginning to make the sum of (7), as well as the forward good-cube costs, smaller than the allocated error. This precedes the selection of libraries.

To compare derivatives at the same target point, account also for

    Dh(G(x))−Dh(f(x)).                                    (8)

Choose value tolerances so G(Q) lies in f(U_P) for all relevant cubes. On a fixed coarse region approximate Dh in L² on a slightly larger compact target neighborhood by a continuous matrix field v. Change of variables for G bounds the pullback approximation error by B_P³||Dh−v||²L²; change of variables for f bounds the other by K_P³||Dh−v||²L². Multiplication by |det DG| costs at most a constant times M_P³. All constants are fixed now. First choose v to make these errors small, then shrink the mesh so uniform continuity of v and the fine value closeness make v(G(x))−v(f(x)) small. This proves smallness of the weighted integral of (8). The identity Dh(f(x))=(Df(x))⁻¹ holds a.e. here because both directions are locally Lipschitz.

On bad cubes with coarse index P, their G-images have volume at most C M_P³ times their source volume. On those images |DG⁻¹|≤B_P and |Dh|≤C K_P. Thus the inverse squared-gradient error is at most

    C M_P³(B_P+K_P)² |bad cubes with index P|.              (9)

Replace the pinned bad-volume requirement by one that pays for (9) and its forward counterpart. The bad volume still tends to zero uniformly under resolution refinement, by the same differentiability argument in the pinned proof; B_P and M_P are already fixed. Allocate summable local errors. This order avoids multiplying an old energy tail by a later, uncontrolled inverse constant. The resulting PL G is onto the same Λ and both global derivative errors are small.

Fine forward value control can enforce arbitrarily small inverse value error: prescribe |G(x)−f(x)| small enough that h(G(x)) lies within a prescribed tolerance of x. This follows from continuity of h at f(x) and positive continuous minorants. At y=G(x), G⁻¹(y)=x. Bounded domains then give small global L² value errors. Apply Theorem A to G and G⁻¹ with p=q=2, and use the triangle inequality. This proves (6), including global inverse membership and exact image. Repeating ε→0 gives a single simultaneous sequence in this stronger class.

Validation limits: the finite libraries argument concerns a **fixed locally bi-Lipschitz input**, whose local constants are available before refinement. It gives no uniform estimate when that input itself comes from the one-sided replacement of the general f. In particular it does not repair the inverse cost (5).

## 6. Exact sufficient criterion and remaining work

Suppose one constructs onto locally bi-Lipschitz H_j:Ω→Λ such that H_j→f strongly W¹,², H_j⁻¹→h in L², and

    limsup_j ∫Ω Φ(DH_j) ≤ ∫Λ |Dh|².                       (10)

Then the target follows. By ordinary local Lipschitz change of variables and exhaustion, ∫ΩΦ(DH_j)=∫Λ|DH_j⁻¹|². Condition (10) gives global L² boundedness of the inverse derivatives. Weak compactness and the L² value limit identify every weak derivative limit as Dh, by testing against compactly supported smooth functions. Weak lower semicontinuity and (10) give convergence of the squared L² norms. The Hilbert identity then gives DH_j⁻¹→Dh strongly L². Section 5 smooths each fixed H_j with error 1/j in both directions; a single diagonal sequence gives the target.

The same argument applies directly to a smooth candidate sequence. The limsup bound is also necessary for strong inverse convergence. Mere boundedness gives only weak subsequential convergence; target-side uniform integrability without derivative convergence in measure is not a substitute for (10).

A useful local form would preserve full-rank germs and prove, on the **same** exceptional complement, small inverse energy in the corresponding target complement. Source forward-tail control is not enough: |cof A|²/|det A| is singular as one singular value vanishes. In the operational construction one needs simultaneous source and target trace transfer, a compatible cell extension, and summable two-sided costs, with constants fixed before tail selection. Reversing the construction independently yields another map and does not establish compatibility.

No rigorous target counterexample was found. The supported contribution is the corrected rank-stratum diagnosis, identities and explicit failure mechanisms, the stronger-input smoothing partial, and criterion (10). These are not claimed novel in the literature. The general initial symmetric replacement estimate remains unproved.
