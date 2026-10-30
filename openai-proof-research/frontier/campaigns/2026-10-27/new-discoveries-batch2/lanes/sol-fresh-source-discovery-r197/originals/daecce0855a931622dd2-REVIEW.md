# Independent Structural229 substantial-contribution review, round 1

**Conditional contribution verdict: TECHNICAL. Full correctness of the ENTIRE unchanged frozen statement AND submitted proof remains UNDISCHARGED.** This review assigns neither a correctness grade nor acceptance nor a count. The parent alone may adopt this conditional contribution finding.

The objects reviewed are `STATEMENT.md`, 2784 bytes, SHA256 `febac8d7844dbc09a741b31c52bfc05da9d2b9d116ea1bdda42ed19aad0455e9`, and `AUTHOR-PROOF.md`, 15446 bytes, SHA256 `bb9cca632d3a53ae08a60d18448ec2d5a601ec7bfb3a341990065257e73e16ff`, in the one admitted author packet. I read both in full, together with PREFREEZE, MATH-VALIDATION, FINAL, the outside REPORT, and the author's private reading record. The conditional verdict covers every conclusion, error term, normalization and auxiliary mathematical assertion in that statement and proof. It does not select a local asymptotic sublemma, substitute a repaired proof, or reduce the target to completeness.

The reason for the verdict is a complete compatible construction: the stipulated source already supplies a smooth positive orbit in a cooperative invariant box; finite-dimensional order comparison, a positive spectral projection and explicit variation of constants give the full critical asymptotic with the submitted errors; determinant algebra and one scalar barrier give the exact metric and warp constants; an elementary global length comparison then gives the full ball-volume law. Below I execute all these steps. In fact the global metric comparison admits a bounded radius error, stronger than the submitted sublinear error, by an explicit function whose gradient has norm at most one. No assertion that a named theorem automatically applies is needed.

This is an operational contribution assessment, not a claim that an identical theorem has appeared in the literature. Literature and original-history coverage is scoped. An unread paper, failed access or exclusion guard supplies no novelty or priority evidence. None is used as a reason for the verdict.

## 1. Inputs actually read, and what is already paid

Write S10 for *A Smooth Nonquadratic Entire Affine Maximal Graph in Dimension Ten*, October 5, 2026, and S39 for *The affine Bernstein theorem in dimensions three through nine*, September 24, 2026, both at the stipulated revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The 14 canonical blobs of this exact two-paper family were independently bound to the complete pinned tree by size and Git blob SHA1, as well as their admitted SHA256 values. That authentication is separate from the following semantic reading.

I read all mathematical constructions in the S10 driver: the introduction and theorem, Proposition `prop:reduction`, Lemma `lem:local`, Lemmas `lem:autonomous` and `lem:box`, Proposition `prop:global`, and the final theorem proof. Its two font-encoding inputs are production inputs, not missing mathematical dependencies. I read S39's driver in its actual input order, all five included files (`geometry`, `area`, `tubes`, `bounds`, `rigidity`), the nested thin-slice figure source, and both bibliographies. Source truth, including all those operations, is stipulated; I have not audited it.

S10 supplies the following at full strength:

* A contraction in the smooth variable s=r²/2, with positive averaged derivative and flux, gives the normalized smooth even profiles. It gives F(0)=P(0)=1, D²F(0)=I and D²P(0)=−11I/9, as well as local uniqueness of the integral fixed point.
* Its reduction supplies the positive Hessian of u, the exact quadratic-tensor identity, determinant identity, separated determinant weight, and verification of the fourth-order affine-maximal equation. This is a classical smooth solution, not a weak or approximate replacement.
* In dimension ten the radial equations are y⁸y′=r⁸FP^(−12/11), (y⁸P′)′=−11r⁸P^(−1/11), F′=y. The integrated negative flux keeps P′<0. Smoothness and positivity extend globally.
* For τ=log r, X=(A,B,D) satisfies

  A′=A(1+B−A),
  B′=B(9+A+(12/11)BD−9B),
  D′=(11−D)A−8D+BD(1−D/11).

  The box [0,9/2]×[0,7/2]×[0,33/7] is invariant. The source explicitly computes its nonnegative cross derivatives and uses the stationary upper corner to control its faces. The difficult choice of cooperative variables and global invariant-region construction is already paid.
* The source already identifies the singular power corner, A=9/2, B=7/2, C=33/2, D=33/7. It bounds the logarithmic derivatives sufficiently to rule out a finite continuation endpoint. It does not state the frozen monotone approach, logarithmic rates, or ball-volume coefficient.

The whole S39 construction is also paid: proper tangent caps from Euclidean completeness; affine-limit compactness and maximal-direction centering; the thin-slice rescaling; conormal affine-area covariance and the cap identity; support-coordinate second forms and measures; cofactor integration by parts and tube coercivity; positive cap mass, Hessian-minor and inverse-Hessian cell bounds; the exponential-versus-polynomial log-box contradiction; section balance, ray extension, normalized convexity modulus, and the final interior-estimate rescaling. In its tube calculation the key determinant is (n−2)(10−n)/16 at λ=1, and its uniform positive choice λ=15/16 is for 3≤n≤9. Nothing in this review transfers that strict coercivity to n=10. Its affine-complete immersed consequence uses TW2002 and retains connectedness, openness, immersion and the dimension restriction.

The admitted r28 original sections must also be carried, not reduced to a vague completeness observation. I read the exact retained original text and checked its three segment hashes against the admitted extents: original lines 15–28, 29–47 and 48–53, bytes [1458,2362), [2362,3571), [3571,4645). They give:

1. The global diffeomorphism (x,v)↦(x,F(x)sinh v), including the origin, and the exact tensor g=P^(1/11)[D²F+F dv²]. The determinant used here remains the determinant in the original affine graph coordinates.
2. With a(r)=FP^(−12/11), a is increasing and a≥1. From y⁹=9∫₀ʳs⁸a(s)ds one gets r⁹≤y⁹≤r⁹a(r), hence y/r≥1 and y′≥a^(1/9)≥1. Thus D²F≥I. This is not a lower bound for D²u.
3. The source bound C≤33/2 gives P(r)≥P(1)max(1,r)^(−33/2), and consequently h=P^(1/11)D²F≥c max(1,r)^(−3/2)|dx|². The exhaustion √c∫₀ʳmax(1,s)^(−3/4)ds tends to infinity and is 1-Lipschitz for h. The base metric is complete and has Euclidean-compact bounded balls.
4. In g=h+Q(x)dv², Q is positive on every compact base set. For a g-Cauchy sequence, projected points are h-Cauchy. Short connecting paths stay in a fixed enlarged base ball; there Q has a positive minimum, so their v differences tend to zero. The full metric is complete, without needing a global lower bound for Q or any asymptotic expansion.

This accounts for both the metric factorization and global affine completeness at their full compatible strength. Neither is a residual contribution of Structural229.

## 2. Actual primary comparisons and exact normalization

The primary references here are actual read proofs, with the precise versions and extents recorded separately. They are comparisons; the newer primary is not added to the stipulated upstream premises.

**TW2000:** N. S. Trudinger and X.-J. Wang, *The Bernstein problem for affine maximal hypersurfaces*, Invent. Math. 140 (2000), 399–422, author-hosted PDF, DOI 10.1007/s002220000059. I read §§2–4 and §§6–7, and visually recovered the formulas on PDF pages 21–22. [Primary PDF](https://maths-people.anu.edu.au/~wang/publications/1-Invent00.pdf).

Section 7 transforms the singular graph √(|x′|⁹+t²) using T=u+t, V=u−t, so V=|x′|⁹/T. This plane transformation has determinant of absolute value 2; it is not the unit-determinant rotation used in the newer paper. For the general power r^(2α)/T, equations (7.5)–(7.10) compute the radial Hessian, the 2×2 determinant 4α(α−1)r^(4α−2)T^(−4), the full determinant C r^(2n(α−1)+2)T^(−n−2), and its determinant weight. The affine-maximal contraction is reduced in (7.11) to

    8α²−(n²−4n+12)α+2(n−1)²=0.

At n=10 this is 2(2α−9)²=0. Thus the critical power and its degeneracy are already present in the primary calculation. For the original square-root graph this gives F=r^(9/2), with

    P=[(9/2)^9(7/2)]^(−11/12) r^(−33/2).

It has the same logarithmic-derivative corner as S10, but no regular origin with F(0)=P(0)=1.

The singular variational verification is also operative, not merely a headline. Section 6 derives concavity of affine area, its first variation and the weak inequality (6.21), including the regular-part Hessian formulation and approximation/upper-semicontinuity discussion. Section 7 uses u∈W_loc^(2,1), the estimate by C r^(−3) times the second-derivative variation measure, its ball-growth bound, Lemma 7.1's integrability estimate, and the excision/integration-by-parts formula (7.15) to assert the weak variational conclusion. Lemma 7.1 is stated with its elementary proof omitted in the paper; that omission is not silently represented as an original proof read. For the needed transverse r^(−3) integrability, covering a bounded axis segment's ε-tube by O(ε^(−1)) balls and using μ(Bε)≤Cε⁹ gives tube mass O(ε⁸); summing dyadic shells gives a finite ∑O(ε⁵). The smooth positive orbit and its rates are not supplied by this weak singular verification.

The singular metric already explains the leading warp ratios: Q is a constant times r³ and ρ=√(7Q), so φ²/ρ²=9/14 and ψ²/ρ²=1/7. It does not give the smooth graph's global ball volume. At the singular tip ψ tends to zero, whereas the smooth graph has a noncompact central axis with minimum fiber cost one. In the tip completion of the purely conical model, arbitrary finite v displacement can be made at arbitrarily small cost near the tip, and the v integral over a tip ball is infinite. This is an obstruction to the naive singular-cone volume substitution, not an obstruction to the stronger smooth warped-metric construction in §7 below.

**TW2002:** N. S. Trudinger and X.-J. Wang, *Affine complete locally convex hypersurfaces*, Invent. Math. 150 (2002), 45–60, author-hosted PDF, DOI 10.1007/s00222-002-0229-8. I read its definitions, Theorem A and corollaries, and all §§2–4, including the deferred star-shaped-domain lemma; PDF page 5 was inspected visually. [Primary PDF](https://maths-people.anu.edu.au/~wang/publications/2-Invent02.pdf).

Theorem A is affine completeness ⇒ Euclidean completeness for locally uniformly convex hypersurfaces of dimension at least two; Corollary 1 supplies a global convex graph for an open such hypersurface. It is not the reverse implication. The proof uses the maximal local graph, the Legendre map, and the positive determinant weight ρ*=(det D²u*)^(1/(n+2)) in the transformed affine length. Lemma 2.1 averages lengths in a cone: Cauchy–Schwarz bounds a ray length by (∫ρ*)^(1/2)(∫u*ηη)^(1/2), and weighted Hölder and the gradient-image volume bound control the averaged first factor. Lemmas 2.2–2.4 exclude finite-slope accessible boundary points and make the dual domain convex. Section 3 supplies the boundary graph argument for immersed hypersurfaces; §4 proves the deferred domain criterion by Monge–Ampère mass and dimension induction. These operations distinguish the completeness notions but supply no critical orbit rate or exact smooth-orbit R¹¹ coefficient. The present argument does not infer affine completeness from entire graphicality.

**TW2610.09385v1:** N. S. Trudinger and X.-J. Wang, arXiv:2610.09385v1, supplied 49-page PDF. I read all §3, including §§3.1–3.4 and Lemmas 3.1–3.2, and inspected PDF pages 18 and 22. [Versioned primary PDF](https://arxiv.org/pdf/2610.09385v1).

The comparison can be made exact. Its unit-determinant 45-degree change has

    T=(u+t)/√2,  U=(u−t)/√2,  U=h(r)/T,  h=F²/2.

Let S=2hh″−h′². Then h′=FF′, S=F³F″, and in dimension ten

    (h′/r)^8 S=F^11 det D²F=F^12 P^(−12/11).

Therefore its scalar determinant weight, called g in (3.5), is exactly G=P/F¹¹. This G is not the affine metric g of the frozen statement. Its equation (3.4) becomes

    G″+(7h′/h+8h″/h′)G′+55(h″/h)G=0.

Writing a=F′/F and b=F″/F′, its two coefficients are 22a+8b and 110(a²+F″/F). Substitute G=F^(−11)P. After multiplication by F¹¹ the P′ coefficient is 8b; the a² coefficient is 132−242+110=0; the F″P/F coefficient is −11−88+110=11. The result is exactly

    P″+8(F″/F′)P′+11(F″/F)P=0,

which, together with the determinant relation, is S10's radial system. This proves the normalization and equation compatibility, rather than identifying the papers by an ansatz name.

For h=F²/2 the initial values are h(0)=1/2, h″(0)=1. The newer paper's h(0)=h″(0)=1 corresponds to

    h_TW(r)=F(r/√2)².

Equivalently its entire square-root graph is the ambient dilation by √2 of S10's graph. Its square-root radial factor is F_TW(r)=√2 F(r/√2), and the corresponding reduced P is P_TW(r)=2^(55/12)P(r/√2). The normalized determinant weight at zero is then 2^(−11/12), as (3.5) also gives. In A,B,D coordinates this is the same orbit with τ shifted by −(log 2)/2. Uniqueness here can be checked against the paid regular-origin integral formulation: any smooth positive radial solution with the same initial data satisfies those integrated equations and lies in the contraction neighborhood. It does not depend on treating a singular-origin fourth-order ODE as an ordinary nonsingular initial-value system by assertion alone.

The actual §3 construction uses the singular h*=c r⁹ as a variational comparison, concavity/uniqueness for the reduced area functional, and a three-case finite-radius continuation analysis. Section 3.3 uses p=h^7(h′)^8 and (pG′)′+55(h″/h)pG=0. Its fundamental-matrix estimate in Lemma 3.2 uses an integrable bound on coefficients and the determinant of the fundamental matrix; its subsequent h=varphi² inequality bounds varphi″ and yields derivative continuation estimates. These are genuine compatible antecedent operations for the fixed orbit. They are finite-interval continuation estimates, not the frozen corner-deficit asymptotic or its two logarithmic exponents.

There are important comparison limits. The proof's constants explicitly allow an interior C* beyond its initially displayed endpoint bounds. The printed discarded power of 2 below (3.13) is not used here: direct substitution h=varphi² in (3.5) gives the factor 2^(−n(n+1)/(n+2)), while the printed discarded exponent is −(n+1)²/(n+2). All normalization constants above come directly from (3.5) and S10's clean determinant identity. The paper is not stipulated true, and this review neither repairs nor validates its entire theorem. Its higher-dimensional product remark is not imported: adjoining quadratic variables changes the required classical determinant exponent, so a product claim alone cannot justify such a transfer.

Section 3.4's actual growth proof uses superlinear conditions u(λx)≥(λ+δ)u(x) or x·Du≥(1+δ)u, the entire Legendre image, normalized centered sections, exclusion of a vertical limiting ray, regularity and blow-down. For the fixed graph here, u(0,t)=√(1+t²), so u(0,λt)/u(0,t)→λ and t u_t(0,t)/u(0,t)→1. Thus neither uniform positive-δ hypothesis holds. That framework gives no radial logarithmic refinement or ball coefficient for this orbit. I read the §3.4 proof, but not every earlier regularity proof or nested cited original to which it refers; none of those unverified branches is an input to the reduction below.

Other operative comparisons were actually read. TW's affine Plateau preprint arXiv:math/0405541v1, §7, proves the generalized Legendre area identity and gives support reconstruction (7.15)–(7.19), which is the relevant antecedent for S39's support-coordinate formulas. Du arXiv:2210.09127v2, §9, computes the product Hessian/determinant and the power-weight conditions for its exponential examples; its θ=(N−1)/N and θ=1/2 examples do not provide the classical θ=11/12 in graph dimension ten. Sun–Xing–Xu arXiv:2608.25330v1, theorem interfaces and §2, computes the determinant and inverse for f=(x₁−∑_{k≥2}x_k²/2)^β and the range a∈[−n/(n+1),0). At n=10 this excludes a=−11/12. Direct substitution of −11/12 into its displayed β gives β=1/2, which does not retain the convexity required by that construction. These are actual incompatible-hypothesis checks, not evidence from a citation or abstract.

## 3. Cooperative monotonicity and selection of the corner

Here is the first part of the full compatible classical reduction. It starts from exactly the paid normalized orbit.

Smooth even expansion and the radial equations give

    F=1+r²/2+a₄r⁴+O(r⁶),  P=1−11r²/18+O(r⁴).

In (y/r)⁸y′=FP^(−12/11), the r² coefficients are 44a₄ and 7/6. Thus a₄=7/264, and

    A=r²+O(r⁴),
    B=1+(7/33)r²+O(r⁴),
    D=(11/9)r²+O(r⁴).

The expansions are smooth in r², so their remainders remain of the indicated order after r∂r. All three components of X′ are therefore positive at sufficiently negative τ.

The source's off-diagonal Jacobian entries on its box are A, B, (12/11)B², 11−D, and D(1−D/11), with the other entry zero; they are nonnegative. Along the orbit H=X′ obeys H′=DV(X)H. On a finite interval add M times the identity so all entries are nonnegative. The integral equation for e^(Mτ)H and its Picard iterates preserve the cone, and in each coordinate retain the strictly positive initial term. This proves H>0 on every later finite interval. It is the source's already exposed order structure applied to the derivative equation; it needs no unproved global monotone-system theorem.

Each coordinate increases and is bounded, hence tends to a limit X∞. Since V is continuous, X′ tends to V(X∞); a nonzero limiting component would contradict convergence. At the limiting equilibrium A>0, B>1 and D>0. The first equations give B=A−1 and D=11(4A−9)/(6(A−1)). Substitution in the last equation gives

    V₃=55(2A−9)²/[36(A−1)].

For clarity the numerator calculation, after division by 11, is

    36A(A−1)−54(4A−9)−(4A−9)²=5(2A−9)².

The only possible corner is X*=(9/2,7/2,33/7). Strict increase also means every coordinate is strictly below its limit at every finite τ. Thus the deficit z=X*−X is componentwise positive and tends to zero. This is exactly the sign information needed for the critical asymptotic, not an assumed genericity or orbit-selection assertion.

## 4. Full critical asymptotic, including the stable-only exclusion

The following is the elementary positive-projection/variation-of-constants method, executed with the exact data. It is not an appeal to the name “center manifold” or “normal form.” The same proof applies to a finite-dimensional C³ vector field with a simple neutral eigenvalue, a stable complement, a positive left projection controlling a positive-cone deficit, and a nonzero quadratic projected drift.

For z=(a,b,d), exact polynomial expansion at X* gives

    z′=Jz−Q₂(z)+Q₃(z),
    J=[−9/2, 9/2, 0;
        7/2, −27/2, 147/11;
        44/7, 132/49, −12],
    Q₂(z)=(ab−a²,
           ab−(27/7)b²+(84/11)bd,
           −ad+(1/7)bd−(7/22)d²),
    Q₃(z)=(0,(12/11)b²d,−bd²/11).

The characteristic polynomial is λ(λ+15)². Put

    ν=(1,1,110/147),  ell=(308,132,147)/550.

Direct multiplication gives Jν=0, ell J=0 and ell ν=1. Every entry of ell is positive, and its minimum is 6/25. Consequently

    q=ell z>0,  |z|₂≤sum z_i≤(25/6)q,  q→0.

This is the essential exclusion of an uncontrolled stable-only trajectory. It uses the actual one-sided source orbit, not a free solution near the equilibrium.

Let Π=ν ell, S=I−Π, and w=Sz=z−qν. Then w lies in E=ker ell. Writing a vector in E as (a,b,−44a/21−44b/49), the restriction of J on its first two coordinates is

    J_E=[−9/2,9/2; −49/2,−51/2].

Its nilpotent part J_E+15I is [21/2,9/2;−49/2,−21/2], whose square is zero. Thus the stable Jordan block is explicitly accounted for:

    exp(sJ)|_E=e^(−15s)[I+s(J+15I)|_E],
    ||exp(sJ)|_E||≤C(1+s)e^(−15s),  s≥0.

There is no hidden diagonalizability assumption. Set N(z)=−Q₂(z)+Q₃(z). On the actual tail, |N(z)|≤Cq² and |q′|≤Cq². Hence

    (1/q)′≤C,  q(τ)≥1/[q(T)^(−1)+C(τ−T)].

In particular q has a polynomial lower bound. An exponentially decaying nonzero stable-only deficit is incompatible with this inequality and the positive projection. Also |q′|/q≤Cq→0. For any ε>0, increase T until this ratio is at most ε, giving

    q(s)≤e^(ε(τ−s))q(τ),  T≤s≤τ.

The projected differential equation can be integrated directly by differentiating e^(−τJ)w(τ):

    w(τ)=e^((τ−T)J)w(T)
       +∫_T^τ e^((τ−s)J)S N(z(s)) ds.

Take, for example, ε=1. Its integral is bounded by

    C q(τ)² ∫₀^∞(1+h)e^(−13h)dh.

The homogeneous term is O((1+τ−T)e^(−15(τ−T))), which is O(q(τ)²) by the preceding polynomial lower bound. Therefore

    z=qν+O(q²).

Both estimates are for this fixed orbit and have finite constants; no family uniformity or tracking theorem is assumed.

The displayed quadratic polynomial gives

    Q₂(ν)=(0,20/7,−2530/3087),
    ell Q₂(ν)=7/15.

As w=O(q²), bilinearity gives Q₂(qν+w)=q²Q₂(ν)+O(q³), while Q₃(z)=O(q³). Therefore

    q′=−(7/15)q²+O(q³).

For H=1/q, this becomes H′=7/15+O(q). First q→0 gives H/τ→7/15, hence q=O(1/τ). Integrating the error again gives H=(7/15)τ+O(log τ), and inversion gives

    q=15/(7τ)+O(log τ/τ²).

Combining with w=O(q²) proves in the ordinary Euclidean norm exactly

    (9/2−A,7/2−B,33/7−D)
      =[15/(7τ)](1,1,110/147)+O(log τ/τ²).

This closes the strongest compatible asymptotic route, including q>0, the stable-only exclusion, the stable Jordan block, and the full quantitative remainder. The hard source orbit construction remains paid; no additional global matching or selection problem survives in this fixed-solution application.

## 5. Both logarithmic profiles and the exact positive-constant constraint

The A expansion gives

    ∂τ log F=9/2−15/(7τ)+O(log τ/τ²).

The error has an absolutely integrable tail, bounded in absolute value by C(log τ+1)/τ. Thus log F−(9/2)τ+(15/7)log τ has a finite real limit log cF, giving cF>0 and

    F(r)=cF r^(9/2)(log r)^(−15/7)
          [1+O(log log r/log r)].

Positivity of cF follows from exponentiating a finite real limit; it is not an arbitrary normalization constant or an unproved nonvanishing limit.

For P the exact relation C=BD gives

    C=33/2−[33/7+(7/2)(110/147)]q+O(q²)
     =33/2−(22/3)q+O(q²).

Consequently

    ∂τ log P=−33/2+110/(7τ)+O(log τ/τ²),

and exactly the same integrable-tail calculation gives a finite real limit log cP and

    P(r)=cP r^(−33/2)(log r)^(110/7)
          [1+O(log log r/log r)],  cP>0.

The source equation, y=AF/r and y′=ABF/r² give the exact identity

    A⁹ B F⁸ P^(12/11)=r¹⁸.

Here 8(9/2)+(12/11)(−33/2)=18 and 8(−15/7)+(12/11)(110/7)=0. Taking the limit therefore yields exactly

    (9/2)^9(7/2)cF⁸ cP^(12/11)=1.

The two constants belong to the one normalized solution. Their existence and the constraint do not create a free parameter family. All frozen error rates and positive constants have now been supplied by the compatible calculation, not just unspecified equivalences.

## 6. Exact metric, the Q barrier, proper radius, warp limits and completeness

The paid Hessian tensor identity is

    D²u=(F/u)D²F+(F²/u³)(dt−(t/F)dF)²,
    det D²u=F¹¹u^(−12)det D²F,
    det D²F=F P^(−12/11).

Pull it back by ζ=t/F and v=asinh ζ. Since F is positive and smooth, this is a global smooth change of parameters, including x=0. The tensor becomes

    (1+ζ²)^(−1/2)D²F+F(1+ζ²)^(−3/2)dζ².

The original affine-coordinate determinant is P^(−12/11)(1+ζ²)^(−6); multiplying by its −1/12 power and using dζ=cosh v dv gives exactly

    g=P^(1/11)[D²F+F dv²].

This does not treat a nonlinear change of parameters as a new affine graph Hessian. The factorization and its smoothness were already supplied in the r28 original.

For the extra global monotonicity of Q=FP^(1/11), put E=A−C/11. Near zero E=(8/9)r²+O(r⁴)>0. The source equations give

    C′=C(1+C−8B)+11AB.

At a hypothetical first zero of E one has C=11A and

    E′=A(8B−12A).

But D=C/B≤33/7 implies B≥7A/3 there, so E′≥(20/3)A²>0. A differentiable function reaching its first zero from positive values has derivative at most zero. This contradiction proves E>0 for every r>0. Thus ∂τ log Q=E>0 and Q(0)=1, giving Q≥1 with strict radial increase. This is a single scalar first-contact barrier using the paid box; no new invariant-region construction is required.

Set K=cF cP^(1/11)>0. The two profile expansions give

    Q=K r³(log r)^(−5/7)[1+O(log log r/log r)].

Away from the axis D²F=F″dr²+rF′g_S8. Hence

    ρ′(r)=sqrt(ABQ)/r,
    (sqrt Q)′(r)=E sqrt Q/(2r),
    φ²=QA,  ψ²=Q.

At zero, ρ=r+O(r³), φ=ρ+O(ρ³), ψ=1+O(ρ²). The tensor extends smoothly there by its Cartesian expression. The base exhaustion in r28 already proves radial properness; alternatively the displayed Q growth and AB→63/4 make the integral defining ρ diverge. In particular ρ maps [0,∞) increasingly onto [0,∞).

Both ρ and sqrt Q tend to infinity, E→3 and AB→63/4. Their derivative quotient tends to

    2sqrt(AB)/E → sqrt 7.

Integrating upper and lower bounds for this quotient after a fixed radius gives ρ/sqrt Q→sqrt 7; no unproved differentiation of an asymptotic equivalence is used. Consequently

    g=dρ²+φ²g_S8+ψ²dv²,
    φ²/ρ²→9/14,  ψ²/ρ²→1/7.

These are the exact frozen constants. No stronger error for the warp limits is required by the frozen statement.

The submitted completeness argument is also compatible: radial displacement is bounded by path length and, since ψ≥1, so is |Δv|. A g-Cauchy sequence has bounded proper radial coordinate and bounded v, hence lies in a Cartesian compact set. Smooth positive metric equivalence there gives convergence. This includes passages through the axis, where ρ along a piecewise smooth path is absolutely continuous. The stronger fact that completeness needed neither these rates nor Q≥1 was already paid by r28, as recorded in §1.

The auxiliary distinctions in the submitted proof are retained. The entire smooth graph's induced Euclidean metric is complete because its path distances dominate base Euclidean distances and a base limit lifts smoothly. This is not the argument for affine completeness. For the Hessian metric D²u, the ray x=0 has coefficient u_tt=(1+t²)^(−3/2). Its square-root integral to infinity is finite, so that metric is incomplete. Thus local Hessian positivity, Euclidean completeness, affine completeness, and Hessian-metric completeness have not been interchanged.

## 7. Global distance comparison through arbitrary excursions and the full density integral

First execute the submitted route exactly. At p0=(x,v)=(0,0), an axis path and then a radial path at fixed v have length |v|+ρ, since ψ(0)=1. Thus d(p0,·)≤ρ+|v| uniformly in the angle and v.

For any piecewise smooth path of length L and a threshold k>0, split its length into L_in on ρ<k and L_out on ρ≥k. Monotonicity of ψ gives

    |v|≤L_in+L_out/ψ(k)≤L_in+L/ψ(k).

The total variation of (ρ−k)_+ is at least (ρ_final−k)_+ and is bounded by L_out. This remains true with arbitrary returns across the threshold, motion on its level set, angular detours, and axis passages. Hence

    L(1+1/ψ(k))≥|v|+ρ_final−k.

Taking the infimum over all such paths, without any minimizing-geodesic confinement assumption, gives for D(T)={ρ+|v|<T}

    D(R) ⊂ B_g(p0,R)
       ⊂ D(R(1+1/ψ(k))+k).

With k=√R and ψ(k)~k/√7, the outer radius is R+O(√R). This already includes v of order R; there is no bounded-v restriction hidden in the argument.

A stronger compatible classical construction makes the absence of a residual global comparison problem particularly transparent. Define

    H0(ρ)=∫₀^ρ sqrt(1−ψ(s)^(−2)) ds.

Because ψ≥1, this is real. For either sign, away from the axis,

    |d(H0(ρ)±v)|_g²=H0′(ρ)²+ψ(ρ)^(−2)=1.

These functions extend locally Lipschitz across the axis; indeed Q=1+(4/9)r²+O(r⁴), ρ=r+O(r³), and H0(ρ)=ρ²/3+O(ρ⁴). Integrating their derivative bound along every path gives

    d(p0,(ρ,ω,v))≥H0(ρ)+|v|.

There is a finite fixed constant

    C0=∫₀^∞[1−sqrt(1−ψ(s)^(−2))]ds.

Near zero the integrand is bounded by one. At infinity it is at most ψ(s)^(−2), because 1−sqrt(1−x)=x/(1+sqrt(1−x))≤x for 0≤x≤1, and ψ(s)~s/√7. Therefore

    ρ+|v|−C0 ≤ d(p0,(ρ,ω,v)) ≤ ρ+|v|,
    D(R) ⊂ B_g(p0,R) ⊂ D(R+C0).

This stronger bounded-error construction is a length bound for the same complete smooth metric, not a substitute theorem or a repair of the submitted proof. It proves all the submitted global comparisons at once. It uses only the minimum fiber cost, the exact radial coefficient, and square-integrability of 1/ψ at infinity. It does not assume a compact link, a proper tangent cone, uniform tensor convergence for growing v, or a globally minimizing path of any prescribed form. The spherical warp enters only in the volume density.

Now carry the whole integral. With the measure-zero axis removed,

    dVol_g=W(ρ)dρ dω dv,  W=φ⁸ψ,
    W(ρ)~κρ⁹,  κ=(9/14)^4/√7.

Near zero W=O(ρ⁸), and globally W≤C(1+ρ⁹). Thus all bounded D(T) have finite volume and

    Vol_g D(T)=2|S⁸|∫₀ᵀ(T−ρ)W(ρ)dρ.

After ρ=Ts, the integrand divided by T¹¹ is bounded for T≥1 by C(1−s)(1+s⁹). Dominated convergence, or splitting off a fixed compact radial interval, gives

    lim Vol_g D(T)/T¹¹
      =2|S⁸|κ∫₀¹(1−s)s⁹ds
      =2|S⁸|κ(1/10−1/11)
      =|S⁸|(9/14)^4/(55√7).

Either the submitted R+O(√R) squeeze or the stronger R+C0 squeeze gives exactly this coefficient for B_g(p0,R). For any fixed p, d0=d_g(p,p0) is finite and

    B_g(p0,R−d0) ⊂ B_g(p,R) ⊂ B_g(p0,R+d0),  R>d0.

Dividing by R¹¹ proves the same coefficient at every fixed center. There is no assertion of a uniform estimate when the center itself depends on R. This completes the geometric calculation at the entire frozen scope, including the noncompact fiber and every normalization factor.

## 8. Exact covariance and other auxiliary proof claims

The numerical coefficient is tied to the stated normalization. Here is a direct check of the submitted covariance claim, not a qualitative appeal to affine invariance. For a parametrized ten-dimensional hypersurface with positive second form H from an arbitrary inward conormal ν and transversal ξ with νξ=1, let T=|det(X₁,…,X₁₀,ξ)|. The Blaschke metric is

    g=(det H)^(−1/12) T^(1/6) H.

Positive rescaling of ν cancels in this formula, and it agrees with (det D²u)^(−1/12)D²u on a graph. An ambient linear map L leaves H unchanged under pullback if ν is transformed by L^(−1), and multiplies T by |det L|. Thus the metric scales by c=|det L|^(1/6). Riemannian dimension is ten, so volumes scale by c⁵ and distances by sqrt c. An R¹¹ coefficient therefore scales by c⁵c^(−11/2)=|det L|^(−1/12), exactly as the submitted proof says. Completeness and growth exponent survive this fixed homothety, while the numerical coefficient changes.

For the radial reduced system the compatible positive scaling is

    F_new(r)=a F(br),
    P_new(r)=a^(−22/3)b^(−33/2)P(br).

The first equation follows directly from det D²F_new=a⁹b¹⁸ det D²F; the second reduced equation has the same common factor on its two terms. The corresponding ambient map is (x,t,u)↦(x/b,at,au), whose determinant is a²b^(−9) and whose pulled-back metric factor is a^(1/3)b^(−3/2), consistent with the preceding formula. Requiring F_new(0)=P_new(0)=1 forces a=b=1. The origin determinant relation then also forces the Hessian normalization. This confirms there is no unused parameter freedom in the proposed fixed orbit.

The source already verifies nonquadraticity through u(0,t)=√(1+t²), global smoothness, pointwise Hessian positivity, embedded entire graphicality and the nonlinear equation. No new product, suspension, cutoff, Legendre-dual entire domain or perturbative solution family is asserted or used. The nonproper conical limiting model is not promoted to a proper global tangent cone. The pinned Lean comparator was read: its theorem ends in `sorry`, so it supplies no proved formal support. No formal build was performed.

## 9. Objections considered, resolutions, and the contribution decision

A merely qualitative limit at the corner would leave the logarithms unproved. Here the positive cone controls the entire deficit by a positive scalar projection, the stable block is explicitly integrated, and the quadratic drift gives the stated O(log τ/τ²) error. The stable-only alternative is excluded quantitatively, not by a genericity slogan.

A theorem about asymptotically conical metrics with compact link would not automatically apply: the v fiber is noncompact and the smooth axis has the cheapest longitudinal cost. Here every path is controlled, first by the exact submitted inner/outer splitting, and more strongly by H0±v. The full integral then supplies the R¹¹ power and 1/55 factor. The failure of the naive compact-cone shortcut has no remaining force after this construction.

A use of TW2002 in the wrong completeness direction would also be invalid. Neither the submitted proof nor this compatible reduction needs that inference; r28 already provides completeness by a proper base exhaustion and fiber control. Likewise the generalized-exponent examples and the newer paper's superlinear-growth theorem have been tested against their actual hypotheses, rather than treated as interchangeable classical results.

The quantitative conclusions are meaningful descriptions of a particular smooth example. Quantitative sharpness is not itself a reason to downgrade them. The reason for TECHNICAL is the explicit exhaustion of their operations at this scope: the source has already solved smooth construction, positivity, continuation and the cooperative invariant geometry; a general positive-projection argument with elementary stable-matrix integration then forces every asymptotic exponent and error; a scalar determinant identity fixes the constant relation; a scalar first-contact barrier and ordinary radial integration give the warp constants; and a general warped-length calculation plus one density integral gives the exact global volume coefficient. None requires a new family, nonlinear matching, a uniform parameter estimate, a new PDE solution, or an additional global compactness mechanism.

In particular, the proposed positive neutral projection is not left as an unpaid operation merely because it is useful: all its signs are consequences of the paid box and monotone orbit, and its application is fully executed in §§3–5. The global ball comparison is not left as an unpaid operation merely because v is unbounded: §7 executes a stronger compatible construction uniformly in v. There is no identified obstruction to this complete source/classical/original-history reduction, and no essential contribution comparison is left unfinished for the verdict stated here.

This conclusion is conditional on correctness of the entire unchanged author statement and submitted proof. The explicit reductions above are evidence for that contribution assessment, not a replacement author proof and not a discharge of the separate correctness obligation. Any correctness objection to any original clause or auxiliary claim must still be handled by the independent correctness role and parent; this review cannot cure it by narrowing the target.

## 10. Limits and remaining obligations

Exact source/primary reading coordinates, visual limits, masked-boundary handling, accidental exposures, failures and timing are in the separate local reading/access record. Calabi 1982's actual original proof remains unread; the author's failed JSTOR access was inspected as metadata, not retried or represented as my own successful access. Chern 1979 and several nested regularity originals remain unread. The newer TW paper is a selective comparison, not a stipulated theorem or a complete literature audit. No unexamined external center-manifold theorem, metric comparison theorem or asymptotic-integration theorem is a dependency: the actual elementary operations used for the verdict have been proved directly above. S10's cooperative construction and TW2026's fundamental-matrix calculation were read rather than cited by name alone.

Original-history coverage is only the admitted r28 mathematical sections. No broader history rerun, peer-review body, correctness review, parent assessment, registry body or closed-target namespace was read. There is no exhaustive history clearance, literature absence or priority claim. All admitted author originals were authenticated before reliance and are rechecked for unchanged bytes and modes at completion. Artifact verification and copied controls are not mathematical gates.

The remaining mathematical review obligation is full independent correctness of the unchanged statement and proof, UNDISCHARGED in this role. Parent adoption, acceptance/count decisions and any downstream formal/manuscript/release work remain outside this review. Publication, uploads, submissions, contacts and browser UI were not undertaken.
