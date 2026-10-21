# Positive-density Coulomb nonattainment: two integrated reductions

PREFREEZE / no nominee. These are research calculations at the unchanged full target P of analytic r10 and coulomb-positive-r2. They do not freeze, nominate, or independently grade a supporting theorem. Source373 and its operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## 1. Scope and credited operations

P asks for a real g in S(R^3), positive at EVERY point, with integral g²=1, such that for μ=g²dx the three-particle Coulomb minimum is finite and attained, no pair of μ-preserving Borel maps attains it, and finite-cost preserving pairs approach it. The cost is c(x,y,z)=|x-y|^(-1)+|x-z|^(-1)+|y-z|^(-1), infinite on collisions. No map regularity, support gap, changed cost, approximate marginal, or restricted quantifier is substituted.

Use the source's bounded union U of five component balls, its smooth component potentials u, its central common ball B and four branch diffeomorphisms H_j=(Y_1,W_1,Y_2,W_2). Restrict closures inside the original neighborhoods if needed before choosing a nonnegative bump g_b compactly supported in B. Put ν=g_b²dx and

    μ0=ν/3 + Σ_j (H_j)#ν/6.

The source constructs a symmetric contact plan π0 and gives E0=3∫u dμ0. Its exact contact set on U³ contains just the two opposite-pair sheets and their permutations. Write K=supp μ0, compactly contained in U. Choose a closed ball Q of positive radius strictly inside {g_b>0}; all four H_j(Q) are inside positive-density regions of μ0. Smaller/larger compact patches below are fixed before ε tends to zero.

Credit separately:

* Source373 local strict convexity, separate projection invertibility, all component-pattern inequalities, exact mass domination, and map approximation.
* GKR's shared-component harmonic example, including its actual selection/uniqueness proof, is an antecedent. It is not a positive-density Coulomb construction.
* CDM author version April 11, 2013, Theorem1.1/Remark1.3 supplies equality of infima for nonatomic Coulomb marginals.
* BCD arXiv:1608.08780v1 supplies uniform collision separation under a uniform small-concentration bound and bounded Lipschitz/semiconcave dual potentials. Its operative exclusion/recombination proof and dual estimates were read; GKR arXiv:1805.00880v1 supplies the wider duality formulation.
* Old r10 constructs a bounded Lipschitz global feasible self-conjugate extension w preserving u on the old component union V=B∪ΣH_j(B). It also proves a compact set of binary minimizing pairs and finite contacts outside its projection R. Positive-r2 already proves that an all-space smooth contact atlas with every coordinate projection diffeomorphic yields a positive Schwartz-square contact marginal. Its separate projection-rank warning and failed common-translation smoothing are retained.

All-N nonattainment (r54 T373N) and the sharp BV/fractional cost author theorem I220 already exist. They are not candidates here. T373E135 and all prior dispositions remain unchanged.

## 2. Inverse variational completion lands exactly at the binding threshold

Take the actual old r10 extension w, and use its notation

    a=inf_{y≠z} [|y-z|^(-1)-w(y)-w(z)].

Its established properties are w=Tw, w≥a, w(x)→a at infinity, a≤-3/2, sup w≤2+1/√2, and a is attained by at least one finite pair (y*,z*). There are old finite three-particle contacts. These are actual old deductions, not new assumptions inserted into P.

Normalize to the vanishing external potential v=a-w. If E_k(v) is the infimum of the k-particle pair energy plus Σv, then direct algebra gives

    E3(v)=3a,                       (2.1)
    E2(v)=a+2a=3a.                 (2.2)

For (2.1), global feasibility gives c-Σw≥0 and an old contact attains zero. For (2.2), use the definition and attainment of a. Thus the inverse construction is critically bound, not strictly bound.

Here is the exact translation into the compatible relaxed primary, Bouchitté–Buttazzo–Champion–De Pascale arXiv:1907.08425v1. In its notation

    M_k(φ)=sup [(1/k)Σ_i φ(x_i)-c_k(x_1,...,x_k)].

Set Φ=3(w-a), a nonnegative continuous function vanishing at infinity. Then

    M3(Φ)=-3a,
    M2((2/3)Φ)=-3a.                (2.3)

Its strict-binding condition M3(Φ)>M2((2/3)Φ), which forces every relaxed minimizer to have full mass, is therefore unavailable for this particular preserved calibration. This is an equality computation, not a claim that the primary has overlooked a hypothesis.

There is an explicit relaxed minimizer of mass 2/3. In the one-point compactification use the symmetric law of (y*,z*,∞). Its finite marginal is

    ρ*=(δ_y*+δ_z*)/3.

Its relaxed cost is |y*-z*|^(-1): the binary stratum achieves that cost, and relaxed duality gives the reverse bound because

    ∫Φ dρ* - M3(Φ)
      = w(y*)+w(z*)-2a+3a
      = |y*-z*|^(-1).

Consequently ρ* minimizes Cbar(ρ)-∫Φ dρ, with value 3a. The smooth but gapped μ0 is also a full-mass minimizer of this same inverse objective, by (2.1). Existence in this convex inverse variational problem hence supplies neither a positive density, an absolutely continuous density, nor even full mass for every minimizer. It remains compatible with existence of a good minimizer: the calculation is not an impossibility result.

Lelotte's 2025 asymptotic/dissociation proof explains why critical binding is compatible with a positive full-support marginal: a dual potential for such a marginal has a+(N−1)/|x|+o(|x|^(-1)), and the corresponding external potential has E_N=E_{N−1}. Strict binding would not be the right surrogate. The full-mass positive contact selection, not the energy identity itself, is unpaid.

One can add density caps, entropy, or derivative penalties to choose a better minimizer, but their Euler conditions change the dual potential. Exact old contacts cannot simply be retained by declaring those constraints inactive. This leads to the deforming-potential route below, which does not assume that w stays fixed.

## 3. Fill all gaps first, and allow the optimal potential to move

Fix any normalized h>0 in S(R^3), for example a Gaussian, and let σ=h²dx. For 0<ε≤1/2 set

    με=(1−ε)μ0+εσ.

Its square root is everywhere positive and Schwartz: it is smooth by strict positivity, and outside a fixed compact set equals √ε h; the difference from √ε h is smooth and compactly supported. This establishes the exact density class in P for every ε, but does not establish nonattainment.

The densities have a common L∞ bound M. Their product couplings have finite Coulomb cost; the estimate ∫|x-y|^(-1)ρ(y)dy≤2π||ρ||∞+1 suffices. Tightness and lower semicontinuity give an optimal πε. It need not be symmetric for what follows.

Choose a globally feasible bounded Borel potential w0 by setting w0=u on U and w0=−2M_u outside, where M_u≥sup_U|u|. Every triple meeting U^c has potential sum≤0<c. Put

    R0=c−Σ_i w0(x_i)≥0,
    Cσ=∫c dσ^⊗3,
    D=Cσ−3∫w0 dσ≥0.

The competitor (1−ε)π0+εσ^⊗3 and exact marginals give the quantitative bound

    ∫ R0 dπε
      = E(με)−3∫w0 dμε
      ≤ εD.                                             (3.1)

This holds for EVERY optimal πε. It does not claim that πε saturates w0. Typically the left side is positive. Also

    πε{x_i∉K for some i}≤3ε,
    πε{y∉U or z∉U}≤2ε.                                (3.2)

These bounds use marginal identities alone and retain arbitrary Borel optimizers.

## 4. Uniform primary separation and actual dual gradients

Pick β>0 such that M(4π/3)β³<1/100. The BCD small-concentration exclusion gives a common η>0, independent of ε, so every optimal πε is supported where all three pair distances are≥η. One may take a conservatively smaller η than its theorem's threshold β/9; no sharp constant is needed.

The mechanism is compatible with (3.1): from a putative near-collision configuration choose two further positive-mass configurations avoiding the β-neighborhoods of all previous coordinates. The uniform concentration bound leaves positive mass at each choice. Latin cyclic redistribution across three equal-mass restrictions makes all new pairs separated. Normalize each product of three restricted marginals by the square of its common mass. The competitor then has the SAME mass and all the SAME marginals. Its cost is at most a fixed multiple of β^(-1) times that mass, whereas the original near collision costs η^(-1) times it. Small enough η contradicts optimality. This uses no regularity of a transport map.

Choose a bounded Lipschitz dual maximizer vε, with common Lipschitz and semiconcavity constants as in BCD (the actual dual and regularity proofs were read). At πε-almost every triple, complementary slackness gives equality and differentiating the first coordinate gives

    ∇vε(x)=∇_x c(x,y,z).                                (4.1)

Indeed the nonnegative dual slack has a minimum in that coordinate, and vε is differentiable for Lebesgue-a.e. x; με has a density. Uniform pair separation bounds the right side by 2η^(-2). The same applies to the other coordinates. No differentiability of a selected map is used.

One can also see the needed local semiconcavity directly: at a contact over x, freezing y,z supplies a smooth upper support for vε in |x'−x|<η/2 whose Hessian is bounded above by a common constant. The contact first-coordinate set has full με-measure and is dense because με>0 everywhere. Continuity extends the upper-support/second-difference estimate to all x. Restriction to a smaller convex patch gives the usual one-sided gradient monotonicity. This avoids deriving semiconcavity from a possibly nonsmooth map.

## 5. A local L² gradient estimate with no fixed-contact assumption

Let Q+ be any compact convex patch strictly inside one of the old components, on which the density of μ0 is bounded below by m>0. Take an open neighborhood of Q+ still inside that component. Fix r>0 smaller than its boundary distance and η/4.

For a πε-contact (x,y,z) with x∈Q+ and y,z∈U, the function

    f_{y,z}(x')=c(x',y,z)−u(x')−u(y)−u(z)

is nonnegative in the local x'-ball. There, all x'-dependent pair distances are≥η/2, and u is smooth, so its gradient and Hessian have uniform bounds G and H. Choose L≥max(H,G/r,1). The descent step x'=x−∇f(x)/L remains in the ball; Taylor's bound and nonnegativity imply

    |∇_x c(x,y,z)−∇u(x)|² ≤ 2L R0(x,y,z).              (5.1)

This is a local nonnegative-function estimate, not an assumed global quadratic coercivity of the entire contact set. On the complementary event y∉U or z∉U, (4.1), separation, and the bounded ∇u give a uniform bound for the gradient error. Integrating (5.1), using (3.1),(3.2), and με≥μ0/2, yields

    ∫_{Q+}|∇vε−∇u|² dx ≤ C ε.                         (5.2)

The constant depends on the fixed source geometry, Q+, m, σ and η, but not ε or the choice of optimizer. Thus the primary duality/separation machinery actually pays a stronger perturbative step than weak convergence of plans alone. This estimate does not pay Jacobian control.

## 6. Semiconcavity upgrades (5.2) to an interior gradient rate

Write Fε=vε−u on Q+. It is uniformly semiconcave and uniformly Lipschitz. Choose Q− compactly inside the interior of Q+ with boundary distance δ>0. At differentiability points x,y the semiconcavity inequality reads

    (∇Fε(y)−∇Fε(x))·(y−x) ≤ A |y−x|².                 (6.1)

Take x∈Q−, p=∇Fε(x), q=|p|. Uniform Lipschitzness gives q≤G0. Increase A to A'≥max(A,G0/(4δ),1), and put r=q/(4A'). For directions e with p·e≤−q/2 and radii t∈[r/2,r], y=x+te remains in Q+ and (6.1) gives

    ∇Fε(y)·e ≤ −q/2+A't ≤ −q/4.

This cone annulus has volume c r³, and hence

    ∫_{Q+}|∇Fε|² ≥ c q² r³ ≥ c' q^5.

Together with (5.2), this proves the genuine interior estimate

    ess sup_{Q−}|∇vε−∇u| ≤ C ε^(1/5).                 (6.2)

It is an a.e. gradient estimate for Lipschitz potentials, not a C² estimate or a claim that vε is smooth. Componentwise additive constants do not enter it. Taking several fixed nested patches proves the same bound on the central and outer positive-density portions needed for a fixed tube around the old sheets.

## 7. What source strict convexity now does pay

On one old component type write

    F_k(x,y,z)=c(x,y,z)−u0(x)−v_k(z).

The source proves that its (x,z)-Hessian is≥λI on a sufficiently small convex product, λ>0, with unique minimum (X_k(y),Z_k(y)). At an actual πε-contact lying in the selected positive-density patches, the derivative equations give

    ∇_{x,z}F_k(x,y,z)
      =(∇vε(x)−∇u0(x), ∇vε(z)−∇v_k(z)).

Strong monotonicity of the SOURCE gradient, not of the perturbed one, and (6.2) imply

    |(x,z)−(X_k(y),Z_k(y))| ≤ C ε^(1/5).               (7.1)

Both pairs stay in the fixed convex product. This is valid at almost every actual contact there. It is a tubular localization of the whole allowed contact relation; it does not prove a single smooth minimizing pair for the moved potential.

There is also a quantitative exceptional-mass estimate. Fix a small tube around the original contact sheets over Q. For triples with x∈Q and y,z∈K, the source slack has a positive minimum κ outside this tube: the set is compact after imposing the uniform separation, and the source describes its exact zero set. Thus

    πε{x∈Q, outside the chosen tube} ≤ 2ε+εD/κ.        (7.2)

The 2ε term pays partners outside K. This estimate remains valid when the original contact support has flat bump boundaries.

## 8. A precise sufficient residual, and why it has not been proved

A sufficient local structural result for full P is now narrower than constructing an all-space contact atlas for the fixed w:

For some sufficiently small ε, the contacts of vε in the fixed tube over Q must admit countably many Borel graph branches H_{j,ε,l}:Q→R³, each injective with a Borel inverse on its image and with

    με(H_{j,ε,l}(S)) < με(S)

for every Borel S⊂Q of positive με-mass. It suffices, for example, to have finitely many C¹ diffeomorphic branches close enough in C¹ to the appropriate original H_j. Smoothness of the fixed densities and the old strict ratio 1/2 then give a uniform ratio≤3/4 on Q after shrinking ε. Such C¹ branch stability has NOT been obtained.

If that residual held, any preserving map T2 agreeing with one of these branches on S would satisfy με(S)≤με(H(S)), a contradiction. A countable union of these selection sets is null. An optimal Monge pair would therefore place all its x∈Q mass in the exceptional event of (7.2), whereas με(Q)≥μ0(Q)/2>0. For ε small enough this contradicts (7.2). This is an integrated sufficient route to the unchanged full P, not a conditional replacement theorem being nominated.

The known estimates do not imply this residual. Uniform C¹-small changes of potentials can destroy strong convexity of the pair minimization. In one scalar coordinate take

    Fδ(t)=λ t²/2 + b δ² cos(t/δ),     b>λ>0.

On a fixed bounded interval Fδ differs from λt²/2 by O(δ²) in value and O(δ) in gradient, with a uniformly bounded second derivative. But Fδ''(0)=λ−b<0, and coercivity plus evenness produce at least two distinct minimizing points near zero (rescale t=δz). Equivalently the changed subtracted potential has a uniformly bounded semiconcavity constant, while the minimum is not unique. This is a scalar inference counterexample, not a Coulomb counterexample to P or to a compatible structural argument.

Likewise C⁰ proximity of maps does not imply pullback density domination: derivatives can oscillate with order-one amplitude. The old exact-CDF cyclic maps in I220 make fine branch selection compatible with exact marginals at arbitrarily small positive excess. They do not establish existence of maps for με, but they explain why a merely small error is insufficient to exclude unrestricted Borel maps. A uniform complexity bound is not part of P and cannot be inserted.

A stronger nonlinear regularity/selection argument might still give the needed domination; failures of naive IFT or factorized smoothing do not rule it out. The local residual and the old fixed-calibration contact-completion problem are two sufficient routes, neither proved necessary for every solution of P.

## 9. Research conclusion

The inverse variational route has been matched to the actual relaxed primary: it is exactly at the binding equality and possesses an explicit singular mass-2/3 relaxed optimizer. The deforming-dual route pays O(ε) calibrated slack, local O(ε) squared-gradient error, interior O(ε^(1/5)) gradient control, source-sheet tubular localization, and O(ε) exceptional mass. These calculations retain the full positive-density class and every Borel map quantifier.

Neither route establishes full nonattainment. The missing step is an exact contact-selection/density-domination mechanism, or an actual smooth positive common marginal on a preserved contact calibration. No viable full theorem has closed, so no new scope is frozen. Supporting estimates are not nominated. Their derivation uses compatible source/classical operations and is not evidence by itself of substantial contribution. No independent grade, acceptance, count, impossibility, current-open, worldwide-priority, or exhaustive-search claim is made.
