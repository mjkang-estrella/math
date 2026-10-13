# I299 independent mathematical proof review

2026-10-13. **Verdict: PASS unchanged for S295.** The user-stipulated OpenAI revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every internal deduction needed below was checked independently; calling an internal lemma accepted in an earlier report supplies no premise for this review.

The target analysis and report match the two supplied frozen hashes. Write L=log 2, V=atanh, H=L−ψ when discussing the source's entropy profiles, and F(ψ(r))=rV(r). All cube norms use uniform probability. Gaussian noise has correlation σ, with OU time −log σ. The target is the arbitrary-kernel, dimension-independent linear stability estimate on exactly the rectangle with ρ₁a₁<1/√2. The review does not enlarge that rectangle.

## 1. Actual stipulated interfaces

The actual pinned family119 main, scalar, canonical, capacity, reserve, thinning, upgrade and flow TeX files were read completely. Fresh immutable raw retrievals match the local bytes. The source contracts actually used are:

1. `main:soft`: arbitrary u∈[-1,1], all finite cube dimensions, contraction at its actual input information.
2. `upgrade:production`: D(g)≥Φ_(Eg)(I(g))≥F(I(g)) for interior g, where Φ_m=max{F,B_m} and

       B_m(I)=2I+(1−m²)S(L−(H(m)−I)/(1−m²)), S=F−2I,

   with the stipulated zero extension of S below zero.
3. `canonical:priced` and `canonical:coverage`: the unique common-budget optimizer is one ordered interior core plus possible equal corners; capacity and the one-corner/reflected geometries include their closed transition.
4. The actual reserve pooling/payment/corner margin, thinning derivative/window margin, deterministic capacity, and low-information wall comparison. These apply at the physical states used below.

The exact energy split is D(g)=Ec(g_+,g_−)+(D(g_+)+D(g_−))/2, with c(x,y)=(x−y)(V(x)−V(y))/4. The stipulated boundary extension is zero at the two equal corners and infinite at other boundary pairs. Its lower semicontinuity is consistent with this extension. The Boolean Hellinger companion was inspected at its main theorem and comparison passage; no soft stability theorem is inferred from it.

## 2. I128 production and original-information bridge

For P_s=T_(e⁻ˢ), y=I(P_su), w=ψ(ae⁻ˢ), z=w−y and R=D(P_su)−F(y), the source gives z,R≥0 at positive time. Direct differentiation gives w′=−F(w), y′=−F(y)−R, hence

    z′=R−Az, A=(F(w)−F(y))/(w−y).

At equality use F′. The source scalar convexity gives 2≤A≤K=max_[0,ψ(a₁)]F′<∞. Therefore

    Δ=∫₀ᵗ exp(−∫ₛᵗA)R(s)ds,
    ∫₀ᵗR≤e^(Kt_max)Δ,
    z(s)≤e^(Kt_max)Δ (0≤s≤t).

The last bound integrates from s to t, discarding nonnegative future surplus. It has the required earlier-time direction. For initial endpoint values, integrate first from η>0; strictly positive finite-cube noise weights make every nonconstant P_ηu interior. Finite-cube continuity gives z(η)→0, and nonnegative improper integration pays the limit. No dimension-uniform interior margin at time zero is required.

For an oriented coordinate with b=E[uεX_i], strong convexity gives

    Eψ(u)−ψ(b)≥½E|u−bεX_i|².

The linear Bregman term averages to zero because V(bεX_i)=εX_iV(b). Orthogonality then gives

    E|u−aεX_i|²≤2[ψ(a)−ψ(b)+ψ(Eu)]+(a−b)².

This also covers b>a; the bracket is nonnegative by the preceding inequality. If ||T_λu−λaεX_i||₂²=q and λ≥ρ₀, constant and singleton coefficients give (Eu)²≤q and |b−a|≤√q/ρ₀. Once |b−a|≤(1−a₁)/2, the derivative bound for ψ and ψ(m)≤Lm² yield exactly

    E|u−aεX_i|²
       ≤2V((1+a₁)/2)√q/ρ₀+2Lq+q/ρ₀².

Thus E131 is an original-budget argument, with its stated square-root loss. It does not invert noise.

## 3. I131 compression and local coercivity

### Compression

Sorting a coordinate fiber replaces b+X_i d by b+X_i|d|. It preserves the full value multiset, mean, second moment and input information. It preserves other singleton coefficients because each other X_j is constant on the sorted fiber. It preserves previous coordinate monotonicity: min and max of two ordered pairs remain ordered. After all coordinates are sorted the function is increasing.

For the noisy outside variables, put B=T_ρb, D=T_ρd and D_+=T_ρ|d|. Positivity gives |D|≤D_+. The even function f_B(q)=[ψ(B+ρq)+ψ(B−ρq)]/2 has f_B′(0)=0 and f_B″≥ρ² on the relevant interval. Its arguments stay in [-1,1] because the sorted and unsorted kernels, and intermediate q between these magnitudes, are bounded there. Consequently the information gain in this sort is at least (ρ²/2)E(D_+²−D²), including endpoints by continuity.

Choose i maximizing c=ĝ(i). Just before sorting i, Ed is the original singleton b_i and E|d|=c; subsequent sorts preserve c. For M=Eu²,

    E D_+²−E D²
       ≥(1−ρ²)(c²−b_i²)−ρ²(M−c²).

This follows from E D_+²≥c², E D²≤b_i²+ρ²(Ed²−b_i²), and Ed²≤M. It yields Q131. Also d_a(g)=M+a²−2ac=(M−c²)+(a−c)². If d_a(g)≤a²/4, then c≥a/2 and

    d_a(u)−d_a(g)
       ≤2a(c−|b_i|)≤4(c²−b_i²).

Substitution gives precisely the constants in Q131b. In the complementary case d_a(u)≤4≤16d_a(g)/a₀². Thus the displayed C_comp is uniform in n and all unregulated kernel features. The identity Δ(u)=Δ(g)+L_gain follows from exact input information and nonnegative sorting gain.

### Spike-tolerant local L2 estimate

For v=aX₁, h=u−v, m=Eh and k=ρV(ρa)/V(a), the constrained functional has the exact identity

    G=k E Bψ(v+h,v)−E Bψ(ρv+T_ρh,ρv)+(1−k)ψ(m).

First variations cancel. The original Hessian is

    Q(h)=k[Eh²/(1−a²)−m²]
             −[E(T_ρh)²/(1−ρ²a²)−m²].

Every nonconstant Walsh coefficient is at least q=k/(1−a²)−ρ²/(1−ρ²a²), and the constant coefficient is a²q. The decreasing function (1−t²)V(t)/t proves q>0; 0<k≤ρ²<1. Scalar compactness yields the original positive c*=a₀²min q.

The L131 split h=g+b uses disjoint supports, with |g|≤η and b supported on a set of probability p≤||h||₂²/η². On the good set Taylor costs at most D₃η||g||₂²/6; on the bad set global strong convexity pays k_min||b||₂²/2. This holds at input endpoints by continuity, without differentiating ψ there.

The output expansion is around |ρv|≤ρ₁a₁<1, so the scalar bound |remainder|≤C_out|T_ρh|^q for q=min{3,1+ρ₁⁻²}>2 is finite even when the perturbed output reaches an endpoint. Near zero it is a uniform interior Taylor estimate; away from zero it uses bounded continuous ψ. Hypercontractivity gives its integral at most C_out||h||₂^q.

The real two-point norm estimate used here can be verified independently. For 1<p≤2 let M(t)=E|A+tBX|^p and f=M^(2/p), X a fair sign. Where no component vanishes,

    f″=2(2−p)M^(2/p−2)(E|A+tBX|^(p−2)(A+tBX)BX)²
       +2(p−1)B²M^(2/p−1)E|A+tBX|^(p−2)
       ≥2(p−1)B².

The last inequality is Jensen for the negative power of |A+tBX|^p. Continuity and locally integrable second derivatives extend it across zeros for p>1. Since f′(0)=0, integration gives ||A+BX||_p²≥A²+(p−1)B². Tensorization with Minkowski gives Lp→L2, and duality gives L2→Lq; composing these proves the needed norm bounds. Thus no Boolean identity is being substituted for real-function hypercontractivity.

In particular ||T_ρb||₂≤p^θ||b||₂, θ=1/(1+ρ₁²)−1/2>0. The good quadratic terms, including (1−k)(Eg)²/2, equal Q(g)/2. The bad output square costs at most B_max p^(2θ)||b||₂²/2. Output and mean cross terms cost at most [B_max p^θ+√p]||g||₂||b||₂. The displayed Young bound consumes at most c*||g||₂²/8 and the stated bad coefficient. Choosing p_* and then ε_* exactly as in L131 leaves

    G≥c₁(||g||₂²+||b||₂²)−C_out||h||₂^q
       ≥(c₁/2)||h||₂².

On the exact information surface G=Δ. All constants use only the endpoints; the split is a proof decomposition and changes neither kernel nor budget. This checks L131 unchanged, including arbitrary bias, rare large spikes and ±1 values.

## 4. J290 joining rigidity, M290 and P290

Suppose a pair law μ of (A,B) has Ec<∞ and δ=(EA−EB)/2>0. If EH(A)=0, A is an endpoint almost surely; finite cost forces B=A almost surely, contradicting δ>0. The same holds for B. An endpoint mean likewise forces equality of the two variables. Thus child entropy moments are positive, both means are interior, and all source profiles are physical, even when μ has mass at equal corners. Entropy concavity gives the common-budget constraint used by the canonical optimizer.

Let

    J=Ec+½[Φ_(EA)(I_A)+Φ_(EB)(I_B)]−Φ_m(I).

The stipulated joining theorem gives J≥0. The independent equality extraction is as follows.

### Reserve parent, including ties

Original-child reserve pooling gives J≥Ec−W(parent)≥K−W(parent). Let the canonical core have mass k>0, half separation δ_c, and corner masses π_+,π_−; δ=kδ_c. Write c₀=2−4L²>0. On either common-corner ray, the actual reserve Euler margin is

    τW′−W≥c₀κ_τ≥(c₀/8)τ²δ_c².

Integrating (W/τ)′ gives loss at least (c₀/8)τ(1−τ)δ_c². Compose retentions τ₁=k/(k+π_+) and τ₂=k+π_+. The second ray uses separation τ₁δ_c. Keeping both losses gives

    kW(core)−W(parent)
       ≥(c₀/8)δ_c²[kπ_++k²π_−]/(k+π_+)
       ≥(c₀/8)(1−k)δ².

The two retentions are positive, with value one for a missing corner. There is no division by a possibly small separation. Since K≥kW(core), J=0 forces k=1.

The deterministic core then has information J_c>0 and variance capacity α_c=1−m_c². If m_c≠0, the positive ψ series gives c_(m_c)=Lm_c²−ψ(m_c)>0. Hence L−e_c/α_c=J_c/α_c−c_(m_c)/α_c is strictly below the positive number J_c/α_c<L. The source's S is strictly increasing on positive arguments and zero below zero, so

    W(core)<α_cF(J_c/α_c)≤c(x,y).

Equality therefore forces m_c=0. Moreover J=0 forces Ec=K. Because the actual law has the same means and exact common entropy e, equality in priced optimality forces it to be the unique canonical optimizer. At capacity price zero, the same uniqueness applies. Thus the actual law is the point mass (r,−r), 0<r<1.

### Strict F parent

Mean zero is impossible because B_0=F. Reflect signs and orient children so m>0. The source's original-child pooling gives J≥Ec−[F(I)−F(j)]≥K−[F(I)−F(j)]. Such a parent has I<L/2.

In the one-positive-corner geometry the core center is nonnegative. The actual thinning derivative and window margin, integrated just as above, give

    kF(J_c)−[F(I)−F(j)]
       ≥(c₀/8)k(1−k)δ_c².

For k<1 this is strictly positive; K≥kF(J_c). For k=1 the core has center m>0 and α_c<1, so strict convexity of F and the deterministic capacity bound give c≥α_cF(J_c/α_c)>F(J_c). The positive separation gives J_c>0, so strict convexity is applicable.

In the reflected-core geometry m>0 implies k<1. Moving the common mean to the one-corner wall holds k, δ, entropy and cost fixed. Information decreases from a value below L/2, and the path is physical, so the stipulated wall monotonicity bounds the original demand by the wall demand. The wall's thinning loss is strictly positive, including the transition and a zero-length wall motion. Thus J cannot vanish in the strict F branch.

Conversely, for a deterministic reflected interior pair the two child informations are zero, Φ_0=F, and c=rV(r)=F(ψ(r)); J=0. This checks J290's complete equality classification, including ties, capacity, equal-corner mass and the strict-parent endpoint cases.

### Fixed-square compactness and production entrance

For δ≥b>0, j₀≤I≤j₁<L, and Ec≤M, probability laws on the fixed square form a weakly compact set. The cost is nonnegative lower semicontinuous, so its integral sublevel is closed. Means and entropy moments are continuous. Within this compact set, the preceding finite-cost argument excludes zero child entropies and endpoint means; their distances from these excluded sets consequently have positive uniform lower bounds.

The resulting profile arguments lie inside a compact physical domain: entropy lower bounds keep the reserve arguments below L, and child information zero, branch ties and the reserve seam are allowed by continuity. Hence J is lower semicontinuous. The distance

    ½E[(A−r)²+(B+r)²], r=ψ⁻¹(I),

is continuous. The closed set on which this distance is at least ε is compact. J290 excludes J=0 there, so its minimum is positive. This is M290; an empty set causes no problem. It involves pair laws on one fixed square, not growing cubes.

For interior g split at the specified marked coordinate, the exact energy identity gives

    R(g)=½Σ_±[D(g_±)−Φ_(Eg_±)(I(g_±))]
            +J(μ)+Φ_(Eg)(I(g))−F(I(g))≥J(μ).

Each face is interior, including dimension-zero constant faces. Also Ec≤D(g)≤F(j₁)+1 when R≤1. The face-law separation is the oriented singleton. M290 therefore yields P290 with a dimension-independent tolerance at that specified coordinate. No selection of a different coordinate or hidden initial proximity is used.

## 5. B290: global marked-sector linear stability

For fixed β>0, choose an original marked singleton ≥β. The ODE bounds in §2 pay both the total production surplus and all earlier deficits. For sufficiently small terminal Δ, all intermediate informations lie in [ψ(ρ₀a₀)/2,ψ(a₁)]. A time in the middle third of [0,t] has

    R(s)≤3e^(Kt_max)Δ/t_min,

where t_min=−logρ₁>0. At that time the marked singleton is e⁻ˢβ≥ρ₀β, and the smoothed input is interior. P290 puts it arbitrarily close to εψ⁻¹(I(P_su))X_i once Δ is small enough. On this positive compact information interval ψ⁻¹ is Lipschitz, so its amplitude differs from ae⁻ˢ by O(Δ).

The original-budget estimate in §2 consequently puts the unsmoothed input in the L131 neighborhood. Choose that neighborhood tolerance first, then the P290 tolerance and terminal-deficit threshold. L131 gives linear stability at the original u. Above the fixed positive threshold, d_a≤4 pays the bound. This proves B290 with constants depending only on β and the endpoint rectangle. The order of tolerances makes its initial-closeness premise fully paid, including original endpoint values and spikes.

## 6. R295, E295 and the Gaussian gap

### Exact-law rearrangement

The operative primary Borell proof was read in Mossel–Neeman 1210.4126v3, complete §2 with its theorem statements. Independently, for J(p,q)=Pr_σ(Z≤Φ⁻¹(p),W≤Φ⁻¹(q)), α=Φ⁻¹(p), β=Φ⁻¹(q) and bivariate density k,

    J_pp=−σk/φ(α)², J_qq=−σk/φ(β)²,
    J_pq=k/[φ(α)φ(β)].

Using the correlated joint OU generator, stationarity and the chain rule gives R′(t)=σE k|∇Φ⁻¹(f_t)(X)−∇Φ⁻¹(g_t)(Y)|²≥0. For ε-interior f,g and positive time derivatives are integrable. Start at positive δ and use strong continuity at zero, convergence to constants at infinity, then let ε↓0 by bounded continuity of J. This proves the needed two-set inequality despite the identified presentational swaps in the source HTML. The target already gives this correct calculation; the review makes no repair to it.

For f=(1+v)/2, f*=F_f⁻¹(Φ(z)) has exactly its law, including atoms. Level sets are nested upper rays up to null sets, including full and empty sets. Layer cake and Borell bound ∫_A Q_σf by ∫_(A*)Q_σf* for every measure p and every A of that measure. The same upper ray A* is used at every level; its input comparison rays are the actual level sets of f*. Thus the comparisons are compatible. Q_σf* is increasing by coupling, so A* attains its largest-p integral.

The identity E(W−c)_+=sup_p[M_W(p)−cp] follows by taking {W>c}, with nonatomic tie splitting if needed. Top-integral domination therefore gives all stop-loss inequalities. Equal means and convex piecewise-linear approximation yield convex order. Applying the continuous convex function ψ(2x−1) proves R295, with the input law and mean preserved exactly.

### Scalar conditional EPI

Rioul's primary EPI setup, transport/rotation proof and equality argument were read. In the application, generate B from w(Z) and choose Z′ independent of (Z,B). For p_±=(1±m)/2>0,

    q_±=φ(1±w)/(1±m)=φr_±, 0≤r_±≤1/p_±.

Gaussian domination pays second moments. The function r log r is bounded in absolute value on this interval, with its zero extension; E_q|log φ| is finite. Hence each differential entropy is finite, also at kernel endpoints. The output posteriors have the identical domination property. If input information is zero, strict convexity makes w constant and the result is immediate; positive information ensures both probabilities are positive.

Apply ordinary scalar EPI separately given B. Conditional independence is valid by construction. For h₀=½log(2πe), the scalar function

    h↦½log[σ²e^(2h)+(1−σ²)e^(2h₀)]

is convex, with second derivative 2AC/(A+C)²>0. Thus averaging the EPI lower bounds and Jensen lower-bound conditional output entropy. Subtracting from h₀ gives exactly

    I_G(Q_σw)≤−½log(1−σ²+σ²e^(−2I_G(w))).

All entropy differences are finite and the bias probabilities are the actual ones. R295 is applied before EPI; no N-dimensional exponent is silently made scalar. The optional strict-EPI argument also checks: preliminary smoothing gives positive continuous posteriors; a positive mixture of two Gaussian densities, each bounded above by a finite multiple of φ, can equal φ only when both components equal φ. That would force zero information. The scalar EPI equality condition and the composition identity for B_σ give the stated strictness below the EPI curve. This is not used to fill a cube-curve reserve at large amplitude.

### Curvature and uniform constants

Now use H_*(x)=exp(−2ψ(√x)), to distinguish it from binary entropy H. Direct differentiation gives

    H_*″/H_* = V(r)²/r²−[r/(1−r²)−V(r)]/(2r³), r=√x.

The series V(r)≥r and r/(1−r²)−V(r)≤r³/(1−r²) give H_*″/H_*≥1−1/[2(1−x)]. The expressions extend at zero. For b₁<1/√2 the stated κ is a positive lower bound for H_*″ on [0,b₁²]. Strong convexity gives A−H_*(σ²b²)≥κσ²(1−σ²)b⁴/2, with A=1−σ²+σ²H_*(b²)≤1. Since log(A/H_*)≥(A−H_*)/A, the target's factor κ/4 and uniform η_G are correct. R295 and E295 therefore give G295-small for every finite Gaussian dimension and arbitrary bounded kernel of exact positive information in the stated compact ranges.

## 7. Unequal split and fixed-degree transfer

The strict rectangle condition makes (ρ₁,min{1,1/(√2a₁)}) nonempty. Choose a fixed λ there. Then σ=ρ/λ lies in a compact subinterval of (0,1), and λa lies in a compact positive interval strictly below 1/√2. A slightly larger interval absorbs information approximation. At s=−logλ the ODE earlier-time bound pays I(T_λu) near ψ(λa) when terminal Δ tends to zero; the semigroup identity pays the second budget at σ. The ordering 0<s<−logρ is correct.

For increasing diffuse u_k, let α_k=max_i û_k(i)→0, h_k=T_λu_k, p_k its degree-d truncation, q_k=T_(σ_k)p_k and v_k=clip(p_k) on Gaussian space. Walsh and multilinear Gaussian monomials have the same orthogonal second moments. Thus Ep_k²≤1 on either space and the cube squared tail is at most λ^(2(d+1)). Multilinearity gives Q_(σ_k)p_k=q_k exactly. No relation σ_k=λ is required.

Monotonicity and range give 0≤∂_ih_k≤1. Hence the genuine L2 influence satisfies Inf_i(p_k)≤E(∂_ih_k)²≤E∂_ih_k=λû_k(i)≤α_k. Also Σ_iInf_i(p_k)≤dEp_k²≤d. Noise decreases these bounds for q_k.

Here is the independent fixed-degree replacement check. Write a polynomial as A+x_iB and replace a bit by a standard Gaussian. Their first three moments match, so fourth-order Taylor remainder is bounded by a constant times ||test⁽⁴⁾||∞ EB⁴. On any mixed bit/Gaussian product, the one-variable estimate

    E(A+XB/√3)⁴=A⁴+2A²B²+(EX⁴/9)B⁴≤(A²+B²)²

holds. Iteration and Minkowski give ||T_(1/√3)p||₄≤||p||₂ for multilinear polynomials. Undoing the degree weights gives EB⁴≤9^(d−1)(Inf_i p)². Summing replacements costs at most C_d||test⁽⁴⁾||∞Σ_iInf_i(p)²≤C_d d||test⁽⁴⁾||∞α_k→0. This proves the displayed invariance assertion independently; a theorem name alone is not a premise.

The bounded uniformly continuous tests clip and ψ∘clip admit smooth uniform approximations with bounded fourth derivative. The unbounded squared-distance test f(x)=dist(x,[-1,1])² is also paid: a compactly supported mollification at radius τ has bounded fourth derivative, and |f_τ−f|≤Cτ(1+|x|)+Cτ². The identical second-moment bound on both spaces controls this approximation error. First fix d and τ, then send k large, and finally τ small. No bounded-test claim is incorrectly applied to f.

On the cube f(p_k)≤|p_k−h_k|². Transfer therefore gives ||v_k−p_k||²_(2,G)≤λ^(2(d+1))+o_k(1). Projection onto [-1,1] is nonexpansive relative to any value in that interval, and Gaussian noise is an L2 contraction, so

    ||Q_(σ_k)v_k−clip(q_k)||_(2,G)≤||v_k−p_k||_(2,G).

The corresponding clipped cube fields are close to h_k and T_(σ_k)h_k. For bounded fields, splitting at a fixed pointwise error threshold δ bounds entropy errors by the modulus of continuity of ψ plus L times squared L2 error divided by δ². Means are paid by L2 and the same scalar continuity. Consequently, for every ζ>0, choose d depending on ζ and the fixed λ, then take k sufficiently large, to transfer both informations with error <ζ. This order allows unbounded original degrees and dimensions.

Define b_k=ψ⁻¹(I_G(v_k)). This enforces exact information without rescaling v_k. Uniform continuity of ψ(σψ⁻¹(J)) on the chosen compact domain pays the comparison to ψ(ρ_ka_k). Choose ζ small relative to the fixed η_G, then let k large. The two transfer errors, the ODE error and this scalar comparison total <η_G/2. Applying G295-small contradicts terminal Δ_k→0. Thus an increasing diffuse sequence of vanishing deficit is impossible.

## 8. Quantifiers, arbitrary-kernel transfer and boundaries

If there were no β,η>0 with a diffuse deficit gap, choosing β=η=1/k would give exactly the forbidden sequence. Hence some β,η, depending only on the endpoints, satisfy max singleton≤β ⇒ Δ≥η for increasing exact-information kernels. In this sector d_a≤4 pays linear stability. B290 pays the complementary sector with its fixed β. Q131b then gives

    d_a(u)≤C_comp[d_a(g)+L_gain]
       ≤C_comp max{C_inc,1}Δ(u).

Every constant is chosen from endpoint-dependent compact scalar ranges, fixed-square law compactness, or a fixed smoothing λ. None depends on dimension, bias, corner/spike masses, support, rank or uncontrolled degree. Degree appears only temporarily in the contradiction argument, fixed before the diffuse limit.

For Δ=0 the diffuse gap rules out the diffuse sector, and B290 plus compression give d_a=0. The zero-surplus time selection and local bound permit equality; there is no division by Δ. The same proof includes n=1, with dimension-zero faces in the energy split. Closed parameter endpoints a₀,a₁,ρ₀,ρ₁ cause no loss because their ranges are compact and λ is chosen with a strict margin. Finite cubes need no smoothness of u. Gaussian inputs may be merely measurable and attain endpoints; their rearrangement, posterior entropy and clipping passages remain valid.

The scalar monotone compactness statement in I295 is also valid: diagonal selection on rational points gives a monotone limit at its continuity points, and bounded dominated convergence gives Gaussian L2 convergence. Hermite expansion proves joint continuity of OU with the correlation parameter; entropy is continuous on bounded L2 fields. Exact positive information constraints define a compact feasible set, so pointwise cube-curve strictness, if available, would yield a uniform gap there. The non-strict Gaussian cube curve follows from the displayed conditional block-sum argument: conditional input bits have means σY_i, variance 1−σ² and uniform third-moment control, so smooth replacement gives a conditional-mean error O(M⁻¹/²) at fixed Gaussian dimension. Output block sums converge to Gaussians, and entropy/mean continuity and bounded smooth approximation pay the limit. A bare joint CLT is not used to infer conditional entropy convergence.

The high-amplitude boundary is honest. H_*′(x)→−∞ near one, so some EPI chords lie below H_*(σ²x); the EPI upper curve then exceeds the cube upper curve. A strict EPI reserve need not dominate that difference. Equality propagation to earlier times is valid by non-strict contraction; later analytic continuation is not proved or invoked. The inspected Proposition 8 statement indeed adds complex conditions beyond tails. No analytic theorem or ordinary LSI nonattainment is used to pass S295.

The added calculations here explain existing valid steps; they are not substantive repairs. **S295 passes unchanged; full all-rectangle S128 is not passed.** Contribution, priority and acceptance are outside this review.
