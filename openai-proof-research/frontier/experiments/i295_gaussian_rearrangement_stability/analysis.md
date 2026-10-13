# I295: Gaussian rearrangement and a restricted global S128 theorem

2026-10-13. The proved result is unrestricted in the kernel and dimension, but restricted in the parameter rectangle: **ρ₁a₁<1/√2**. Full S128 on all compact rectangles remains open here. No acceptance or worldwide-priority claim is made. The current count, updated by the user during this assignment, is 13/20; this work changes no counts or frozen inputs.

All OpenAI theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. I290 is used at the exact scope of its completed, authenticated proofs, not as a proof of its unpaid G290. The parent I295 note supplies leads, each verified below. Natural logarithms are used throughout.

## 1. Notation, dependencies, and the precise result

Put L=log 2,

    ψ(t)=((1+t)log(1+t)+(1−t)log(1−t))/2,
    I(u)=Eψ(u)−ψ(Eu),
    d_a(u)=min_(i,ε∈{−1,1}) E|u−εaX_i|²,
    Δ_ρ(u)=ψ(ρa)−I(T_ρu),

where X is uniform on {−1,1}^n and I(u)=ψ(a). On standard Gaussian space γ_N define

    I_G(v)=E_Gψ(v)−ψ(E_Gv),
    Q_σv(z)=E[v(σz+√(1−σ²)Z′)].

**S295 (proved, restricted parameter theorem).** Given

    0<a₀≤a₁<1, 0<ρ₀≤ρ₁<1, ρ₁a₁<1/√2,

there is C<∞ depending only on these four endpoints such that, for every n≥1, every measurable cube kernel u:{−1,1}^n→[−1,1], every a∈[a₀,a₁] and ρ∈[ρ₀,ρ₁] with exactly I(u)=ψ(a),

    d_a(u)≤C Δ_ρ(u).                                      (S295)

There is no balance, monotonicity, initial closeness, endpoint exclusion, singleton lower bound, or complexity hypothesis in this theorem. Constants are existential, dimension independent; no effective numerical value is claimed.

The pinned sharp soft contraction is `main:soft` in the actual family119 main TeX; positive-time production and integration are `upgrade:production` and `flow:sharp-trajectory`. The companion's `thm:main` concerns Boolean Hellinger contraction, not this soft stability statement. The previous project dependencies are I128 P128/E128, I131 L131/Q131b/E131, and I290 B290/D290 plus its fixed-degree transfer calculation. These contracts are inspected explicitly in the authentication record. In particular:

* B290 pays global linear stability whenever max_i|û(i)|≥β, for every fixed β>0, allowing all other coordinates and all bias.
* Q131b sorts coordinate fibers to an increasing g, preserving the input law and information, and gives Δ(u)=Δ(g)+L_gain and d_a(u)≤C_comp[d_a(g)+L_gain].
* The I290 Lindeberg argument transfers both information budgets after fixed positive smoothing, with clipping and mean errors paid. Its original half-time split is replaced, and rechecked, in §5.

Sections 2–4 supply the Gaussian gap at small amplitude. Section 5 proves S295. Section 6 pays compact one-dimensional optimization and isolates precisely the remaining large-amplitude strictness problem.

## 2. Borell implies an exact law-preserving one-dimensional reduction

### 2.1 Primary proof verification and normalization

The primary source actually read is Mossel–Neeman, `1210.4126v3`, Theorems 1.1–1.2 and the complete §2 proof of Borell's theorem. It is a primary semigroup reproof of Borell's two-set inequality; the original 1985 article is credited but not claimed newly read. The theorem has two arbitrary measurable sets, standard Gaussian marginals, cross covariance σ Id, and 0<σ<1. The comparison sets are parallel halfspaces with the same orientation. Reflection allows either lower or upper halfspaces.

Here is a direct verification of the operative calculation, including the endpoints needed for layer cake. Write J(p,q)=Pr(Z≤Φ⁻¹(p),W≤Φ⁻¹(q)), corr(Z,W)=σ. If α=Φ⁻¹(p), β=Φ⁻¹(q), and k is the bivariate density at (α,β), direct differentiation gives

    J_pp=−σ k/φ(α)², J_qq=−σ k/φ(β)²,
    J_pq=k/[φ(α)φ(β)].

For f,g in [ε,1−ε], let f_t=Q_(e⁻ᵗ)f, g_t=Q_(e⁻ᵗ)g and R(t)=E_σ J(f_t(X),g_t(Y)). The joint OU generator is

    ℒ_joint=Δ_x+Δ_y+2σΣ_i ∂_(x_i)∂_(y_i)−x·∇_x−y·∇_y.

Its expectation vanishes under the correlated Gaussian law. Applying the chain rule and subtracting Eℒ_joint J therefore gives

    R′(t)=σ E_σ k |∇Φ⁻¹(f_t)(X)−∇Φ⁻¹(g_t)(Y)|²≥0.   (1)

For t>0 smoothing and the ε interior bound justify the derivatives and integration by parts; one may first integrate from δ>0. Strong L2 continuity at zero and convergence to constants at infinity give

    E_σ J(f(X),g(Y))≤J(Ef,Eg).

Apply this first to ε+(1−2ε)f and ε+(1−2ε)g, then let ε↓0. Continuity and boundedness of J on the closed square pay the limit for all bounded measurable f,g. With indicators J equals their product, proving the exact two-set bound used below. The primary HTML has typographical swaps in an introductory endpoint sentence and intermediate Gaussian factors; (1) is independently checked by the Hessian above rather than using those swaps.

### 2.2 Layer cake, top integrals, and convex order

Let v:R^N→[−1,1] be arbitrary, and f=(1+v)/2. On γ_1 define f* by the increasing quantile of the law of f: f*(z)=F_f⁻¹(Φ(z)), with any usual generalized inverse. Then f* has the full law of f, including atoms. For almost every t∈[0,1], {f*>t} is an upper halfspace of Gaussian measure γ_N(f>t). Empty and full sets are allowed. Set v*=2f*−1.

For any output set A of Gaussian measure p, Tonelli and the Gaussian conditional law give

    ∫_A Q_σ f dγ_N
      =∫₀¹ Pr_σ(Y∈A, f(X)>t)dt
      ≤∫₀¹ Pr_σ(Y∈A*, f*(X)>t)dt
      =∫_(A*) Q_σ f* dγ_1,                            (2)

where A* is the upper ray of measure p. Borell applies separately at every t; all of its comparison input rays are already the nested level sets of this same f*. Thus the optimizers are compatible across t. There is no optimization over a different f for each level. Dimension one rays can equivalently be embedded in R^N.

Q_σ f* is nondecreasing: coupling σz+√(1−σ²)Z′ for ordered z proves it. Hence its largest-p integral is attained by A*. On the nonatomic Gaussian space define M_W(p)=sup_(γ(A)=p)∫_A W dγ. Equation (2) says M_(Qf)(p)≤M_(Qf*)(p) for all p∈[0,1]. For every real c,

    E(W−c)_+=sup_(0≤p≤1)[M_W(p)−cp].

The upper bound follows by restricting W−c to a set; the reverse follows by taking {W>c}, with arbitrary portions of ties if needed. Consequently all stop-loss expectations for Qf are bounded by those for Qf*. Their means coincide. Every continuous convex function on [0,1] is a uniform limit of convex piecewise-linear functions, each an affine function plus a nonnegative sum of (x−c)_+. This proves

    Q_σ f≤_cx Q_σ f*.

Apply it to x↦ψ(2x−1). The full input law, mean, and information are preserved, and output means are preserved as well. Thus

    I_G(v*)=I_G(v),
    I_G(Q_σv)≤I_G(Q_σv*).                              (R295)

This is classical Gaussian rearrangement machinery derived from Borell; it is not claimed as a new rearrangement theorem. It applies to arbitrary soft kernels and arbitrary bias, not only Boolean sets or fixed-mean extremization.

## 3. Scalar conditional EPI: exact information and endpoint hypotheses

Let w:R→[−1,1], m=Ew(Z), and, conditional on Z, sample a sign B with Pr(B=±1|Z)=(1±w(Z))/2. Let Y=σZ+√(1−σ²)Z′ with Z′ independent of (Z,B). Then

    I(B;Z)=I_G(w), I(B;Y)=I_G(Q_σw).

No fair-output assumption is made. If I_G(w)>0 then p_±=(1±m)/2 are both positive. The scalar posterior densities are

    q_±(z)=φ(z)(1±w(z))/(1±m)≤φ(z)/p_±.             (3)

They have finite second moments and finite real differential entropies, even if w takes endpoint values. Indeed q=φr, 0≤r≤1/p: E_q|log φ| is finite, and ∫φ r log r is finite because r log r extends continuously at zero and is bounded on this compact interval. The same argument applies to Y|B, whose density is also at most φ/p. Thus all following entropy differences and conditional averages are finite. A compact positive lower information bound also forces p_± uniformly away from zero, since I_G(w)≤L−ψ(m).

The actual primary EPI proof read is Rioul's published 2017 author-hosted paper: its entropy/regularization discussion, change-of-variable lemma, complete transport-and-rotation proof, and equality argument. It proves ordinary EPI, not an unexamined conditional formula. In dimension one its normalization is

    exp(2h(U+V))≥exp(2h(U))+exp(2h(V))

for independent variables with densities and finite second moments. Equivalently N(U)=exp(2h(U))/(2πe). The factor cancels below. Scaling gives h(cU)=h(U)+log|c|. The log form in the paper yields the displayed form by optimizing its weight after scaling U and V; the optimum weight is exp(2h(U))/(exp(2h(U))+exp(2h(V))).

Apply ordinary EPI separately given B=s. Conditional independence is valid because Z′ was chosen independent of (Z,B). With h₀=h(Z)=½log(2πe),

    h(Y|B=s)≥½log[σ² exp(2h(Z|B=s))+(1−σ²)exp(2h₀)].

The function h↦½log[σ²e^(2h)+(1−σ²)e^(2h₀)] is convex (a direct second derivative is positive). Jensen therefore supplies a **lower** bound after averaging these posterior entropies:

    h(Y|B)≥½log[σ² exp(2h(Z|B))+(1−σ²)exp(2h₀)].

Since h(Z|B)=h₀−I(B;Z), and Y is standard Gaussian,

    I_G(Q_σw)≤B_σ(I_G(w)),
    B_σ(J):=−½log(1−σ²+σ²e^(−2J)).                 (E295)

Combining R295 and E295 proves this bound for all Gaussian dimensions and kernels. **Dimension reduction comes first.** Direct N-dimensional conditional EPI would instead give −(N/2)log(1−σ²+σ²e^(−2J/N)); it does not give (E295) without rearrangement.

There is also pointwise strictness in E295 at positive information, at every finite σ∈(0,1). To avoid importing equality through a nonsmooth limit, choose τ∈(σ,1) and put w₁=Q_τw. This field is smooth and strictly between the endpoints at every finite argument. It has positive information: OU is injective on L2, by its positive Hermite eigenvalues. Its posterior densities are positive, continuous, and satisfy (3).

If both posterior densities were Gaussian, (3) would imply their variances are at most 1; a variance-1 posterior must have mean zero. In a mixture equal to φ, every variance-less-than-1 summand divided by φ tends to zero in both tails, whereas each variance-1 summand equals φ. A positive mixture with a variance-less-than-1 term could therefore not have ratio 1 in the tails. Both posteriors must equal φ, forcing w₁ constant, a contradiction. At least one posterior is non-Gaussian. The positive-density EPI equality argument is consequently strict for that posterior and Gaussian Z′. Weighted averaging remains strict. B_r is increasing and B_r(B_τ(J))=B_(rτ)(J). Taking r=σ/τ yields

    I_G(Q_σw)<B_(σ/τ)(I_G(w₁))≤B_σ(I_G(w)).       (4)

This strictness is below the EPI curve, not automatically below the smaller cube curve at every amplitude.

## 4. Algebraically paid Gaussian gap for b<1/√2

Set x=b², r=√x, E(x)=ψ(√x), H(x)=exp(−2E(x)); H(0)=1. Differentiation gives E′=atanh(r)/(2r) and

    H″/H=atanh(r)²/r²
          −[r/(1−r²)−atanh(r)]/(2r³).            (5)

All expressions extend continuously at zero. The positive series gives atanh(r)≥r and

    r/(1−r²)−atanh(r)
      =Σ_(k≥1) [2k/(2k+1)]r^(2k+1)
      ≤r³/(1−r²).

Thus H″/H≥1−1/[2(1−x)]>0 for 0≤x<1/2. This verifies the parent calculation independently, including the derivative factors and the series direction.

Fix 0<b₀≤b₁<1/√2 and 0<σ₀≤σ₁<1. On [0,b₁²] one can take

    κ=exp(−2ψ(b₁)) [1−1/(2(1−b₁²))]>0

as a lower bound for H″. The strong-convexity chord estimate at θ=σ² gives

    A−H(θx)≥(κ/2)θ(1−θ)x²,
    A=(1−θ)H(0)+θH(x)≤1.

Since log(A/H(θx))≥(A−H(θx))/A,

    ψ(σb)−B_σ(ψ(b))
       =½log[A/H(θx)]
       ≥(κ/4)σ²(1−σ²)b⁴
       ≥η_G:=(κ/4)σ₀²(1−σ₁²)b₀⁴>0.            (6)

Consequently, for every finite N and every Gaussian kernel v with exactly I_G(v)=ψ(b) in the stated compact ranges,

    I_G(Q_σv)≤ψ(σb)−η_G.                          (G295-small)

This is the full uniform G290 obligation on those amplitude ranges. It is not mere nonattainment, requires no Gaussian equality theorem, and covers bias and endpoint values. The explicit constant is a lower bound, not an optimal one.

## 5. Unequal split and the complete arbitrary-kernel proof of S295

Choose once and for all

    ρ₁<λ<min{1,1/(√2 a₁)}.

The interval is nonempty by the strict assumption ρ₁a₁<1/√2. Now σ=ρ/λ belongs to [ρ₀/λ,ρ₁/λ]⊂(0,1), λ<1 is fixed, and λa lies in the compact interval [λa₀,λa₁]⊂(0,1/√2). Choose a slightly larger compact b interval still below 1/√2, to absorb the Gaussian input-information approximation.

### 5.1 The information at the split is paid by the original deficit

For any cube u in the model put P_s=T_(e⁻ˢ), t=−logρ, y(s)=I(P_su), w(s)=ψ(ae⁻ˢ), z=w−y, and R(s)=D(P_su)−F(y(s)), where F(ψ(r))=r atanh(r). The pinned contraction and production give z,R≥0, and P128 gives

    z′=R−A(s)z, 2≤A(s)≤K=max_[0,ψ(a₁)]F′.

Integrating from any s≤t and dropping nonnegative future production yields

    0≤z(s)≤exp(Kt_max)Δ_ρ(u), t_max=−logρ₀.      (7)

At s=−logλ we have 0<s<t because λ>ρ₁≥ρ. Consequently, for any increasing sequence u_k with Δ_(ρ_k)(u_k)→0, h_k=T_λu_k satisfies

    I(h_k)−ψ(λa_k)→0,
    I(T_(σ_k)h_k)−ψ(ρ_ka_k)→0.                  (8)

The integrating factor is used toward an earlier time. No conclusion from a small earlier deficit to an arbitrary later one is presumed. For inputs attaining endpoints, P128 integrates first from positive time and then uses finite-cube continuity; no dimension-uniform L∞ interior bound is used.

### 5.2 Diffuse increasing kernels transfer at this unequal split

Suppose additionally α_k=max_i û_k(i)→0. For a fixed degree d, let p_k be the degree-≤d Walsh truncation of h_k, also regarded as the same multilinear Gaussian polynomial; let q_k=T_(σ_k)p_k and v_k=clip(p_k,−1,1) on Gaussian space. Multilinearity makes q_k=Q_(σ_k)p_k exactly, even though σ_k differs from λ.

Parseval and 0<λ<1 give uniformly

    ||h_k−p_k||₂²≤λ^(2(d+1)),
    ||T_(σ_k)h_k−q_k||₂²≤λ^(2(d+1)), E p_k²≤1. (9)

For ∂_i h=(h|_(X_i=1)−h|_(X_i=−1))/2, monotonicity and boundedness give 0≤∂_ih≤1. Therefore the actual polynomial L2 influences satisfy

    Inf_i(p_k)≤E(∂_ih_k)²≤E∂_ih_k
                 =λ û_k(i)≤α_k.                (10)

No Boolean identity is used. q_k has no larger influences or L2 norm. For fixed d, the matching-first-three-moments Lindeberg replacement bounds the expectation error for any C4 test with bounded fourth derivative by

    C_d ||test^(4)||∞ Σ_i Inf_i(p_k)²
      ≤C_d d ||test^(4)||∞ α_k→0.               (11)

Here the mixed bit/Gaussian fourth-moment estimate for a degree-(d−1) derivative B is E B⁴≤9^(d−1)(Inf_i p_k)². It follows from the two-variable expansion E(A+XB/√3)⁴≤(A²+B²)² and tensorization, as proved in I290. Equations (9)–(11) involve λ only through its fixed spectral tail, and σ_k only through noise contraction. Neither needs σ_k=λ.

Transfer the uniformly continuous bounded tests clip and ψ∘clip by smooth uniform approximation. Transfer dist(x,[−1,1])² by convolution: its smooth fourth derivative is bounded at any fixed convolution radius, and the approximation error is at most Cτ(1+|x|)+Cτ², paid by E p_k²≤1 on both spaces. Since h_k is bounded, (9) implies

    ||v_k−p_k||_(2,G)²≤λ^(2(d+1))+o_k(1).

Gaussian L2 noise contraction then gives

    ||Q_(σ_k)v_k−clip(q_k)||_(2,G)
      ≤||v_k−p_k||_(2,G).

The corresponding cube clip errors relative to h_k,T_(σ_k)h_k are bounded by (9). For bounded fields w,w′, continuity of ψ converts small L2 error to small entropy error by splitting at |w−w′|≤δ and bounding the complement by L||w−w′||₂²/δ². Mean errors are also paid by L2, followed by scalar uniform continuity of ψ. Combining these estimates with (11) proves: for any ζ>0, first choose d sufficiently large depending only on ζ,λ, then take k sufficiently large to obtain

    |I_G(v_k)−I(h_k)|<ζ,
    |I_G(Q_(σ_k)v_k)−I(T_(σ_k)h_k)|<ζ.           (12)

This reproduces precisely the operative I290 transfer with the unequal split. The order is fixed d, then large k; no growing-degree invariance assertion or multivariate EPI shortcut enters.

Define b_k=ψ⁻¹(I_G(v_k)). For small ζ and large k, (8),(12) put b_k in the selected compact interval below 1/√2. This definition enforces exact Gaussian information. Uniform continuity of (σ,J)↦ψ(σψ⁻¹(J)) makes ψ(σ_k b_k) as close to ψ(ρ_k a_k) as desired. Apply G295-small. Choose ζ so that the two errors in (12), the error in (8), and this scalar continuity error together are less than η_G/2. It follows that

    I(T_(σ_k)h_k)≤ψ(ρ_ka_k)−η_G/2,

contradicting (8). Hence no increasing diffuse sequence of vanishing deficit exists on this rectangle.

### 5.3 Obtaining a uniform linear constant, with every entrance step paid

The contradiction just proved implies there exist β,η>0 depending only on the endpoints such that every increasing kernel of the exact information budget with max_i û(i)≤β has Δ_ρ≥η. Otherwise choose such kernels with max singleton≤1/k and Δ≤1/k, contradicting §5.2. In this sector d_a≤4≤(4/η)Δ. In its complement B290 gives d_a≤C_βΔ. Thus all increasing kernels satisfy

    d_a≤C_inc Δ, C_inc=max{4/η,C_β}.

For completeness, B290 does not impose a hidden closeness hypothesis. Its proof uses (7) and the integrated surplus on a middle third of [0,t] to find a positive time s with R(s) small. The marked original singleton remains at least ρ₀β there. I290 P290 supplies a qualitative L2 entrance from the small surplus at this specified coordinate. Its proof is compactness of pair laws on the fixed square [−1,1]² and the marked joining equality classification, not compactness of growing cubes. The comparison amplitude ψ⁻¹(I(P_su)) is within O(Δ) of ae⁻ˢ on a compact positive information range.

The backward step uses the original budget: with q=||P_su−εae⁻ˢX_i||₂², E131 gives

    E|u−εaX_i|²
      ≤[2atanh((1+a₁)/2)/ρ₀]√q+2Lq+q/ρ₀².

Once q is small this enters the spike-tolerant L131 neighborhood, whose linear bound applies to the original u. Larger deficits are paid by d_a≤4. This explains why no new initial closeness, mean-zero, endpoint exclusion, or inverse-noise assumption has appeared in C_β.

Finally sort any arbitrary u to g and use Q131b. Since L_gain≥0,

    d_a(u)≤C_comp[C_inc Δ(g)+L_gain]
            ≤C_comp max{C_inc,1} Δ(u).

Taking this last constant as C proves S295 with all the original kernel quantifiers.

## 6. Extension work: compact optimization is paid; cube strictness is not

### 6.1 Compact scalar optimizers and what their existence does imply

Let M be all nondecreasing [−1,1]-valued functions on R modulo γ_1-null sets. Every sequence in M has a subsequence converging at continuity points of a monotone limit, by diagonal selection on rational points and the monotone extension. There are only countably many discontinuities. Dominated convergence gives L2(γ_1) convergence. Thus M is sequentially compact in this metric, hence compact.

I_G is continuous on bounded L2 fields by the entropy-continuity argument above. Moreover (w,σ)↦Q_σw is jointly L2-continuous on M×[σ₀,σ₁]:

    ||Q_(σ_k)w_k−Q_σw||₂
      ≤||w_k−w||₂+||(Q_(σ_k)−Q_σ)w||₂→0.

The last limit follows from Hermite expansion and dominated convergence of the squared coefficients. Therefore

    K={ (w,b,σ): w∈M, b∈[b₀,b₁], σ∈[σ₀,σ₁],
                    I_G(w)=ψ(b) }

is compact for every compact rectangle in (0,1)². It is nonempty, since w=b sign(z) works at every b. Output information and the deficit are continuous on K; extrema are attained. R295 makes this a true dimension-free reduction: the supremum over every finite Gaussian dimension equals the scalar monotone supremum.

The non-strict cube curve is valid on Gaussian space, by the constructive block-sum argument already paid in I290 §5. To specify that interface: apply a bounded smooth w with bounded derivatives through order three to normalized sums of fair bits. Conditional on all noisy output bits, the centered input summands are independent with uniformly bounded third moments and variance 1−σ². A third-order replacement estimate gives an O(M⁻¹/²) conditional-mean error uniformly in the output bits as block size M→∞. The output normalized sums converge to standard Gaussian. Uniform continuity of ψ pays input and output information convergence. Bounded smooth approximation in Gaussian L2 and OU contraction extend the result to measurable kernels. This uses conditional-mean convergence, not a bare joint CLT to assert conditional entropy convergence. Pinned `main:soft` consequently implies

    I_G(Q_σw)≤ψ(σψ⁻¹(I_G(w))).                     (13)

Thus, after the new compactness reduction, the following **pointwise** obligation is sufficient and equivalent to G290 on all compact rectangles:

    For every nonconstant w∈M, 0<I_G(w)<L,
    and every 0<σ<1,
    I_G(Q_σw)<ψ(σψ⁻¹(I_G(w))).                    (U295, UNPROVED)

If U295 holds, its positive continuous deficit has a positive minimum on each K. Conversely G290 implies U295. Before law-preserving rearrangement and fixed scalar compactness, this inference from pointwise strictness to a dimension-free uniform gap was unavailable. Both the compactness and the exact remaining strictness claim are now separated.

Equation (4) similarly implies a uniform gap below the **EPI** curve on each K, and R295 transfers it to all dimensions. This is a paid strict EPI reserve, but its size has not been shown to exceed the difference between the EPI and cube curves where that difference is positive.

### 6.2 Why EPI does not close all rectangles

H is not globally convex. In (5), as x↑1 the negative term is asymptotic to −1/[2(1−x)], whereas the positive term is only O(log²(1−x)); H″ is negative near 1. More directly H′(x)=−H(x)atanh(√x)/√x→−∞. For fixed x close to 1 define

    g_x(θ)=1−θ+θH(x)−H(θx).

Then g_x(1)=0 and g_x′(1)=H(x)−1−xH′(x)>0 when x is sufficiently close to 1. Hence g_x(θ)<0 for θ<1 sufficiently close to 1. At b=√x and σ=√θ, B_σ(ψ(b))>ψ(σb). This is an analytic obstruction to using the scalar EPI curve as a globally stronger bound; no numerical scan is used. It is not a counterexample to G290 or S128.

Strict ordinary EPI and compactness give some improvement ε_K>0 over B_σ on K. To close the large-amplitude region by this route one would need a bound ε_K exceeding sup_K[B_σ(ψ(b))−ψ(σb)] (or a pointwise tailored improvement). Neither ordinary EPI equality nor the compactness proof provides that comparison. The sufficient threshold 1/√2 is not claimed optimal.

### 6.3 Analytic propagation was investigated, not assumed

Suppose equality in (13) held at a finite time t. Non-strict contraction from every intermediate time s to t forces equality along 0≤s≤t: writing r(s)=ψ⁻¹(I_G(Q_(e⁻ˢ)w)), we have r(s)≤e⁻ˢr(0) and r(t)≤e^(−(t−s))r(s), and equality at t forces both bounds to be equalities. This gives an exponential amplitude on that interval only. It does not continue equality to later times where amplitude is small; a nonnegative production surplus could start later.

Real analyticity of the required information trajectory would permit continuation and then a contradiction with §4, but it is not proved here. The actual primary Guo–Wu–Shamai–Verdú `1004.3332v1` Proposition 8 and its Appendix D were inspected. The theorem adds uniform complex nonvanishing and tail-ratio hypotheses (55)–(58), beyond sub-Gaussian tails. Its proof uses these hypotheses for the denominator and uniform integrability of the complexified MMSE integrand. Posterior bounds (3) pay tails and moments, but do not establish those complex conditions. Their unrestricted monotone factor is not a finite Gaussian mixture. Earlier search hits making a blanket analyticity assertion are not used as a theorem.

For an explicit interface, with s=σ²/(1−σ²), information about B through √s Z+Z′ satisfies

    I(B;√s Z+Z′)=I(Z;√s Z+Z′)
                    −Σ_±p_± I(Z;√s Z+Z′|B=±).

The first term is ½log(1+s); the other terms concern the posterior input laws (3). Analyticity would have to be justified for those laws, or proved directly for the binary OU information. Infinite differentiability, positivity on the real axis, or pointwise analyticity of a smoothed density is insufficient for an identity theorem on the integrated entropy. This route remains an exact unpaid analytic obligation, not a proof of U295.

The complementary-density LSI route also remains at the I290 boundary: D_G−2I_G=2Σp_±δ_LSI(f_±). Nonattainment of ordinary LSI does not pay the larger reserve F(I_G)−2I_G. Borell's halfspace equality classification concerns its two-set functional and does not classify equality in (13), which already may be evaluated on a perfectly rearranged w. These are distinct equality problems.

## 7. Contribution, proof scope, and validation

The result proved here is S295 on every compact rectangle with ρ₁a₁<1/√2, for all arbitrary soft kernels. It is a concrete global theorem with a full proof, not a proposed Gaussian bridge or a local/junta special case. It does not settle full S128. The remaining obligation can now be stated exactly as U295, a scalar monotone pointwise strictness theorem; compactness then supplies G290, and I290 supplies the rest of S128.

Borell rearrangement, entropy power, Helly selection, Gaussian smoothing, Lindeberg replacement, and the Gaussian bottleneck curve are classical. The parent supplied the route and the conservative curvature calculation. I128's budget/ODE identities, I131's compression and local/backward bridges, and I290's marked-sector and diffuse transfer are essential inherited deductions. I295 verifies and assembles these into the parameter-restricted unrestricted-kernel theorem, and pays the scalar compact-optimizer reduction. This is a new-to-this-round completion of a previously unpaid regime; no independent old-method novelty or worldwide priority is asserted. The external comparisons already authenticated by I290 are credited at their read scopes, not newly replayed or declared globally exhausted.

Validation is analytic: primary proof reads, direct Hessian/entropy/curvature calculations, the unequal-split transfer bounds, and exact local file/source authentication. No scans, certificates, subagents, live sibling reads, shared-index changes, staging, commits, or publication occurred. Detached output hashes are returned separately. Acceptance and contribution judgment remain for the parent.
