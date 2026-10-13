# I290 mathematical analysis

2026-10-13. S128 is unresolved. This file proves a conditional global bridge, eliminates every fixed positive singleton sector, and gives a constructive reduction of the remaining diffuse sector to a precisely stated, unpaid Gaussian gap. It supplies neither that gap nor an actual counterexample. No acceptance judgment is made.

All cube expectations use uniform probability. Write L=log 2, H=L−ψ, V=atanh, F(ψ(r))=rV(r), S=F−2I with the source's zero extension below zero, and

    B_m(I)=2I+(1−m²)S(L−(H(m)−I)/(1−m²)),
    Φ_m(I)=max{F(I),B_m(I)}.

For interior g, D(g)=E[V(g)Ng], N=½Σ_i(Id−flip_i), and R(g)=D(g)−F(I(g))≥0. Source operations are stipulated, including arbitrary coupled laws in the joining theorem. References below are the labels in the authenticated pinned TeX, not informal catalogue assertions. The accepted L131 local theorem and Q131b compression transfer are used at precisely their stated scopes.

## 1. Paid route one: equality and compactness of a marked join

### J290: equality at a nonzero mean separation

Let μ be a probability law of (A,B) on [-1,1]². Extend

    c(A,B)=(A−B)(V(A)−V(B))/4

by zero at the two equal corners and +∞ at all other boundary pairs, as in `canonical:cost`. Suppose Ec<∞ and δ=(EA−EB)/2>0. Put

    m=(EA+EB)/2, e_A=EH(A), e_B=EH(B), e=(e_A+e_B)/2,
    I=H(m)−e, I_A=H(EA)−e_A, I_B=H(EB)−e_B,
    J(μ)=Ec+½[Φ_(EA)(I_A)+Φ_(EB)(I_B)]−Φ_m(I).

Then J≥0, and J=0 if and only if μ is the point mass at (r,−r) for some 0<r<1.

First note that e_A,e_B>0 and both means are interior. If e_A=0, A is an endpoint almost surely. Finite c then forces B=A almost surely, contradicting δ>0. The same argument applies to e_B. If EA is an endpoint, A is that constant endpoint and again B=A. Thus all arguments in `upgrade:joining` are physical, including a law with some mass at equal corners.

Here are the strictness checks missing from a mere citation of the source optimizer. Let K be the common-budget minimum, attained by the unique canonical law with core (x,y), mass k>0, and corner masses π_+,π_−. Let its core center be m_c and its half separation δ_c; δ=kδ_c. Set c₀=2−4L²>0.

If the parent maximum is attained by B (ties included), `reserve:pooling`, `reserve:payment`, and `reserve:canonical-payment` give

    J ≥ Ec−W(parent) ≥ K−W(parent) ≥ 0.

Keeping the positive margin in `reserve:corner-margin` gives

    K−W(parent) ≥ (c₀/8)(1−k)δ².                 (1)

For completeness, on a common-corner ray with retention τ, the source Euler identity gives

    τW′−W ≥ c₀κ_τ,  κ_τ≥τ²δ_c²/8.

Integrating (W/τ)′ from τ to 1 gives a loss at least (c₀/8)τ(1−τ)δ_c². Compose retentions k/(k+π_+) and k+π_+. The sum, with the first loss multiplied by the second retention, is at least

    (c₀/8)δ_c² [kπ_+ + k²π_−]/(k+π_+)
      ≥ (c₀/8)(1−k)δ².

There is no division by δ. This is the I131 R131b extraction, reproduced here to retain its exact scope. Hence equality forces k=1.

At k=1 the optimizer is deterministic. For its center m_c put α_c=1−m_c² and J_c=H(m_c)−[H(x)+H(y)]/2>0. The source capacity payment is

    W(core) ≤ 2J_c+α_c S(J_c/α_c)
            = α_c F(J_c/α_c) ≤ c(x,y).

The first inequality is strict if m_c≠0. Indeed

    H(m_c)−α_c L=Lm_c²−ψ(m_c)>0

for 0<|m_c|<1, by the positive ψ series. Thus the surplus argument L−e_c/α_c is strictly less than J_c/α_c, which is positive and below L by `capacity:onebit`. S is strictly increasing on positive arguments and zero on nonpositive arguments. Consequently W(core)<α_c F(J_c/α_c) when m_c≠0. Equality therefore forces m_c=0. Finally J=0 forces Ec=K. Unique optimality in `canonical:priced`/`canonical:coverage` forces the actual law to be that deterministic core, rather than merely to share its scalar moments.

If the parent strictly chooses F>B, `upgrade:original-child-pooling` gives

    J ≥ Ec−[F(I)−F(j)] ≥ K−[F(I)−F(j)],
    j=(I_A+I_B)/2.

Reflect signs to m>0. In one-positive-corner geometry, the thinning proof, with its retained margin `thinning:derivative-loss` and `thinning:window-bound`, gives

    kF(J_c)−[F(I)−F(j)] ≥ (c₀/8)k(1−k)δ_c².

This is strictly positive if k<1. If k=1, the law is deterministic with m>0; `capacity:onebit` and strict convexity of F give

    c(x,y) ≥ α_c F(J_c/α_c)>F(J_c).

In reflected-core geometry m>0 implies k<1. Moving to the one-corner wall cannot decrease the demanded increment (`wall:monotonicity`); the endpoint has the same k, cost and separation, and its thinning loss is strictly positive. Therefore K>F(I)−F(j) also in this case. A strict F parent cannot have J=0. Conversely the reflected deterministic pair has child informations zero, parent mean zero, Φ_0=F, and cost rV(r)=F(ψ(r)), so J=0. This proves J290.

### M290: a uniform modulus on pair laws

Fix 0<j₀≤j₁<L, b>0 and M<∞. For every ε>0 there is η>0, depending only on these five parameters, such that any pair law with

    δ≥b, j₀≤I≤j₁, Ec≤M, J(μ)≤η

satisfies, with r=ψ⁻¹(I),

    ½E[(A−r)²+(B+r)²] < ε.                     (2)

**Proof.** Probability laws on the fixed compact square [-1,1]² are weakly compact. The cost is nonnegative and lower semicontinuous, so {Ec≤M} is weakly closed. Means, entropy moments, δ and I are continuous. Hence the parameter-restricted set K is compact. On K neither entropy moment can be zero and neither mean an endpoint, by the finite-cost argument above. Compactness consequently gives uniform positive lower bounds for both entropy moments and for both distances of the means from the endpoints. This is deduced from the cost and separation hypotheses; no pointwise interior bound is assumed.

All profile arguments therefore lie in a compact part of their physical domains. Φ is continuous there, including branch ties, the clipped reserve seam, and child information zero. Thus J is lower semicontinuous on K. The expression on the left of (2) is continuous, since r depends continuously on I. The closed subset where it is at least ε is compact. Its minimum J is positive by J290. Take η smaller than that minimum; if this subset is empty, any positive η suffices. This proves (2).

This compactness occurs in the space of probability laws on one fixed square. No cube dimension, finite-junta approximation, or infinite-cube compactness enters.

### P290: marked production entrance in arbitrary dimension

Fix j₀,j₁,b as above. For every ε>0 there is η>0 such that every finite-dimensional interior g with

    j₀≤I(g)≤j₁, |ĝ(i)|≥b, R(g)≤η

obeys

    E|g−σψ⁻¹(I(g))X_i|²<ε,

where σ orients ĝ(i) positively. The coordinate is the specified marked coordinate; it need not maximize the singleton coefficient.

**Proof.** Apply M290 to the law of the two faces at i. After orientation its δ is |ĝ(i)|. The exact energy split and stipulated face production yield

    R(g)=½Σ_±[D(g_±)−Φ_(Eg_±)(I(g_±))]
           +J(μ)+Φ_(Eg)(I(g))−F(I(g)) ≥ J(μ).

Also Ec≤D(g)≤F(j₁)+1 when R≤1. Use M=F(j₁)+1 and reduce η to at most 1. Equation (2) is exactly the asserted cube L2 distance. This proves P290. Arbitrary bias, unequal face means, corner mass, spikes and arbitrarily many remaining coordinates are allowed.

## 2. B290: global stability whenever a singleton is bounded below

Fix the four S128 endpoints and β>0. There is C_β<∞, depending only on them and β, such that for all finite n and all u in the original S128 model,

    max_i |û(i)|≥β  ⇒  d_a(u)≤C_β Δ_ρ(u).      (3)

This is a global theorem within its stated sector: there is no closeness, balance, endpoint-value or complexity assumption. The added β is essential to the proof and is not removed in S128.

**Proof.** Put P_s=T_(e⁻ˢ), t=−logρ, y(s)=I(P_su), w(s)=ψ(ae⁻ˢ), z=w−y, R(s)=D(P_su)−F(y(s)). Let

    t_min=−logρ₁>0, t_max=−logρ₀,
    K=max_[0,ψ(a₁)] F′, w_min=ψ(ρ₀a₀)>0.

The P128 ODE z′=R−Az, 2≤A≤K, and its integrating factor imply both

    ∫₀ᵗ R(s)ds≤e^(Kt_max)Δ,
    0≤z(s)≤e^(Kt_max)Δ  (0≤s≤t).              (4)

For the second assertion, integrate from s to t and discard the nonnegative future surplus. This is an earlier-time bound, not a reverse estimate at later noise times.

If Δ is small enough, throughout [0,t] we have

    w_min/2≤y(s)≤ψ(a₁).

Choose a point s in [t/3,2t/3] where

    R(s)≤3e^(Kt_max)Δ/t_min.                   (5)

Such a point exists by (4). At positive time P_su is interior for every nonconstant finite-cube input; positive information excludes constants. A marked coordinate with |û(i)|≥β has

    |(P_su)^hat(i)|=e⁻ˢ|û(i)|≥ρ₀β.

P290, with j₀=w_min/2, j₁=ψ(a₁), b=ρ₀β, gives arbitrarily small L2 distance between g=P_su and σr_sX_i, r_s=ψ⁻¹(y(s)), once Δ is below a fixed positive threshold. On this compact information range, ψ⁻¹ is Lipschitz, so (4) gives |r_s−ae⁻ˢ|≤CΔ. Hence

    ||P_su−σae⁻ˢX_i||₂²

is as small as desired, uniformly in n.

For clarity the backward step uses the original information budget. Write λ=e⁻ˢ≥ρ₀, m=Eu, and b_i=E[uσX_i]. If the last displayed squared distance is q, then m²≤q and |b_i−a|≤√q/ρ₀. Strong convexity gives the E128 inequality

    E|u−σaX_i|²
      ≤2[ψ(a)−ψ(b_i)+ψ(m)]+(a−b_i)².

For q small enough that |b_i−a|≤(1−a₁)/2, its right side is at most

    2V((1+a₁)/2)√q/ρ₀+2Lq+q/ρ₀².

Choose the P290 tolerance and then the Δ threshold so that this is at most ε_*² from L131. L131 now gives d_a(u)≤Δ/c_* at the original u. At larger deficits use d_a(u)≤4 and that positive threshold. Taking the maximum of these constants proves (3). Initial endpoint values and spikes were handled by positive-time entrance and the accepted spike-tolerant L131 theorem, not by uniform L∞ smoothing.

## 3. D290: all possible failure sequences are diffuse after compression

Let g be the increasing function obtained by sorting every coordinate fiber of u. I131 Q131b states

    I(g)=I(u), Δ(u)=Δ(g)+L_gain,
    d_a(u)≤C_comp[d_a(g)+L_gain], L_gain≥0.

If max_i ĝ(i)≥β, B290 applies to g, so

    d_a(u)≤C_comp(C_β+1)Δ(u).                  (6)

Consequently, if S128 fails on any fixed endpoint rectangle, one can choose a sequence with d_a(u_k)>kΔ(u_k). Since d_a≤4, Δ(u_k)→0. Equation (6) forces the maximum singleton of each compressed g_k to tend to zero. Their deficits also tend to zero. Thus it is enough to rule out a sequence of increasing, exact-information kernels with

    Δ_ρ(u)→0,  max_i û(i)→0.                  (7)

Conversely a uniform positive deficit gap for increasing kernels with max singleton≤β, for some fixed β>0, together with (3), closes S128 and transfers it by Q131b. If full S128 holds, such a gap exists: d_a≤CΔ and Cauchy–Schwarz imply some singleton at least a−√(CΔ), hence at least a₀/2 for sufficiently small Δ. This equivalence uses the newly proved global marked sector, not an assumed coordinate-selection theorem.

## 4. Paid route two: the diffuse-to-Gaussian transfer

For a bounded function v on standard Gaussian space define

    I_G(v)=E_Gψ(v)−ψ(E_Gv),
    Q_σv(z)=E[v(σz+√(1−σ²)Z′)].

Here is the exact unpaid statement sufficient to close the main target.

**G290 (UNPROVED).** For every 0<b₀≤b₁<1 and 0<σ₀≤σ₁<1 there is η_G>0 such that for every finite Gaussian dimension N, every measurable v:R^N→[-1,1], every b in [b₀,b₁] with exactly I_G(v)=ψ(b), and every σ in [σ₀,σ₁],

    I_G(Q_σv) ≤ ψ(σb)−η_G.                   (8)

No balance or monotonicity is imposed. This is a uniform strict fixed-information Gaussian gap, not merely a fixed-mean Boolean halfspace theorem or a statement that equality is never attained. Pointwise strictness without a uniform gap does not suffice.

**T290 (proved conditional reduction).** G290 on the compact parameter ranges below implies that (7) is impossible, and therefore implies full S128.

**Proof.** Suppose (7) holds for increasing u_k, with α_k=max_i û_k(i)→0. Put λ_k=√ρ_k, σ_k=√ρ_k, h_k=T_(λ_k)u_k. Equation (4), applied at half noise time, gives

    I(h_k)−ψ(λ_ka_k)→0,
    I(T_(σ_k)h_k)−ψ(ρ_ka_k)→0.               (9)

For an integer d let p_k be the multilinear Walsh polynomial of h_k truncated to degree d. Regard the same polynomial as a function of independent standard Gaussians, and let v_k=clip(p_k,−1,1) there. Put q_k=T_(σ_k)p_k, meaning multiplication of each degree-j coefficient by σ_k^j. On Gaussian space q_k=Q_(σ_k)p_k exactly, because the polynomial is multilinear.

The elementary spectral bounds are dimension independent:

    ||h_k−p_k||₂²≤λ_max^(2(d+1)),
    ||T_(σ_k)h_k−q_k||₂²≤λ_max^(2(d+1)),
    E p_k²≤1, λ_max=√ρ₁<1.                  (10)

Moreover ∂_ih_k≥0 and ≤1 by monotonicity and boundedness; therefore

    Inf_i(p_k)≤E(∂_ih_k)²≤E∂_ih_k
               =λ_k û_k(i)≤α_k.             (11)

The same estimates hold for q_k. These are actual L2 polynomial influences; no Boolean identity E∂²=E∂ is used.

For fixed d, cube and Gaussian expectations of any fixed smooth test of p_k or q_k differ by o_k(1). A direct proof is the Lindeberg argument underlying MOO Theorem 3.18, Hypothesis 4: write p=A+x_iB and replace one bit by one Gaussian. Their first three moments match. Fourth-order Taylor remainder costs at most a constant times ||test^(4)||∞ E B⁴. Mixed bit/Gaussian multilinear hypercontractivity gives E B⁴≤9^(d−1)(Inf_i p)². Summing the errors is at most C_d||test^(4)||∞ α_k Σ_i Inf_i p≤C_d d||test^(4)||∞ α_k. This tends to zero at fixed d. The Gaussian and bit hypercontractive inputs and this replacement proof are classical; the relevant primary statements/proofs were read, and no new invariance theorem is claimed.

The mixed fourth-moment bound can also be checked directly. For a fair bit or a standard Gaussian X and η=1/√3,

    E(A+ηXB)⁴=A⁴+2A²B²+(EX⁴/9)B⁴≤(A²+B²)².

This is the one-variable L2→L4 norm inequality for linear polynomials. Tensorization by Minkowski gives ||T_η p||₄≤||p||₂ for multilinear polynomials on any mixture of these variables. Apply it to the polynomial with coefficients multiplied by η^(−|S|) to obtain ||p||₄≤3^(d/2)||p||₂ at degree d. Applied to B of degree d−1 this gives exactly the bound used above. It requires no regularity or equality theorem about the Gaussian kernel v_k.

Approximate the bounded uniformly continuous functions ψ(clip x) and clip x uniformly by smooth functions with bounded fourth derivative. The preceding argument then transfers their expectations as well. It also transfers the expected squared distance f(x)=dist(x,[-1,1])², despite its quadratic growth. To see the latter without assuming a bounded test, convolve f at radius τ. Its fourth derivative is bounded for fixed τ, while |f_τ(x)−f(x)|≤Cτ(1+|x|)+Cτ²; E p_k²≤1 on both spaces pays the approximation error. First send k to infinity and then τ to zero.

Since h_k is in [-1,1], dist(p_k,[-1,1])≤|p_k−h_k| on the cube. Thus (10) and the transferred squared-distance estimate give

    ||v_k−p_k||_(2,G)²≤λ_max^(2(d+1))+o_k(1). (12)

L2 contraction of Q_σ and Q_σv_k in [-1,1] yield

    ||Q_(σ_k)v_k−clip(q_k)||_(2,G)
      ≤||Q_(σ_k)v_k−q_k||_(2,G)
      ≤||v_k−p_k||_(2,G).                    (13)

Likewise on the cube, clipping p_k and q_k changes their distance to h_k and T_(σ_k)h_k by no more than the errors in (10). Continuity of ψ on [-1,1] converts bounded L2 errors to dimension-free expectation errors: split at |x−y|≤δ and bound the complement by L||x−y||₂²/δ². Mean errors are bounded by L2 errors, with the same scalar continuity estimate for ψ of the means.

Combining the smooth-test transfers, (10)–(13), and these entropy continuity bounds, for any ζ>0 one can first choose d, depending only on ζ and ρ₁, and then k large, to obtain

    |I_G(v_k)−I(h_k)|<ζ,
    |I_G(Q_(σ_k)v_k)−I(T_(σ_k)h_k)|<ζ.        (14)

This proves transport of both initial and final information. It is not a seed lift, a growing-dimension compactness argument, or inversion of noise. The order of limits d then k is essential.

Choose a compact b interval strictly containing [√ρ₀ a₀,√ρ₁ a₁] and lying in (0,1), and use σ in [√ρ₀,√ρ₁]. For sufficiently small ζ and large k, I_G(v_k) lies in the corresponding information interval. Define b_k=ψ⁻¹(I_G(v_k)); this preserves exact Gaussian information rather than rescaling v_k. The map

    (σ,J)↦ψ(σψ⁻¹(J))

is uniformly continuous on that compact domain. If (8) holds, choose ζ so small that the errors in (9), (14) and this scalar comparison total less than η_G/2. Then (8) implies

    I(T_(σ_k)h_k)≤ψ(ρ_ka_k)−η_G/2,

contradicting (9). This proves T290 and the conditional reduction to full S128.

**What remains unpaid.** Equation (8) has not been proved here. Fixed-mean Boolean Gaussian comparisons do not establish it at exactly Eψ(v)−ψ(Ev)=ψ(b), and a qualitative Gaussian equality classification does not establish its uniform η_G over dimensions. T290 pays the transfer, including clipping, means, exact-information matching and the two noise levels; the Gaussian optimization/gap itself is the outstanding theorem in this second route.

## 5. User-suggested complementary-density LSI route: the precise reserve still needed

This optional lead was investigated within the Gaussian route. For a smooth Gaussian field v in (-1,1), with m=Ev and finite energy, put w_±=(1±m)/2 and

    f_+=(1+v)/(1+m), f_-=(1−v)/(1−m).

Both are probability densities relative to standard Gaussian measure and

    w_+f_++w_-f_-=1,
    I_G(v)=w_+Ent_G(f_+)+w_-Ent_G(f_-).

For J_G(f)=E_G|∇f|²/f, direct differentiation gives

    D_G(v):=E_G|∇v|²/(1−v²)
            =w_+J_G(f_+)+w_-J_G(f_-).

Indeed the two terms are ½E|∇v|²/(1+v) and ½E|∇v|²/(1−v). In the standard normalization δ_LSI(f)=J_G(f)/2−Ent_G(f),

    D_G(v)−2I_G(v)=2[w_+δ_LSI(f_+)+w_-δ_LSI(f_-)].  (15)

If I_G(v)≥j₀>0, I_G(v)≤H(m) gives |m|≤m_*(j₀)<1, so both weights are bounded below and both density upper bounds 2/(1±m) are bounded above. These are actual consequences of the information constraint. No posterior Poincaré inequality is inferred.

Equality in both standard Gaussian LSI inequalities would make both densities exponential tilts. A positive mixture of two such tilts cannot be identically 1 unless both tilts are constant: any nonzero tilt diverges along its tilt direction while the other summand is nonnegative. Equivalently a bounded exponential tilt is constant. Thus exact equality in D_G≥2I_G is incompatible with positive information. This observation alone is weaker than G290. Along a putative sequence with D_G−F(I_G)→0 at fixed positive information, the right side of (15) need not tend to zero; it can tend to the positive number F(I_G)−2I_G. Standard near-LSI-equality stability therefore cannot simply be applied to that sequence.

The exact sufficient production statement is:

**GP290 (UNPROVED).** On every 0<j₀≤j₁<L, there is η_P>0, independent of Gaussian dimension, such that

    D_G(v)≥F(I_G(v))+η_P

for all fields of finite Gaussian energy and information in [j₀,j₁]. In complementary-density terms the required lower bound is

    2Σ_±w_±δ_LSI(f_±)≥F(I_G(v))−2I_G(v)+η_P. (16)

This specifies the quantitative reserve needed beyond standard LSI. It is stronger than an unspecified positive lower bound on the weighted LSI deficit.

GP290 would imply G290 by semigroup integration. The non-strict Gaussian version of the pinned sharp contraction can itself be obtained without a Gaussian equality theorem: approximate a bounded continuous Gaussian field by applying it to independent normalized block sums of fair bits. Given the full noisy output Y, the summands in each input block are independent, have means ρY_i, and have identical variance 1−ρ². The centered normalized conditional sums have uniformly bounded summands of order N^(−1/2); the Lindeberg CLT therefore holds uniformly over Y for fixed block dimension and fixed 0<ρ<1. For bounded Lipschitz test fields it gives conditional posterior means approaching Q_ρv at the output block sums. This can be obtained directly by smooth approximation and the replacement Taylor argument, whose total third-order error is O(N^(−1/2)) uniformly over Y. Output block sums converge to independent Gaussians. Continuity of ψ then transports both entropy expectations and the mean, so pinned cube contraction passes to Gaussian space. General bounded continuous fields follow by Gaussian L2 approximation by bounded smooth Lipschitz fields; bounded measurable fields follow by the same approximation, OU L2 contraction and entropy continuity. A joint weak CLT alone is not being used to assert convergence of conditional entropies.

Thus the coordinate comparison z is nonnegative. Under a small terminal deficit, information throughout the noise interval stays above half its compact positive terminal comparison value. The Gaussian de Bruijn identity y′=−D_G, with the same F-secant integrating factor as P128, then gives a terminal deficit at least η_P(1−e^(−Kt))/K. At larger terminal deficits use half the minimum terminal information. Smooth positive-time approximation/regularization justifies the identity for bounded initial fields; this is the standard OU entropy calculation, also displayed in the FIL primary proof. Hence a uniform reserve in (16) would close the already-paid transfer route.

The checked primary LSI comparisons do not supply (16). Fathi–Indrei–Ledoux's Theorem 1 and Corollary 2 require a Poincaré inequality for each posterior measure; their proof uses that inequality on its evolved log-density gradient. The complement relation and an upper density bound do not furnish this hypothesis. Eldan–Lehec–Shenfeld's Corollary 2 imposes a second-moment matrix bound, and Theorem 3's sharper covariance specialization requires covariance dominated by identity. The complementary posteriors have only the pooled identity

    w_+Cov(f_+γ)+w_-Cov(f_-γ)=Id−rrᵀ/(1−m²), r=E[vZ].

This does not put each covariance below identity. For example take one Gaussian coordinate and v=ε(h(Z)−Eh(Z)) for a smooth bounded even h strictly increasing in Z². For small ε both densities are positive and bounded, m=r=0, and their variances are 1±εCov(h(Z),Z²). The covariance is strictly positive by the independent-copies covariance identity. One posterior variance exceeds 1. Their unconditional mixture is still exactly Gaussian. This is a scope check, not a counterexample to GP290.

The ELS general mixture/Wasserstein statements inspected also do not turn the right side of (15) into (16); some have explicit dimension factors or a different decomposition target. No arbitrary-density dimension-free compactness or posterior Poincaré estimate is asserted. The lead identifies a promising complementary-mixture optimization problem, but the strict nonlinear reserve remains unpaid. No small-amplitude Taylor heuristic is used as its proof.

## 6. Why diffuse bounded soft fields cannot be dismissed by a junta assertion

An analytic test family, not a numerical scan, illustrates the real scope. For odd n put Z_n=n^(-1/2)Σ_iX_i and

    u_n=tanh(c_n Z_n),

where c_n>0 is the unique root Eψ(tanh(c_n Z_n))=ψ(a) for a fixed 0<a<1. Symmetry gives Eu_n=0. Since odd n has no zero atom, this continuous increasing function of c goes from 0 to L, so the root exists and the budget is exact. The classical central limit theorem and bounded continuous convergence show c_n→c_a, the unique positive root Eψ(tanh(c_a Z))=ψ(a). For fixed c, the Gaussian expectation strictly increases from 0 to L; bracketing c_a proves convergence of the roots, without any numerical evaluation.

The fiber derivative is nonnegative and at most c_n/√n, hence every singleton tends to zero. For any coordinate set K of size k, symmetry of the remaining sum and Lipschitz continuity of tanh give

    |E[u_n|X_K]|≤c_n|Σ_(i∈K)X_i|/√n,
    ||E[u_n|X_K]||₂²≤c_n²k/n.

But ||u_n||₂²≥ψ(a)/L>0. Its distance to every function depending on a fixed k coordinates is therefore bounded below by ψ(a)/L−c_n²k/n. Even after any fixed noise λ>0, a nonzero amount of variance remains: symmetry gives

    W₁(u_n)=(E[u_n Z_n])²→(E[tanh(c_a Z)Z])²>0,
    Var(T_λu_n)≥λ²W₁(u_n),

where convergence of the first moment follows from the uniform second-moment bound on Z_n. Projection onto K still has norm at most c_n√(k/n). Thus smoothing does not give a uniformly accurate finite-junta approximation for arbitrary bounded monotone soft fields at this information budget. This family is not shown to have small deficit and is not a counterexample to S128 or G290.

## 7. Contribution and validation limits

J290/M290/P290 are a qualitative global joining-rigidity bridge at a marked nonzero singleton. B290 upgrades this to linear S128 stability throughout every fixed positive singleton sector, using the accepted local theorem only after paying global entrance. D290 clears that entire sector, including arbitrarily complex face functions. T290 then pays an explicit diffuse-to-Gaussian reduction. These statements are not a proof of unrestricted S128.

The optimizer, scalar capacities, reserve, thinning, sharp contraction, compression transfer, local L2 theorem, hypercontractivity and Lindeberg method are already paid or classical. The contribution is their new strict equality/compact-law use and the two global reductions with their stated scopes. No quantitative modulus rate in β, no global soft Gaussian gap, no world-priority claim and no acceptance nomination is asserted. All new inequalities were checked symbolically by their displayed derivations; no numerical scans, inherited verification replay, staging, commits or publication occurred.
