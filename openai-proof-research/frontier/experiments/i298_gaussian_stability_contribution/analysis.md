# I298 independent contribution analysis

2026-10-13. **Verdict: TECHNICAL for the complete S295 package, including the necessary, previously unaccepted I128/I131/I290 ingredients.** Full all-rectangle S128 remains UNRESOLVED. This is a contribution judgment under the project's existing standard, not an acceptance decision, an exact-duplicate assertion, or a substitute for an independent full-proof gate.

The standard requires an additional substantive construction, estimate, or structural bridge beyond source operations and standard transfers. A theorem need not already appear verbatim in a paper to be technical under that standard. Conversely, naming Borell and EPI is not enough to classify this theorem. The reduction below includes the difficult soft-kernel interfaces and the linear conclusion, and does not assume L131, Q131b, or B290 as accepted premises.

All OpenAI results and operative proof inequalities at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. I independently read the downstream arguments. Historical words such as “accepted” in I290 do not authorize treating its internal prerequisites as upstream stipulations. The parent authentication is evidence about bytes, not an independent proof pass. The supplied current count is thirteen toward twenty; this review changes neither count nor acceptance.

## 1. Exact object being classified

Let X be uniform on {-1,1}^n, n≥1, and let u:X→[-1,1] be arbitrary. Natural logarithms are used. Set

    ψ(t)=((1+t)log(1+t)+(1−t)log(1−t))/2,
    I(u)=Eψ(u)−ψ(Eu),
    d_a(u)=min_(i,ε=±1) E|u−εaX_i|²,
    Δ_ρ(u)=ψ(ρa)−I(T_ρu).

Fix 0<a₀≤a₁<1 and 0<ρ₀≤ρ₁<1 with ρ₁a₁<1/√2. S295 asserts that a finite C depending only on these four endpoints satisfies

    I(u)=ψ(a), a∈[a₀,a₁], ρ∈[ρ₀,ρ₁]
        ⇒ d_a(u)≤CΔ_ρ(u)

for every n and every u. Bias, endpoint values, rare spikes, and unlimited dependence on other coordinates are included. There is no balance, monotonicity, proximity, singleton, rank, support, or complexity premise. C is existential. Neither its effective value nor the optimal parameter region is claimed.

Frozen I295 analysis, report, and I290 analysis match the three hashes specified in the brief. Their exact checks and the independently read passages are recorded in input-authentication.json.

## 2. What the sources supply, and what they do not

The actual [family119 main](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/main.tex) already has arbitrary soft-channel contraction (`main:soft`), the exact coordinate energy split, and the mean-sensitive production envelope (`upgrade:production`). Its proof files additionally supply a unique common-budget optimizer (`canonical:priced`, `canonical:coverage`), the variance-refined deterministic capacity, strict common-corner derivative losses, and the comparison with the one-corner wall. Those are the structural inputs to the marked sector; S295 does not introduce another optimizer.

[Ky–Tran stability v1](https://arxiv.org/html/2609.31797v1), Theorem 1.1, is global dimension-independent Boolean stability. Its proof already uses production, local hypercontractive control, spectral/marked sectors, and quantitative compression. It does not directly imply S295: Boolean Parseval gives Eu²=1 and distance (1−max|û(i)|)/2, while its entropy clock starts with EH(f)=0. The soft kernel has neither identity. Its companion's bounded variance and real-field martingale lemmas are useful comparisons, but the Boolean clock does not acquire a soft endpoint by substitution.

[Chen et al. v2](https://arxiv.org/html/2609.24931v2), Lemmas 8.1 and 9.2 and their semigroup deduction, cover arbitrary interior arrays and arbitrary pair couplings. Keeping the actual initial information in the scalar integration supplies the sharp soft contraction already present upstream. These operations do not state the global soft deficit-to-coordinate estimate. I do not infer an exact duplicate from them.

[Yu v5](https://arxiv.org/html/2410.10147v5), Theorems 4.1, 4.2, 4.5 and Lemma 4.4, treats balanced Boolean local optimality and real-function hypercontractivity. It provides a close methodological comparison for rare-error smoothing, rather than the target soft theorem itself. The pinned Hellinger companion's `thm:main` is Boolean and concerns a different profile; its main proof strategy supplies no exact-information soft stability assertion.

Thus the technical verdict requires a reduction through the stronger pinned operations and standard methods, not a bare invocation of published Boolean stability.

## 3. Concrete reduction: compression and local linear stability

### 3.1 Soft compression is a quantitative version of the existing sorting proof

Sort each coordinate fiber increasingly. Minimum and maximum preserve previously established monotonicity. Sorting preserves the full multiset of values, hence the mean, M=Eu², and the exact information. Convexity of ψ gives a nonnegative total information gain L_gain. This proof does not require Boolean values.

For a coordinate attaining c=ĝ(i), immediately before its sort write the field as b+X_i d. Other sorts preserve its singleton. Therefore Ed=û(i)=b_i, E|d|=c, Ed²≤M. The even output function

    q↦[ψ(T_ρ b+ρq)+ψ(T_ρ b−ρq)]/2

has second derivative at least ρ² on its feasible interval. Positivity of noise gives |T_ρd|≤T_ρ|d|. Jensen and the nonconstant spectral bound give, at that sort,

    gain ≥ (ρ²/2)(||T_ρ|d|||₂²−||T_ρd||₂²),
    (1−ρ²)(c²−b_i²)≤2L_gain/ρ²+ρ²(M−c²).

The replacement for the Boolean identity Ed²=E|d| is simply Ed²≤M. Since d_a(g)=M+a²−2ac≥M−c² and ≥(a−c)², if d_a(g)≤a²/4 then c≥a/2. Choosing the sign of the original coordinate to match b_i yields

    d_a(u)≤[1+4ρ²/(1−ρ²)]d_a(g)
               +8L_gain/[ρ²(1−ρ²)].

When d_a(g)>a²/4, use d_a(u)≤4≤16d_a(g)/a₀². Hence

    d_a(u)≤C_comp[d_a(g)+L_gain],
    Δ_ρ(u)=Δ_ρ(g)+L_gain.

This reproduces Q131b from the quantitative sorting method, with the full soft scope and uniform constants. It is an extension of the calculation in Ky–Tran Lemma 3.3, not application of that Boolean statement unchanged.

### 3.2 The local estimate includes endpoints and spikes

At v=aX₁, use the constrained functional

    G(u)=ψ(ρa)−I(T_ρu)+k[I(u)−ψ(a)],
    k=ρatanh(ρa)/atanh(a).

Its first variation vanishes. Its full Hessian, for h=u−v and m=Eh, is

    Q(h)=k[Eh²/(1−a²)−m²]
             −[E(T_ρh)²/(1−ρ²a²)−m²].

Every nonconstant Walsh mode has coefficient at least

    q=k/(1−a²)−ρ²/(1−ρ²a²)>0;

the constant mode has coefficient a²q. Positivity is equivalent to strict decrease of (1−t²)atanh(t)/t. Thus a compact endpoint rectangle gives Q(h)≥c_H||h||₂² and k≥k_min>0. This is a scalar nondegeneracy calculation, not a new spectral estimate.

To obtain L2 rather than L∞ coercivity, fix a small η and split h=g+b at |h|≤η. If ε=||h||₂ and p=P(|h|>η), then p≤ε²/η². With A=(1−a²)⁻¹, the exact Bregman identity is

    G(u)=k E Bψ(v+h,v)−E Bψ(T_ρv+T_ρh,T_ρv)
                  +(1−k)ψ(m).

On the good set Taylor expansion lower-bounds the input by kA||g||₂²/2−O(η)||g||₂²; on the bad set ψ''≥1 supplies k_min||b||₂²/2. The output center stays in a compact interval inside (-1,1), although the output itself may reach an endpoint. For some 2<q₀≤min(3,1+ρ₁⁻²), continuity at endpoints and Taylor near zero give

    |Bψ(x+z,x)−ψ''(x)z²/2|≤C_out|z|^q₀,
    |x|≤ρ₁a₁, x+z∈[-1,1].

Real-function hypercontractivity pays the output remainder by C_out ε^q₀. It also gives

    ||T_ρ b||₂≤p^θ||b||₂,
    θ=1/(1+ρ₁²)−1/2>0.

The good quadratic terms, including the good mean square, equal Q(g)/2. The bad output square is O(p^(2θ))||b||₂², and the cross terms cost O(p^θ+√p)||g||₂||b||₂. Young's inequality absorbs them into the strictly positive good and bad input terms, for small ε. Finally absorb ε^q₀ because q₀>2. Therefore

    I(u)=ψ(a), ||u−ε₀aX_i||₂≤ε_*
        ⇒ Δ_ρ(u)≥c_*||u−ε₀aX_i||₂².

All constants depend only on the endpoints. This reconstructs L131, including its important rare-spike scope. The proof is a coercive Hessian plus the same hypercontractive small-support payment used in primary local stability arguments. The changes needed for the soft input have been displayed; L131 has not been removed from the contribution package merely because it was written earlier.

## 4. Concrete reduction: global entrance in the marked sector

### 4.1 The joining equality is extracted from existing strict margins

Use H=log2−ψ, F(ψ(r))=ratanh(r), S=F−2I, and the source envelope Φ_m=max(F,B_m). For a pair law μ of (A,B) on [-1,1]², define its joining loss

    J(μ)=Ec(A,B)+[Φ_(EA)(I_A)+Φ_(EB)(I_B)]/2−Φ_m(I),
    c(A,B)=(A−B)(atanh A−atanh B)/4,
    δ=(EA−EB)/2, m=(EA+EB)/2.

Extend cost by zero at equal corners and infinity at other boundary pairs. If δ>0 and Ec<∞, each child entropy is positive and each mean is interior: zero child entropy forces that child to consist of endpoints, and finite cost forces the other child to coincide, contradicting δ>0. Thus the source joining theorem applies, even with common-corner atoms.

Let the source's unique common-budget optimizer have core mass k, separation δ_c=δ/k, and common-corner masses π_±. Put c₀=2−4(log2)²>0. The source `reserve:corner-margin` and `thinning:derivative-loss` with `thinning:window-bound` already retain the inequality

    τW'−W ≥ c₀κ_τ, κ_τ≥τ²δ_c²/8

on the respective physical corner rays. Integrating (W/τ)' and composing the source's two retentions k/(k+π_+) and k+π_− gives

    K−W(parent) ≥ (c₀/8)(1−k)δ².

For a reserve parent (including ties), equality therefore forces k=1. At a deterministic core of nonzero center m_c, the positive entropy series gives

    H(m_c)−(1−m_c²)log2>0.

Consequently the reserve argument is strictly below J_c/(1−m_c²); S is strictly increasing above zero. The deterministic capacity comparison is therefore strict unless m_c=0. Equality also forces Ec=K; source optimizer uniqueness forces the actual law, rather than just its moments, to be that deterministic reflected pair.

For a strict F parent, the source pools the original child informations and compares K with F(I)−F(j). In the one-positive-corner geometry the retained thinning derivative margin gives positive loss when k<1. At k=1 the core has nonzero center, and strict convexity of F gives

    c(core)≥(1−m_c²)F(J_c/(1−m_c²))>F(J_c).

In reflected-core geometry a strict F parent has m>0 and k<1; the source's wall comparison moves the demand to the one-corner endpoint with unchanged cost, where the retained loss is positive. A strict F parent has no equality case. Conversely the deterministic reflected pair (r,−r), 0<r<1, has zero joining loss.

This reconstructs J290 without a new optimization, a quantitative optimizer theorem, or an unproved equality classification. The classification is useful and not stated verbatim in the source, but it is obtained by retaining the explicit strict inequalities of that same proof. The conservative coefficient is a lower bound; no optimal rate is asserted.

### 4.2 Fixed-square compactness gives a dimension-free qualitative modulus

Impose δ≥β>0, j₀≤I≤j₁<log2, Ec≤M. Probability laws on one fixed compact square are weakly compact; lower semicontinuity of c makes the cost sublevel closed. The entropy and mean moments are continuous. Finite cost and separation rule out zero entropy moments and endpoint means throughout that compact set, so their uniform interior bounds are consequences, not extra assumptions.

The profiles are continuous there, including their seams and ties; J is lower semicontinuous. The distance to the reflected pair of radius ψ⁻¹(I) is continuous. On the closed subset where that distance is at least any fixed tolerance, J has positive minimum by the equality classification. This is the usual compact-minimum argument. It uses no compactness of growing cubes and needs no effective modulus.

For an interior cube field g and any specified coordinate i, the source's energy split gives

    D(g)−F(I(g))
      =[D(g_+)−Φ_(Eg_+)(I_+) + D(g_−)−Φ_(Eg_−)(I_−)]/2
           +J(μ)+Φ_(Eg)(I(g))−F(I(g)) ≥ J(μ).

Also Ec≤D(g). Small production surplus and |ĝ(i)|≥β consequently imply small L2 distance to the signed soft coordinate at that specified i. This is P290, valid with arbitrary remaining face dimension and bias.

### 4.3 Ordinary differential comparison and the original budget finish the sector

For P_s=T_(e⁻ˢ), t=−logρ, write y=I(P_su), w=ψ(ae⁻ˢ), z=w−y, R=D(P_su)−F(y). Pinned production and flow give

    z'=R−Az, 2≤A≤K=max_[0,ψ(a₁)]F',
    ∫₀ᵗR≤e^(Kt_max)Δ,
    z(s)≤e^(Kt_max)Δ (0≤s≤t), t_max=−logρ₀.

The second bound integrates toward the terminal time and drops future nonnegative surplus. Positive-time smoothing and finite-cube continuity justify boundary inputs. These are P128's integrating-factor consequences.

If |û(i)|≥β, select s in the middle third of [0,t] with R(s)≤3e^(Kt_max)Δ/t_min, t_min=−logρ₁>0. For small Δ, the information stays in a compact positive interval, and the marked singleton of P_su is at least ρ₀β. The preceding modulus gives arbitrarily small

    q=||P_su−εae⁻ˢX_i||₂².

The original budget is essential for returning to u. Strong convexity at b_iεX_i, b_i=E[uεX_i], proves

    ||u−εaX_i||₂²≤2[ψ(a)−ψ(b_i)+ψ(Eu)]+(a−b_i)².

Here |b_i−a|≤√q/ρ₀ and (Eu)²≤q. On a fixed scalar neighborhood this yields

    ||u−εaX_i||₂²
      ≤2atanh((1+a₁)/2)√q/ρ₀+2(log2)q+q/ρ₀².

This is a budget-assisted convexity estimate, not inverse noise. Choose the modulus tolerance to enter §3.2's local neighborhood. The local estimate then supplies the **linear** bound at the original u. For larger Δ, d_a≤4 pays the bound. Thus every fixed β sector satisfies d_a≤C_βΔ, without closeness, balance, endpoint, or complexity hypotheses. This reproduces B290, together with L131 and E131 rather than assuming their acceptance.

## 5. Concrete reduction: paying the diffuse sector on the restricted rectangle

### 5.1 Borell followed by scalar EPI

[Mossel–Neeman v3](https://arxiv.org/html/1210.4126v3), Theorems 1.1–1.2 and full §2, supplies Borell's two-set comparison. For any Gaussian field v, shift to f=(1+v)/2 and let f* be its increasing scalar quantile. Layer cake compares ∫_A Q_σf with the integral of Q_σf* on the upper ray of the same measure, for every output set A. The nested input rays all come from the same quantile, so their comparisons are compatible. Largest-p integrals then imply all stop-loss inequalities; equal means give convex order. Applying ψ(2x−1) preserves the entire input law and yields

    I_G(v*)=I_G(v), I_G(Q_σv)≤I_G(Q_σv*).

This is a standard rearrangement consequence of Borell, not a new noise-stability inequality.

For scalar w, make a binary sign B with conditional mean w(Z). Its posterior densities are φ(z)(1±w(z))/(1±m), m=Ew. At positive information both weights are positive. The densities are bounded by a fixed multiple of φ for that field. Second moments and differential entropy are finite even if w reaches endpoints: r log r is bounded on the bounded density-ratio interval, including zero.

Apply ordinary scalar EPI separately to Z|B=± and the independent Gaussian noise, then Jensen to the convex function h↦½log(σ²e^(2h)+(1−σ²)e^(2h₀)). The actual [Rioul primary proof](https://perso.telecom-paristech.fr/rioul/publis/201706rioul.pdf) supplies ordinary EPI with these hypotheses. The result is

    I_G(Q_σw)≤B_σ(I_G(w)),
    B_σ(J)=−½log(1−σ²+σ²e^(−2J)).

Rearrangement **precedes** EPI. Direct multivariate EPI would introduce the dimension factor and is insufficient for this reduction. No balance hypothesis enters the conditional averaging.

### 5.2 An elementary curve comparison supplies a uniform absolute gap

For E(x)=ψ(√x), H_c(x)=e^(−2E(x)), r=√x,

    H_c''/H_c=atanh(r)²/r²
                 −[r/(1−r²)−atanh(r)]/(2r³).

The positive series gives atanh(r)≥r and the bracket ≤r³/(1−r²). Hence H_c''/H_c≥1−1/[2(1−x)]>0 for x<1/2. A strong-convexity chord between 0 and b² gives, uniformly on compact b and σ ranges with b<1/√2,

    ψ(σb)−B_σ(ψ(b))≥(κ/4)σ²(1−σ²)b⁴≥η_G>0,
    κ=e^(−2ψ(b₁))[1−1/(2(1−b₁²))].

This is differentiation, a positive-series bound, and the chord inequality. It supplies the restricted Gaussian gap for arbitrary bias and all Gaussian dimensions. No stability theorem for EPI or equality in Borell is needed.

### 5.3 Standard invariance transfers both budgets

Choose once ρ₁<λ<min(1,1/(√2a₁)); this is exactly where ρ₁a₁<1/√2 is used. Set σ=ρ/λ. If an increasing sequence has Δ→0 and max singleton α→0, §4.3 gives both I(T_λu)→ψ(λa) and I(T_ρu)→ψ(ρa).

Truncate h=T_λu at a fixed degree d, obtaining p. The spectral tail squared is at most λ^(2(d+1)). Monotonicity and boundedness imply 0≤∂_ih≤1, so

    Inf_i(p)≤E(∂_ih)²≤E∂_ih=λû(i)≤α,
    Σ_iInf_i(p)≤d.

The same bounds hold for q=T_σp; on Gaussian space q=Q_σp because p is multilinear. The exact primary comparison is [MOO's published Annals paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n1-p05-p.pdf), Theorem 3.18 under Hypothesis 4 and its full replacement proof, with the distance-to-interval and truncation extensions. First-three-moment matching gives the C4 test error O_d(||test⁽⁴⁾||∞ΣInf_i²)=O_d(α). The mixed fourth-moment estimate is the classical tensorized L2→L4 bound, EB⁴≤9^(d−1)(Inf_i p)².

Clip the Gaussian p to v∈[-1,1]. Transfer clip and ψ∘clip through smooth uniform approximation. For squared distance to [-1,1], smooth convolution has bounded fourth derivative at fixed radius and error O(τ(1+|p|)+τ²); Ep²≤1 pays it. Thus Gaussian clipping costs at most the spectral tail plus o(1). OU L2 contraction also pays clipping at the output. Uniform continuity of ψ on the closed interval pays both expectation and mean errors. First choose d, then let α→0; no growing-degree assertion is required.

Consequently both information budgets transfer with arbitrarily small error. Define b=ψ⁻¹(I_G(v)); this enforces exact Gaussian information without rescaling v. It stays in a compact interval below 1/√2 near λa. Continuity of ψ(σψ⁻¹(J)) compares the output cube curve, while §5.2 leaves a fixed η_G. Choosing all errors smaller than η_G/2 contradicts Δ→0.

Therefore some β,η>0, depending only on the endpoints, satisfy max singleton≤β ⇒ Δ≥η for increasing kernels. In that sector d_a≤4≤4Δ/η. In the complementary sector §4.3 gives C_βΔ. Finally §3.1 transfers the increasing estimate to every arbitrary kernel, with

    C=C_comp max{1,C_β,4/η}.

This completes a standard-method reduction at the **exact full S295 scope and linear rate**. It does not quietly impose a junta, a finite dimension bound, a fair binary output, or a proximity premise. The non-effective constants are precisely what permit qualitative fixed-square compactness and the invariance contradiction.

## 6. Contribution judgment and unresolved boundaries

The completed restricted theorem is a useful new-to-this-project corollary, and the soft adaptations demand care. Nevertheless, every additional ingredient has a concrete reduction above: quantitative sorting via convexity/spectral gap; local L2 coercivity via Hessian/truncation/hypercontractivity; marked equality via strict losses of the existing optimizer proof; uniform entrance via fixed-square compactness; backward entrance via exact-budget convexity; diffuse exclusion via classical rearrangement/EPI/invariance and a scalar curvature computation. The package therefore does not meet this project's stronger requirement of a substantive mechanism beyond pinned operations and standard transfer. This assesses I128/I131/I290 together; it does not classify only I295's last assembly.

The conclusion is not that Ky–Tran, Chen, Yu, or the companion already states S295, nor that there is no publishable value in making the deduction explicit. No worldwide-priority claim follows from a scoped comparison. The parent supplied the Gaussian route and conservative curvature lead; this also limits any author-level priority attribution to I295 alone.

Scalar monotone [-1,1] fields are compact in Gaussian L2 by Helly selection and dominated convergence. OU and bounded entropy are jointly continuous on compact correlation intervals. This optimizer reduction is technical, too. It would turn a proved pointwise strict Gaussian cube-curve inequality into a uniform gap. That pointwise inequality at **all** amplitudes remains unproved here.

Strict EPI is below its own curve, which can exceed the cube curve near high amplitude/correlation. Ordinary LSI strictness addresses D_G−2I_G rather than the nonlinear reserve above F(I_G). [FIL](https://www.normalesup.org/~mfathi/docs/LSI14.pdf) requires posterior Poincaré hypotheses for its strengthened LSI; [ELS v2](https://arxiv.org/pdf/1903.04522v2) has matrix/covariance restrictions for the relevant stronger bounds. Complementary posterior mixtures do not pay those hypotheses or the needed reserve.

[Guo–Wu–Shamai–Verdú v1](https://arxiv.org/pdf/1004.3332v1), Proposition 8 and Appendix D, adds uniform complex nonvanishing and tail-ratio conditions. Gaussian domination of the posterior densities does not establish them. No analytic continuation is imported. These are boundaries of a possible extension, not hidden ingredients of S295.

No blocking internal mathematical gap was found at the operative scopes needed for this contribution reduction. This does **not** issue a separate independent full-proof PASS: that gate must audit the frozen proof as a proof, including all its stated ancillary claims. The decisive contribution classification is TECHNICAL; full all-rectangle S128 is UNRESOLVED; acceptance remains untouched.
