# I325 — global small-information alternative

2026-10-13. **Full S313 has a complete proof after the authorized I334 audit, subject to fresh proof/contribution gates.** Sections 1–7 prove G325, the global small-information endpoint on each fixed interior mean interval. Section 10 independently verifies I334's new uniform biased-production argument; Section 11 audits I332 and combines it with G325 and the finalized compact-rectangle result. Original endpoint values, rare events, and changing finite dimensions are retained. No acceptance or count is changed.

## 1. Target, result, and dependencies

All expectations use the uniform finite cube; n≥1. Let

    ψ(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    I(u)=Eψ(u)-ψ(Eu)=ψ(a),  u∈[-1,1],
    Δ=ψ(ra)-I(T_r u),  d_a=min_(i,s=±1) E(u-saX_i)².

The full target keeps every 0<a≤a1<1 and r∈[r0,r1]⊂(0,1), arbitrary means, original endpoint values, rare events, and dimensions. It asks d_a≤C(a1,r0,r1)a^(-4)Δ.

**G325 (new, interior mean only).** For each m0<1 and the fixed correlation rectangle, there are a_*>0 and c_*>0, independent of dimension, such that every exactly normalized u with |Eu|≤m0 and 0<a≤a_* satisfies

    Δ≥c_* a^4 B,  B=m²+q-max_i û({i})²+H,
    q=Σ_i û({i})², H=Σ_(|S|≥2) û(S)².                 (G325)

Consequently d_a≤C_*a^(-4)Δ in this global, explicitly restricted regime. There is no original-residual tube assumption. This is a small-information theorem, not a claim for unrestricted endpoint means or a replacement for the full S313 question.

The source stipulation is only OpenAI/math revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual main:soft, upgrade:production, scalar:profile-convexity, capacity:onebit/refined, and the flow section were read. Source contraction gives Δ≥0; the capacity bound is used only on a genuine one-bit conditional field. Internal I321 is not stipulated. Its complete analysis and records were read; the operations reused here are audited below. Neither its tube theorem nor a generic nonlinear version of N131 is assumed.

The proof has three new operations: global original-H entrance with paid bad input tails; a dimension-uniform, spike-retaining quartic reduction at H=O(a^4); and relative coercivity in a fixed cone around a balanced coordinate. The third operation preserves the exact one-bit baseline and pays clipping errors relative to the other-singleton mass. It avoids a Gaussian limit and never inverts smoothing.

## 2. Elementary interfaces and their audit

Put h_m=1-m². On a fixed interior base interval |x|≤γ<1,

    Bψ(y,x)=ψ(y)-ψ(x)-atanh(x)(y-x),
    (y-x)²/2≤Bψ(y,x)≤U_γ(y-x)²,  |y|≤1.             (2.1)

The lower inequality is global ψ''≥1. The upper constant is finite by interior Taylor expansion on the diagonal and continuity off it, including y=±1. For 2<p≤3 there is also the global remainder inequality

    |Bψ(x+z,x)-ψ''(x)z²/2|≤C_γ,p |z|^p             (2.2)

whenever x+z is physical. For small z use the interior cubic remainder; away from zero divide a bounded continuous remainder by |z|^p. Thus (2.2) does not differentiate ψ at endpoints.

Let f_r(J)=ψ(rψ^(-1)(J)) and

    k=f'_r(ψ(a))=r atanh(ra)/atanh(a)
      =r²-r²(1-r²)a²/3+O(a^4).                    (2.3)

This profile is concave. Indeed tV'(t)/V(t)=sinh(2V(t))/(2V(t)) increases; comparison at rt and t shows that rV(rt)/V(t) decreases. The extension at zero is smooth. Therefore, for any bounded comparison field v, with β=ψ^(-1)(I(v)),

    Δ(u)≥Δ(v;β)+k[I(u)-I(v)]-[I(T_ru)-I(T_rv)].   (2.4)

This supporting-tangent inequality holds whether I(v) is above or below I(u). No assumed entropy ordering is needed.

We use real-function hypercontractivity only in the following forms, with

    p=min{3,1+r1^(-2)}>2,
    θ=1/(1+r1²)-1/2>0:
    ||T_r z||_p≤||z||_2,
    supp(z) of mass P ⇒ ||T_r z||_2≤P^θ||z||_2.    (2.5)

The real two-point proof in finalized I304 lines 121–126 was read and checked: differentiating (E|A+tBX|^s)^(2/s), 1<s≤2, gives a nonnegative square plus at least 2(s-1)B², by Jensen for the negative power. Locally integrable zeros are handled by continuity. Integrating and tensorizing with Minkowski, then dualizing, gives (2.5). Yu v5 Lemma 4.4 independently states the real-function interface; no Boolean restriction is imposed. For the low-degree projection Π≤1 and a supported z,

    ||Π≤1 z||_2≤C P^(1/4)||z||_2.                 (2.6)

To verify this, dualize against degree≤1 polynomials F of L2 norm one. E F^4≤C follows by expanding the independent signs (E(first chaos)^4≤3||first chaos||_2^4). Hölder gives ||F1_supp(z)||_2≤C P^(1/4). This proof is dimension independent.

For first chaos L=Σ c_iX_i, s²=||L||², E exp(tL)=Π cosh(tc_i)≤exp(t²s²/2). Chernoff gives subgaussian tails and, for every fixed j, ||L||_j≤C_j s. If C_η(L) is symmetric clipping to [-η,η], then, for fixed η>0 and any fixed j,

    ||L-C_η(L)||_j≤C exp(-c/s²)                   (2.7)

for small s; polynomial factors can be absorbed in the exponent. When s=0 the difference is exactly zero. These tail estimates are direct cube calculations, not invariance estimates.

Finally the modal bridge is rederived. If b=max_i|û({i})|, conditional Jensen gives I(u)≥J(m,b)≥ψ(b), because J is even and convex in m (ψ'' is convex). Hence b≤a. With the maximizing coordinate oriented, B=E(u-bX_i)². Cancellation of the Bregman linear term gives

    ψ(a)-ψ(b)≤E Bψ(u,bX_i)≤U_a1 B,
    (a-b)²≤2[ψ(a)-ψ(b)],
    B≤d_a≤(1+2U_a1)B.                             (2.8)

Also Var(u)≤2I(u)≤C a² by strong convexity at the mean. Thus q+H≤C a². Means exactly ±1 cannot have positive information, but approach to those endpoints remains part of the full target.

## 3. Global entrance: the original higher modes are paid

Fix m0<1. Write the actual orthogonal decomposition

    u=m+L+W,  L=Π_1 u,  W=Π_≥2 u, ||W||²=H.

Then ||L||+||W||≤C a. Choose a small fixed η0, depending on m0 and the correlation rectangle, and use the comparison field

    v=m+C_η0(L),  t=L-C_η0(L), e=u-v=W+t.

The symmetric distribution of L makes Ev=m and Et=Ee=0. All values of v and T_rv are in a fixed interior interval. The clipping error t has every fixed norm bounded by E_a=C exp(-c/a²). Constants in these estimates may deteriorate as m0→1. Clipping is only a comparison device; u and its information are not altered.

In (2.4), both entropy differences have exact Bregman expansions. Their linear contribution is

    C_lin=k E[ψ'(v)e]-E[ψ'(T_rv)T_re].

Expand ψ'(m+z)=V(m)+z/h_m+O(z²) on the fixed interior interval. The constant terms vanish. The first-chaos terms involving W vanish exactly by orthogonality and self-adjointness of T_r. The clipped first-chaos errors have size E_a. Moment bounds give

    |C_lin|≤C a²√H+E_a.                           (3.1)

This estimate does not expand the original input spikes.

We next prove, for all small a,

    k E Bψ(u,v)-E Bψ(T_ru,T_rv)≥c H-E_a.           (3.2)

Choose another fixed small η1 and split e=G+Z on disjoint supports at |e|=η1. Let P be the bad support mass. Then P≤C a²/η1²+E_a. On the good set, Taylor gives an input lower bound with quadratic multiplier arbitrarily close to 1/(2h_m), by choosing η0,η1 small. On the bad set retain the exact global lower bound k||Z||²/2. The output bound (2.2) has quadratic multiplier arbitrarily close to 1/(2h_m), because |T_rv-m|≤η0, and remainder at most C||e||_2^p.

At these constant multipliers the quadratic form on degree≥2 has gap at least

    min_(r∈[r0,r1], |m|≤m0) (r²-r^4)/(2h_m)>0.

Its degree≤1 block has bounded operator norm. Formula (2.6) and Π≤1 e=Π≤1 t give

    ||Π≤1 G||²≤C P^(1/2)||Z||²+E_a.

Thus the good quadratic form is ≥c||G||²-C P^(1/2)||Z||²-E_a after the small fixed multiplier errors are chosen. The bad output square costs C P^(2θ)||Z||² by (2.5); its cross term with G costs C P^θ||G||||Z||. Young's inequality spends a fixed fraction of the good gap and C P^(2θ)||Z||². The remaining output remainder satisfies

    C||e||_2^p≤C a^(p-2)(||G||²+||Z||²)+E_a.

Since P→0 and p>2, all these costs are absorbed for small a into fixed fractions of the good gap and the bad input payment k||Z||²/2. This proves a lower bound c(||G||²+||Z||²)-E_a, which implies (3.2), since e=W+t. This proves genuine rare-tail payment: bad residual energy has a positive coefficient, not an uncontrolled O(a^4) remainder.

Source Δ(v;β)≥0 in (2.4), together with (3.1)–(3.2), yields

    Δ≥c H-C a²√H-E_a≥c' H-C' a^4,
    H≤C(Δ+a^4).                                   (E325)

This holds for arbitrary exactly normalized original kernels on the fixed interior mean interval, including endpoints and changing dimensions. If H≥K a^4 for sufficiently large fixed K, it directly gives Δ≥c H and therefore pays a^4B. If Δ=o(a^4), it forces H=O(a^4). The absolute a^4 cost here belongs only to the coarse entrance. It will not be used as a relative error near B=0.

## 4. Uniform quartic reduction with the bad entropy retained

Assume |m|≤m0 and H≤K a^4, for fixed K. All statements in this section are uniform in n,m,r and kernels under these conditions as a→0. Put s²=q=||L||², h=1-m², v=m+C_η0(L), e=W+t as above. Split at the shrinking residual threshold τ=a^(1/2):

    G=e 1_(|e|≤τ), Z=e 1_(|e|>τ), P≤C_K a^3+E_a,
    A_bad=E[Bψ(u,v)1_(|e|>τ)].

Then ||G||+||Z||=O_K(a²), and

    ||Z||²/2≤A_bad≤U_γ||Z||².                    (4.1)

Bad input entropy is retained exactly. By (2.5), ||T_rZ||_2=o(a²); by (2.6), ||Π≤1G||_2=o(a²). Also

    |E L² Z|≤||L²1_bad||_2||Z||_2
            ≤C a² P^(1/4)||Z||_2=o(a^4).          (4.2)

On the good residual set, input Bregman expansion gives

    E[Bψ(u,v)1_good]=||G||²/(2h)+o(a^4).           (4.3)

For clarity, the variation of ψ''(v) is not bounded by a supremum O(a). Restrict first to |L|≤a^(1/2), where that variation is O(a^(1/2)); the complementary first-chaos tail is exp(-c/a), and |G|≤τ controls its integral. The cubic input residual remainder is O(τ||G||²). This proves (4.3) with a uniform o(a^4).

At the output, (2.2) and (2.5) give a remainder O_K(a^(2p))=o(a^4). The multiplier variation is also o(a^4): Hölder with exponents p/(p-2), p/2 bounds it by C||T_rv-m||_(p/(p-2))||T_re||_p²=O_K(a^5)+E_a. Supported Z contributions to the output square and its cross terms are o(a^4). The exact first-chaos linear terms cancel for the total e=W+t before Z is discarded; discarding them separately would be invalid.

With C4=(1+3m²)/(12h³), the exact entropy therefore has the expansions

    ψ(a)=s²/(2h)+C4 E L^4+(m/h²)E L²G
                         +||G||²/(2h)+A_bad+o(a^4),
    I(T_ru)=r²s²/(2h)+C4 r^4 E L^4
                +(m r²/h²)E[L² T_rG]+||T_rG||²/(2h)+o(a^4).
                                                               (4.4)

To check the linear terms, expand ψ'(m+L) through L². The remaining L2 norm is O(a³), and it pairs with O(a²) residual. Terms containing t are exponentially small. Equation (4.2) removes the bad cubic coupling. All leading linear terms in L pair with W to zero. No jet representation for u is assumed.

The first equation gives s²=h a²+O_K(a^4), so s>0 for small a. Set κ=Σ_i c_i^4/s^4 when L=Σ c_iX_i, and G_d=Π_dG. Eliminating s²/(2h) using the exact input equation and ψ(ra)-r²ψ(a)=-r²(1-r²)a^4/12+O(a^6), then completing the level-two square, gives

    Δ = r²(1-r²)a^4[κ m²/(3h)+(1-κ)/6]
       + r²(1-r²)/(2h)||G_2+(m/h)(L²-s²)||²
       + Σ_(d≥3)(r²-r^(2d))||G_d||²/(2h)
       + r² A_bad + o_K(a^4).                     (N325)

The equality means the displayed exact bad entropy remains, while all other errors are uniformly o(a^4). No signed bad-tail remainder is hidden in that error. The negligible degree-zero and degree-one energies of G justify their omission; the scalar component of E L²G is likewise negligible.

Independent algebra audit: E L^4=s^4+V, V=2(s^4-Σ c_i^4). The cross term is r²(1-r²)m E[(L²-s²)G_2]/h². Completing it subtracts r²(1-r²)m²V/(2h³). Substitution of s^4=h²a^4+O(a^6) leaves

    (1+3m²)(h²+2h²(1-κ))/(12h³)
       -m²(1-κ)/h -1/12
       =κ m²/(3h)+(1-κ)/6.

This independently audits the I320/I321 optimized coefficient actually used. The important new point is the uniform reduction (4.1)–(4.4) for arbitrary kernels and changing dimensions with H=O(a^4), not a fixed-cube formal jet. It does not claim an o(a^4B) error.

In particular, the bracket is ≥(m²+1-κ)/12. If Δ=o(a^4), E325 and N325 force

    m→0, κ→1, A_bad=o(a^4),
    ||G_2+(m/h)(L²-s²)||²=o(a^4),
    Σ_(d≥3)||G_d||²=o(a^4), H=o(a^4).              (4.5)

For the last conclusion, ||(m/h)(L²-s²)||=o(a²), (4.1) controls Z, and the low G projection is negligible. Also κ≤max_i c_i²/s²; choosing the largest singleton gives b²/s²→1 and

    L_other²:=s²-b²=o(a²), b²/(h a²)→1.            (4.6)

This is original-kernel entrance to a fixed cone. It is not entrance to the a^M tube. Absolute quartic errors are used only to obtain (4.5)–(4.6); the next step has a relative budget.

## 5. Audit of the in-flight quartic suggestion

Let φ(t)=ψ(t)-t²/2-t^4/12. Direct differentiation gives φ''(t)=t^4/(1-t²)≥0. Hence, for |x|<1 and |x+w|≤1, including endpoints by continuity,

    Bψ(x+w,x)≥w²/2+x²w²/2+xw³/3+w^4/12.          (5.1)

The quartic polynomial Q_x(w) is convex in w, because Q_x''(w)=(x+w)². For x=m+bX_i, other singleton l, and higher chaos W, its tangent yields

    E Q_x(l+W)≥E Q_x(l)
       +E[(x²l+x l²+l³/3)W].

Orthogonality removes E lW, leaving 2mb E[X_i lW] from the first term. First-chaos moment bounds therefore give exactly the proposed bound

    |coupling|≤C[|m|b||l||+(|m|+b)||l||²+||l||³]√H. (5.2)

Thus the suggestion is correct at its stated scope. Alone (5.1) is insufficient: discarding input Bφ while retaining its output curvature can lose a term of order m^4||l||², which can exceed a²||l||² when m^4≫a². We retain the full ψ derivative and exact one-bit baseline below. The second in-flight suggestion has the same coupling structure. Instead of introducing a smooth minorant outside the range, we use a bounded clipped comparison whose errors depend only on ||l|| and vanish relative to a²||l||². No unproved extension property is needed.

## 6. Relative cone coercivity, without a shrinking residual tube

There are small fixed μ,ε,δ>0 and a_c>0, depending only on the correlation rectangle, with the following property. Orient a coordinate and decompose the actual u as

    u=v+l+W, v=m+bX_1=E[u|X_1], b≥0,
    l=Σ_(j≠1) û({j})X_j, L0=||l||, W=Π_≥2u.

If exactly I(u)=ψ(a), a≤a_c, and

    |m|≤μ, L0≤ε a, |b²/((1-m²)a²)-1|≤δ,           (6.1)

then

    Δ≥c[a^4m²+a²L0²+H].                           (R325)

There is no extra H hypothesis: H≤C a² follows from information, and suffices for the output remainder. In particular residuals of order εa are permitted. The following proof handles original endpoint spikes directly.

Choose a fixed small η>0 and define A=v+C_η(l), t=l-C_η(l), e=u-A=W+t. The clip is symmetric, independent of X_1, and has mean zero. Let E_L=C exp(-c/L0²) denote any of its required fixed-norm error bounds, with E_L=0 when L0=0. Choose μ,η,a_c so |A|,|T_rA|≤γ, where γ²<1-r1². No change to u or its information is made.

Applying (2.4) directly to v and splitting both entropy differences through A gives the exact lower comparison

    Δ≥Δ(v;β)+k A_l-O_l
          +k E[ψ'(A)e]-E[ψ'(T_rA)T_re]
          +k E Bψ(u,A)-E Bψ(T_ru,T_rA),            (6.2)

where β=ψ^(-1)(I(v)), A_l=E Bψ(A,v), O_l=E Bψ(T_rA,T_rv). The linear terms in the v→A increment vanish by independence and symmetry. Formula (6.2) uses k at the original exact a, not at β or a replacement amplitude.

### 6.1 Paying the original one-bit bias

Only genuine v is used here. Source capacity and convexity of F(J)-(2/3)J² give D(v)-F(I(v))≥(2/3)m² I(v)². Along its one-bit noise flow, let y(s)=I(T_(e^-s)v), z(s)=ψ(βe^-s)-y(s), R=D-F(y). Exact differentiation gives z'=R-A_sec z, with 2≤A_sec≤K on a fixed small-information interval. If the final z is at least half ψ(rβ), it already dominates c m²β^4. Otherwise y(s)≥y(-log r)≥cβ², so integration of R≥(2/3)m²y² gives the same conclusion. Hence

    Δ(v;β)≥c m²β^4≥c' m² a^4.                    (6.3)

The last inequality follows from (6.1) and I(v)=b²/(2h)+O(b^4). This rechecks the one-bit operation used in I321. It does not apply N131 to u.

### 6.2 Paying other singleton mass relatively

Taylor expansion of Bψ at v and T_rv through cubic order has zero averaged cubic term, since C_η(l) and T_rC_η(l) have symmetric laws and are independent of X_1. Its fourth-order costs are ≤C L0^4. Up to E_L, the quadratic term is

    k A_l-O_l=(Q11/2)L0²+O(L0^4)+O(E_L),
    Q11=k A0-r² B0,
    A0=E_X1[1/(1-v²)], B0=E_X1[1/(1-(T_rv)²)].

Writing h=1-m², uniform analytic expansion gives

    Q11=r²(1-r²)[(1+3m²)b²/h³-a²/(3h)]+O(a^4).

For small μ,δ,a_c this is ≥c a²; its coefficient at m=0, b²=a² is 2r²(1-r²)/3. Taking ε small absorbs L0^4. Thus

    k A_l-O_l≥c a²L0²-C E_L.                     (6.4)

Unlike an expansion at m alone, the exact conditional baseline retains every pure m term.

### 6.3 Paying higher chaos and its nonlinear coupling

Global (2.1), compact output (2.2), the degree≥2 spectral gap, and (2.5) give

    k E Bψ(u,A)-E Bψ(T_ru,T_rA)
       ≥[k/2-r^4/(2(1-γ²))]H-C H^(p/2)-C E_L
       ≥c H-C E_L.                               (6.5)

The first coefficient is uniformly positive after reducing a_c, because k=r²+O(a²) and γ²<1-r1². Terms involving t are estimated by Young and its exponentially small norm; they spend a fixed fraction of H. Since H≤Ca² and p>2, the output remainder is absorbed against the order-one H gap, rather than a²H. This pays endpoint spikes without input Taylor expansion in W.

For the linear term in (6.2), keep full ψ. Expand ψ'(v+l) through l²; clipped differences cost E_L. Conditional orthogonality kills ψ'(v)W. The even X_1 component of ψ''(v)l pairs to zero with W, and its odd coefficient is bounded by C|m|b. The coefficient ψ'''(v) is bounded by C(|m|+b), and the cubic remainder has L2 norm ≤C L0³. The same calculation at T_rv uses self-adjointness of T_r and the same orthogonal cancellations. Therefore

    |k E[ψ'(A)e]-E[ψ'(T_rA)T_re]|
       ≤C K0√H+C E_L,
    K0=|m|aL0+(|m|+a)L0²+L0³.                    (6.6)

This is the full-ψ version of the audited quartic coupling. Young spends cH/2 and CK0², with

    K0²≤C[m²a²L0²+(m²+a²)L0^4+L0^6]
         ≤C(μ²+ε²+μ²ε²+ε^4)a²L0².               (6.7)

Choosing μ,ε small absorbs this cost in (6.4).

All clipping errors are relative: for L0≤εa,

    E_L/(a²L0²)≤C ε² exp(-c/L0²)/L0^4→0

uniformly as a→0, and they are exactly zero at L0=0. The fixed η tails introduce no additive error depending on b or the entire first chaos. Hence they can be absorbed in (6.4) even when B is exceptionally small. Combining (6.2)–(6.7) proves R325. This is a fixed cone result, not a slightly improved a^M exponent.

## 7. Combining the paid operations proves G325

Suppose G325 failed for some fixed m0 and correlation rectangle at arbitrarily small a. There would be exactly normalized kernels, arbitrary finite dimensions, a_k→0 and r_k in the rectangle, with B_k>0 and

    Δ_k/(a_k^4 B_k)→0.

Since B≤m0²+C a² is uniformly bounded, Δ_k=o(a_k^4). E325 gives H_k=O(a_k^4), so the uniform N325 applies. Equations (4.5)–(4.6) give m_k→0, H_k=o(a_k^4), and, after choosing the largest singleton, L0,k/a_k→0 and b_k²/((1-m_k²)a_k²)→1. Thus the fixed hypotheses (6.1) hold eventually, independently of dimension. R325 then gives

    Δ_k≥c[a_k^4m_k²+a_k²L0,k²+H_k]≥c a_k^4 B_k,

contradiction. This establishes uniform constants a_*,c_* for the entire fixed interior mean interval. If B=0, the modal bridge already gives d_a=0. No division by B in that case is used. Closed correlation endpoints, n=1, rare events, original values ±1, and changing dimensions are covered by the estimates above.

The contradiction uses an absolute o(a^4) only to enter the fixed cone; the final payment is relative and contains no such error. It never claims that the absolute normal-form remainder is o(a^4B). Constants are obtained by contradiction and the explicit local cone estimates, not by numerical scans. The earlier a^M tube is not used.

## 8. Endpoint limitation of G325 alone

G325 does not control sequences |m|→1. In E325, the comparison interior interval, ψ-derivative bounds and clipping margins depend on m0. In N325 the coefficients contain h^(-1), h^(-2), h^(-3), and its error uniformity was proved only for h≥1-m0². None may be sent to h=0 without new payment. Small information does not imply small relative fluctuations at an endpoint mean. Rare Boolean outputs remain in the full target.

The source production profile is not a substitute. It gives max{F(J), B_m(J)}, with

    B_m(J)=2J+h S(L-(H_binary(m)-J)/h), h=1-m².

Its surplus branch vanishes whenever J≤H_binary(m)-hL. This threshold is positive for nonzero interior m. Therefore the source's already-stated max-profile inequality alone does not supply the nonlinear bias gap D-F(I)≥c m²I² in this sector. Its absence is not a refutation. The stronger claim requires the new quantitatively paid joining argument of Section 10.

At this stage G325 alone leaves full S313 unresolved. The authorized later I334 candidate supplies a different uniform production operation, audited in Section 10. Section 11 then pays the endpoint means and completes the original target. No exactly normalized counterexample is found. The limitation in G325's own constants is not removed or hidden by that combination.

## 9. Validation, substantiality, priority

Correctness claim: E325, the spike-retaining uniform N325, R325, and their combination G325 are proved at their explicitly stated hypotheses. Sections 10–11 additionally verify the authorized I334 candidate and complete full S313. The parent suggestions and production candidate were audited, not stipulated. Validation is analytic and includes exact coefficient algebra, real norm interfaces, source joining hypotheses, and fresh pinned source byte comparisons. No formal checker or numerical scan was used.

Substantiality claim: G325 closes the global fixed-interior-mean component; the independently audited parent production candidate closes the complementary endpoint means. The resulting full endpoint package is one connected proposed contribution, not separate acceptance nominations for its ingredients. Fresh independent proof and contribution gates still remain. The parent reported acceptance of R021 during this turn and a current count of 15/20. This task makes no acceptance or count edit and does not claim another acceptance for I325.

Worldwide priority: no claim. Focused primary literature reading covers Yu v5's Boolean local statements and real hypercontractivity interface; their hypotheses do not state G325. This comparison is not an exhaustive worldwide search. The standard subgaussian, Bregman, and norm operations are not claimed novel, and inherited one-bit/modal/source results are not counted as new findings.

## 10. Independent attack on the authorized I334 candidate

The parent authorized this additional audit before finalization. The complete 139-line I334 candidate and complete 41-line I332 reduction were read. I334's immutable read identity is 4a733cd467b7ebca97c10cb4ec90ebd99d4ded4de5b925989fb3560c1cae899a; I332 is 299f7e7db1c3ee99933d22cb6935848195407cc77cbd9083445e842a153478e8. They are internal candidates, not axioms. Actual scalar, canonical coverage/geometries, reserve joining, thinning derivative/window and upgrade high-information/wall statements were read from the pinned primary source before checking the new steps.

**Audit conclusion:** the claimed uniform biased-production inequality passes this independent analytic check. No repair or added restriction is necessary. The proof, including the extra payment not supplied by the source theorem, follows.

Let L=log 2 and F(ψ(t))=t atanh(t). Write H_b=L-ψ, h=1-m² and S=F-2I with the source's zero extension. Its actual scalar results give

    F'≥2, F''≥μ:=1/(2L²),
    F''(I)≤M/(L-I)², M=4L²/3,
    δ0=2-3M=2-4L²>0,
    η=2-max_[0,L/2](F''/F')>0.                    (10.1)

The lower μ follows from the source's scaled-curvature lower bound. The last strict margin is source wall:rate-slope, including zero by smoothness and compactness. Put k0=L-1/2 and Ξ(I)=(I-k0)S'(I)-S(I). Actual upgrade:high-information proves Ξ(L/2)>0, Ξ increasing above L/2, and

    B_m(I)-F(I)≥m²Ξ(I), I≥L/2.                   (10.2)

Choose the following absolute constants:

    A=μ/2, B0=δ0/8, C0=4L²+3L/2,
    c=(1/2)min{μ/8,B0/C0,η,Ξ(L/2)/L²}>0.

Define G(m,I)=F(I)+cm²I² and P_m(I)=max{B_m(I),G(m,I)}. The Hessian of G has entries 2cI², 4cmI, F''+2cm². Its determinant is 2cI²(F''-6cm²)≥0 and both diagonals are nonnegative. Thus G is jointly convex on the full rectangle (-1,1)×[0,L), not merely a nonconvex physical subset. This addresses a possible pooling obstruction. Equations (10.2) and cL²≤Ξ(L/2) show B_m≥G above half information. At m=0 they agree. Hence a strict G-parent branch has 0<I<L/2 and nonzero m.

### 10.1 Strict common-output slack and the added demand

Use the source's one-positive-corner path with interior core center x_c≥0, half difference d_c>0, σ_c=1-x_c>d_c, core information J_c and mass λ∈(0,1]. Its state has

    x=1-λσ_c, I=H_b(x)-λe_c, ν=average child information,
    J=I-ν, cost=λ c_core.

The exact source Euler derivative and window bound give, with Δ_F=F(I)-F(ν),

    λΔ_F'-Δ_F≥δ0 κ,
    κ=-(1/2)log(1-λ²d_c²/(1+x)²)≥λ²d_c²/8.

No derivative is taken holding the moving cutoff fixed incorrectly: the source computes both path derivatives before its auxiliary entropy integration. Integrating (Δ_F/λ)' from λ to 1 gives the actual retained slack

    λF(J_c)-[F(I)-F(ν)]≥B0 λ(1-λ)d_c².           (10.3)

At λ=1 this is zero, as it must be. The core capacity statement gives c_core≥αF(J_c/α), α=1-x_c², with J_c/α<L. Since R(I)=F(I)-μI²/2 is convex and R(0)=0, perspective comparison gives

    c_core-F(J_c)≥A(α^(-1)-1)J_c²≥A x_c²J_c².    (10.4)

This uses a genuine deterministic core only; it is not a generic nonlinear N131 substitution.

For the additional G demand, the independent flag chain rule gives

    I=λJ_c+E_λ,
    E_λ=h_bin(λσ_c/2)-λh_bin(σ_c/2),
    J≤λJ_c.                                      (10.5)

The last inequality is data processing for the fair input after discarding an independent flag. For g(t)=-(1-t)log(1-t), -2≤g''≤-1 on [0,1/2], so convexity of g+t² and concavity of g give

    0≤g(λp)-λg(p)≤λ(1-λ)p², p=σ_c/2.

Separating -t log t and using σ_c≤1, 1-λ≤log(1/λ) yields

    0≤E_λ≤(3/4)λσ_c log(1/λ).                    (10.6)

The actual core posterior identity and ψ(t)≤Lt² give

    J_c≤Ld_c²/[σ_c(1+x_c)],
    σ_cJ_c≤Ld_c², J_c²≤L²d_c².                  (10.7)

The second squared bound uses d_c<σ_c and 1+x_c≥1. It is uniform even near an endpoint core; no interior margin is lost.

Now x=x_c+(1-λ)σ_c, so x²≤2x_c²+2(1-λ)². Equations (10.5)–(10.7) give

    x²(I²-ν²)=x²J(2I-J)
       ≤2λ²x²J_c²+(3/2)λ²x²σ_cJ_c log(1/λ)
       ≤4λx_c²J_c²+C0 λ(1-λ)d_c².               (10.8)

For the first term use λ²≤λ and λ²(1-λ)²≤λ(1-λ), together with J_c²≤L²d_c². For the second use x²≤1 and λ log(1/λ)≤1-λ. These inequalities verify the constants in the parent's proposed payment, including λ→0. Since 4c≤A and cC0≤B0, (10.3), (10.4), and (10.8) imply

    λ c_core≥G(x,I)-G(x,ν).                       (10.9)

This holds throughout the source's one-positive-corner branch, including capacity λ=1 and the reflected-core transition x_c=0. No mass or entropy is silently changed.

### 10.2 Reflected cores and the upgraded wall

Fix physical d,e and 0<m with I=H_b(m)-e≤L/2, j=[H_b(m+d)+H_b(m-d)]/2-e, J=I-j>0. Let W0=atanh(m)>0 and Q0=[atanh(m+d)+atanh(m-d)]/2. The source proves Q0/W0≥exp(2J). Integration of F''/F'≤2-η on [j,I] gives F'(I)/F'(j)≤exp((2-η)J). Hence

    Q0F'(j)-W0F'(I)≥2η W0J.                     (10.10)

Indeed F'(j)≥2 and exp(2J)-exp((2-η)J)≥ηJ. Differentiate the new demand at fixed d,e:

    ∂_m[G(m,I)-G(m,j)]
       =Q0F'(j)-W0F'(I)
         +2cm(I²-j²)+2cm²(jQ0-IW0).

The middle correction is nonnegative. Q0≥W0 and j≥0 give jQ0-IW0≥-JW0; m²≤1 bounds the last correction below by -2cW0J. Thus the derivative is ≥2(η-c)W0J>0. This verifies the quantitative margin, rather than merely invoking the source's monotonicity for the old potential.

The exact reflected optimizer has d=kr, e=kH_b(r), cost=d atanh(r), and 0<m≤ell=1-k. Moving m to ell keeps d,e,cost fixed and remains physical; I decreases and stays below L/2. The upgraded demand therefore increases, and its wall value is paid by (10.9). That pays every reflected strict-parent branch. The cases ell=m, j=0, and k=1 cause no division or missing limit; k=1 forces m=0 and belongs to the reserve branch.

### 10.3 Original child budgets and induction

For an arbitrary child pair law with positive individual entropies e_a,e_b, keep its actual means a,b and actual information I_a=H_b(a)-e_a, I_b=H_b(b)-e_b. Put m=(a+b)/2, e=(e_a+e_b)/2, I=H_b(m)-e, j=(I_a+I_b)/2.

If the parent P is a reserve value, the stipulated reserve:joining inequality pays it because the child P values dominate the child reserves. Otherwise reflect and swap to m>0,d=|a-b|/2>0. The actual law is feasible for the exact common-average-budget canonical cost K(m,d,e). Its source coverage/geometries and (10.9)–(10.10) give

    E c(A,B)≥K(m,d,e)≥G(m,I)-G(m,j).

Joint convexity, at the *original* individual child states, gives

    [P_a(I_a)+P_b(I_b)]/2
       ≥[G(a,I_a)+G(b,I_b)]/2≥G(m,j).

For d=0, I=j and the same convexity plus nonnegative cost suffices. Thus every branch satisfies the full joining inequality for P. No canonical individual entropies are substituted for e_a,e_b; this was a crucial potential failure checked explicitly.

At dimension zero, P_m(0)=0: the reserve argument is nonpositive by H_b(m)≥L(1-m²), and G(m,0)=0. Induct using the exact source decomposition

    D(u)=[D(u_+)+D(u_-)]/2+E c(u_+,u_-).

Every face of an interior field has positive entropy, so all joining uses are physical. This proves independently the new inequality

    D(u)≥F(I(u))+c(Eu)² I(u)²                     (BP325)

for all finite dimensions and all interior means, with one absolute c>0. The generator normalization matches D=(1/4)Σ_i E[(u-u^(i))(V(u)-V(u^(i)))]=E[V(u)Nu]. Initial endpoints are handled at positive noise time as in the source; no finite initial production is needed for the consequence below.

## 11. Full S313: audited semigroup reduction and compact joining

Fix the original a1,r0,r1, and K=max_[0,ψ(a1)]F'<∞. For any exactly normalized original u, including endpoint-valued u, set t=-log r, y(s)=I(T_(e^-s)u), w(s)=ψ(ae^-s), z=w-y and R=D-F(y). At every s>0 a nonconstant finite-cube input becomes interior; its mean remains m. Source contraction and BP325 give y≤w and R≥cm²y². Direct differentiation yields z'=R-A_sec z, 2≤A_sec≤K. Integrating first from positive time and then taking its zero limit gives

    Δ=∫_0^t exp(-∫_s^t A_sec(v)dv)R(s)ds.         (11.1)

If Δ≥w(t)/2, then Δ≥r0²a²/4≥r0²a^4/4. Otherwise monotonicity of information gives y(s)≥y(t)>w(t)/2≥r0²a²/4 throughout [0,t], so

    Δ≥c m² r0^4 a^4(1-r1^K)/(16K).               (11.2)

In particular |m|≥1/2 implies Δ≥c_b a^4 with c_b>0 depending only on the fixed rectangle and a1. Since d_a≤Eu²+a²≤2, this proves the requested inequality uniformly for those means, even as |m|→1. This independently verifies I332 with the now-proved stronger hypothesis; no relative-fluctuation assertion or factor (1-m²)^(-1) is needed.

For |m|≤1/2 and small a, use G325 with, for example, m0=3/4 and the modal bridge. All remaining amplitudes are bounded away from zero. The inherited finalized I304/R020 compact-rectangle theorem says that for every fixed 0<a0≤a1<1,

    d_a(u)≤C_compact(a0,a1,r0,r1)Δ_r(u)            (11.3)

for all means, endpoint values, and finite dimensions. Its complete report and 319-line independent proof were newly read in this audit; both immutable identities match the I321 brief. It is an internal proved result, not another stipulated upstream theorem. Its used argument was checked at the operational scope: exact earlier-time integrating-factor budget; law-preserving soft compression; local spike payment; marked-singleton joining equality/compactness; the non-strict Gaussian interface and strict scalar gap; fixed-degree transfer of both exact entropy budgets; and the endpoint-dependent diffuse/marked dichotomy. The positive lower amplitude is fixed before its errors and constants are chosen. No small-information rate is extracted from this theorem. Its full proof remains in the authenticated finalized analysis, rather than being silently treated as a vanishing-a Gaussian estimate.

Choose a0 smaller than G325's positive threshold. Equations (11.1)–(11.3), G325 and (2.8) then cover every 0<a≤a1 and every mean. Since a≤a1<1, (11.3) also implies its weaker a^(-4) version. Taking the maximum of these fixed constants proves precisely

    d_a(u)≤C(a1,r0,r1)a^(-4)[ψ(ra)-I(T_ru)]        (S313)

for all finite n≥1, all r∈[r0,r1], arbitrary u∈[-1,1], and exact I(u)=ψ(a). Endpoint means exactly ±1 cannot have a>0; approach to them is covered uniformly by (11.2). No counterexample family or approximate renormalization is used. The earlier one-bit obstruction to any exponent below four remains inherited sharpness, not a new acceptance.

**Final proof verdict:** complete target proved by the new fixed-interior endpoint proof, the independently verified parent biased-production upgrade, and the inherited fully reviewed compact-amplitude theorem. This changes the mathematical verdict of the earlier draft, not the project's acceptance state. Fresh independent proof and contribution gates for this connected endpoint package remain necessary before acceptance. Count stays at the parent-reported 15/20; no worldwide-priority claim is made.
