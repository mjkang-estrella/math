# I313 — analytic endpoint research

2026-10-13. **Developed gap record; S313 remains unproved and unrefuted.** The parent obstruction and one-coordinate upper bound pass independent calculation. Proved partials below establish the sharp endpoint for every bounded affine Walsh field, an amplitude-independent compression transfer, a universal modal distance bridge, and a shrinking spike-tolerant local neighborhood. These are not an unrestricted theorem or an acceptance.

## 1. Target and source boundary

X is uniform on {-1,1}^n, n>=1; T_r is product noise. All logarithms are natural. Write

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2, V(t)=atanh(t),
    I(u)=E psi(u)-psi(Eu)=psi(a),
    Delta_r(u)=psi(ra)-I(T_r u),
    d_a(u)=min_(i,s=±1) E|u-s aX_i|^2.

For each 0<a1<1 and 0<r0<=r1<1, S313 asks for C=C(a1,r0,r1) such that d_a(u)<=C a^(-4)Delta_r(u), simultaneously for all n, 0<a<=a1, r in [r0,r1], and arbitrary u in [-1,1]. Bias, original endpoints, spikes and unrestricted complexity are included.

Only the exact OpenAI results at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. Actual `main:soft` covers arbitrary soft kernels at actual information and all correlations. `upgrade:production` gives D(g)>=max{F(I(g)),B_(Eg)(I(g))} for interior fields, with D(g)=E[V(g)Ng], N chi_S=|S|chi_S, F(psi(t))=tV(t). `scalar:profile-convexity` gives F''>=4/3 and smoothness including zero. `capacity:onebit` / `capacity:refined` gives D(m+tX)>=(1-m^2)F(J(m,t)/(1-m^2)), for a genuine one-bit channel with |m|+t<1. The Hellinger companion's `thm:main` is Boolean. All nine freshly retrieved pinned source files matched local bytes; hash authentication is distinct from semantic reading.

I128 P128, I131 N131 including its immediately following warning, and I131 Q131/L131 were read at their proofs. Finalized I299, I301, I303 and authorized I304 were read at the scopes recorded in the log. Both supplied I304 hashes match. I304's full compact-rectangle PASS is respected; it proves no small-a rate. I312 and I314 were not read. Old live-status/count sentences in historical reports are not current premises.

For P_s=T_(exp(-s)), t=-log r, set y(s)=I(P_su), w(s)=psi(a exp(-s)), R(s)=D(P_su)-F(y(s)), z=w-y. Directly checking P128 gives

    z'=R-Az, 2<=A<=K=max_[0,psi(a1)]F',
    Delta=integral_0^t exp(-integral_s^t A(v)dv)R(s)ds.    (1)

R>=0 follows from source production. Original endpoints use integration from positive time and continuity at zero. Also z(s)<=exp(Ktmax)Delta for s<=t, tmax=-log r0. Every later argument retains the original exact information.

## 2. Independent parent audit

For fixed 0<|m|<1 put h=1-m^2. The derivatives are psi''(m)=1/h and psi''''(m)=2(1+3m^2)/h^3, so

    J(m,b)=b^2/(2h)+(1+3m^2)b^4/(12h^3)+O_m(b^6).

The analytic inverse in b^2 of J(m,b)=psi(a) has positive derivative at zero. Equating coefficients gives

    b^2=h a^2-(2/3)m^2 a^4+O_m(a^6),
    Delta_r(m+bX)=[r^2(1-r^2)m^2/(3h)]a^4+O_(m,r)(a^6).

Admissibility |m|+b<1 holds for small a; information is exact, not its Taylor approximation. Since d_a=m^2+(a-b)^2,

    lim_(a->0) a^4 d_a/Delta=3h/[r^2(1-r^2)]>0.

Thus every p<4 fails. The error is for fixed m,r; no uniform expansion over kernels follows.

For the parent upper bound, one-bit capacity and convexity of F(x)-(2/3)x^2, which is zero at zero, give

    D(m+bX)-F(J)>=(2/3)m^2 J^2.                         (2)

Orient b>=0. J(m,b)>=psi(b), hence b<=a. Also J(m,b)<=psi(|m|+b), so a<=|m|+b and d_a<=2m^2. If Delta>=w(t)/2, then Delta>=r0^2a^2/4>=r0^2m^2a^4/4. Otherwise y(s)>=y(t)>w(t)/2>=r0^2a^2/4, and (1),(2) give

    Delta>=m^2a^4r0^4(1-r1^K)/(24K).

The parent's c and upper constant 2/c are correct. The case m=0, n=1, closed parameter endpoints and original ±1 values check, the latter at positive time. N131 has not been imported as general production coercivity.

## 3. B313: universal modal distance bridge

For 0<=gamma<1 define

    U_gamma=sup_{|x|<=gamma, |y|<=1} Bpsi(y,x)/(y-x)^2,
    Bpsi(y,x)=psi(y)-psi(x)-V(x)(y-x),

with psi''(x)/2 on the diagonal. This finite scalar constant includes endpoint y: near the diagonal use an interior derivative bound; away from it use continuity of psi and bounded V(x).

For any admissible u, let m=Eu, b=max_i |uhat(i)|, q=sum_i uhat(i)^2, H=sum_{|S|>=2}uhat(S)^2, eta^2=q-b^2. Jensen conditional on the maximizing coordinate gives I(u)>=J(m,b). The function J(m,b) is even and convex in m, since its second m derivative is [psi''(m+b)+psi''(m-b)]/2-psi''(m)>=0. Thus J(m,b)>=psi(b), and b<=a<=a1, including endpoints by continuity.

Orient that coordinate and write u=bX_i+w. Then E[X_iw]=0 and Ew^2=m^2+eta^2+H. Cancellation of the Bregman linear term gives

    psi(a)-psi(b)<=E psi(u)-psi(b)<=U_a1(m^2+eta^2+H).

Strong convexity gives (a-b)^2<=2[psi(a)-psi(b)]. Parseval therefore proves

    B=m^2+eta^2+H <= d_a(u) <= D0 B,
    D0=1+2U_a1.                                        (B313)

This pays the amplitude mismatch even for arbitrary endpoint kernels. S313 is equivalent up to D0 to Delta>=c a^4B. The latter remains missing in general.

## 4. Q313: compression without an additional amplitude loss

Use I131's actual soft sorting construction. It preserves input law and exact information, yields increasing g, and has Lgain=I(T_rg)-I(T_ru)>=0. Write M=Eu^2=Eg^2, c=max_i ghat(i), d=d_a(g). The established marked gain inequality is

    (1-r^2)(c^2-b_i^2)<=2Lgain/r^2+r^2(M-c^2).

For d<=a^2/4 its original proof gives

    d_a(u)<=[1+4r^2/(1-r^2)]d+8Lgain/[r^2(1-r^2)].

For d>a^2/4 avoid the old d_a(u)<=4 step: c<=sqrt(M) and d>=(sqrt(M)-a)^2 imply sqrt(M)<=a+sqrt(d). Consequently

    d_a(u)<=M+a^2=d+2ac<=d+2a^2+2a sqrt(d)<=13d.

Thus

    d_a(u)<=C_Q[d_a(g)+Lgain],
    C_Q=max{13,1+4r1^2/(1-r1^2),8/[r0^2(1-r1^2)]}.       (Q313)

C_Q is independent of a. Since Delta(u)=Delta(g)+Lgain and a<=1, an a^(-4) theorem for increasing kernels transfers at the same order. The older 16/a0^2 factor is avoidable; it is not the remaining endpoint obstruction.

## 5. A313: sharp endpoint for all bounded affine Walsh fields

**Proved partial theorem:** S313 holds for u=m+sum_i b_iX_i, with arbitrary n, bias and permitted original endpoints. Exponent four is optimal within this class by Section 2.

First take interior u. Put Z=sum_i b_iX_i, alpha=1-m^2, j(t)=J(m,t), e(t)=t[V(m+t)-V(m-t)]/2. Symmetry of Z and the exact identity Nu=Z imply

    I(u)=E j(|Z|)=J, D(u)=E e(|Z|).

Apply the stipulated one-bit capacity at each realized magnitude, where |m|+|Z|<1 and j(|Z|)/alpha<L. Averaging, then quantitative Jensen, gives

    D>=alpha E F(j(|Z|)/alpha)
      >=alpha F(J/alpha)+(2/(3alpha))Var(j(|Z|)).

The perspective surplus contributes (2/3)m^2J^2/alpha. Also

    j''(t)=[psi''(m+t)+psi''(m-t)]/2>=1/alpha,
    d[j(sqrt(s))]/ds>=1/(2alpha).

The independent-copy formula for variance therefore yields Var(j(|Z|))>=Var(Z^2)/(4alpha^2). Hence

    D-F(J)>=(2m^2/(3alpha))J^2+Var(Z^2)/(6alpha^3)
            >=(2/3)m^2J^2+Var(Z^2)/6.                  (A313a)

For q=sum_i b_i^2, b=max_i |b_i|, eta^2=q-b^2,

    Var(Z^2)=2(q^2-sum_i b_i^4)>=2q eta^2.              (A313b)

This is a new, explicitly justified averaging deduction at the affine scope, not N131 applied unchanged in dimension n. A general kernel lacks both its generator identity and its symmetric centered law.

B313 gives d_a<=D0(m^2+eta^2). If |m|<=1/2, Bregman comparison at m gives psi(a)<=U_(1/2)q and q>=a^2/[2U_(1/2)]. At time s, q_s=exp(-2s)q, eta_s^2=exp(-2s)eta^2; every nonconstant original affine kernel is interior at positive time.

If Delta<w(t)/2, then y(s)>=r0^2a^2/4, and A313a,b give

    R(s)>=r0^4a^4m^2/24+r0^4a^2eta^2/[6U_(1/2)]
         >=r0^4a^4 min{1/24,1/[6U_(1/2)]}(m^2+eta^2).

If |m|>1/2, use d_a<=4<=16m^2 and the bias term alone to obtain R(s)>=r0^4a^4 d_a/384. Set tmin=-log r1>0 and

    c_aff=min{r0^2/16,
       tmin exp(-Ktmax)r0^4
       min{min{1/24,1/[6U_(1/2)]}/D0,1/384}}>0.

The weight in (1) is >=exp(-Ktmax), proving Delta>=c_aff a^4d_a in the small-deficit branch. Otherwise Delta>=r0^2a^2/4 and d_a<=4 give the first term in c_aff. Thus C_aff=1/c_aff is an explicit dimension-independent upper constant expressed in finite scalar suprema. It does not depend on bias, endpoint margin, number of affine coefficients, support or complexity. No expansion or information approximation is used in this upper bound.

## 6. L313: a shrinking local neighborhood for arbitrary kernels

The I128 Hessian has nonconstant minimum

    qH=k/(1-a^2)-r^2/(1-r^2a^2), k=rV(ra)/V(a),

and constant coefficient a^2qH. Independent scalar expansion gives qH=(2/3)r^2(1-r^2)a^2+O(a^4), uniformly on the fixed r interval. Its strict positivity for a>0 and continuous positive extension of qH/a^2 at zero imply qH>=c_Ha^2 for all 0<a<=a1. Also k is uniformly bounded below. Thus Q(h)>=c_Ha^4||h||_2^2.

Track the actual spike-tolerant L131 proof. Put

    qout=min{3,1+r1^(-2)}>2,
    theta=1/(1+r1^2)-1/2>0,
    Mloc=max{4+1/theta,4/(qout-2)}.

Choose its input truncation tolerance eta_tr=c a^4 using the fixed interior cubic bound. Its bad-support Young cost is <=C p^(2theta)/(c_Ha^4), so p_*=c a^(2/theta) suffices. The condition p<=epsilon^2/eta_tr^2 is paid by epsilon<=c a^(4+1/theta). Its output hypercontractive remainder C epsilon^qout is <=c a^4epsilon^2 when epsilon<=c a^(4/(qout-2)). Constants here depend only on a1,r0,r1. Consequently there are c_rad,c_loc>0 with

    I(u)=psi(a), ||u-s aX_i||_2<=c_rad a^Mloc
       ==> Delta_r(u)>=c_loc a^4||u-s aX_i||_2^2.        (L313)

Spikes, original endpoints and arbitrary dimension are allowed. The truncation is internal to the Bregman estimate and never changes u or its information. Every error is absorbed relative to a^4||h||_2^2. This conservative radius is not claimed optimal; global entrance to it is unproved.

Choose c_rad<=1/4. Since Mloc>1 and a<1, the neighborhood radius is <=a/4. Distinct signed soft coordinates are at least sqrt(2)a apart (opposite signs on one coordinate are 2a apart), so the coordinate in this neighborhood is the unique nearest one. Thus ||h||_2^2=d_a(u) here, and the error payment is relative to the actual target a^4d_a(u).

## 7. Exactly normalized tests and failed shortcuts

### Fixed-amplitude rare spikes

Let E_k be the all-positive atom of k bits, p=2^(-k), fixed 0<t<=1, u_k=t1_(E_k). Define a_k=psi^(-1)(p psi(t)-psi(tp)). Input information is exact and a_k^2~2p psi(t). But

    E psi(u_k)-Eu_k^2/2=p[psi(t)-t^2/2]=Theta(a_k^2),

not O(a_k^4). The remainder after the fourth term is also Theta(a_k^2). Thus a uniform quartic expansion over bounded kernels is false. For this family, hypercontractivity does pay the spike:

    I(T_r u_k)<=L t^2p^(2/(1+r^2))=o(p),
    Delta~r^2p psi(t),
    d_(a_k)=pt^2+a_k^2-2a_k tp=Theta(p),
    a_k^4 d/Delta=O(p^2)->0.

It is not a counterexample to S313.

### Rare output with bias approaching an endpoint

Set u_k=1-2 1_(E_k), a_k=psi^(-1)(H_b(p)). Again information is exact. Here Var(u_k)/(1-(Eu_k)^2)=1 although I->0: small information does not imply small normalized relative fluctuation.

The rare posterior of Y has density L_E(y)=product_(i<=k)(1+r y_i) relative to uniform Y and KL divergence k psi(r). The common posterior has KL at most its chi-square divergence p^2[(1+r^2)^k-1]/(1-p)^2=o(p). Hence

    I(T_r u_k)=p k psi(r)+o(p),
    Delta~p k[r^2 log2-psi(r)]>0,
    d_(a_k)->1, a_k^4d/Delta=O(pk)->0.

The strict coefficient follows from psi(r)<r^2 log2 for 0<r<1. This exposes a real limitation of likelihood-ratio perturbation methods, but does not refute the endpoint.

### Higher Walsh mass alone cannot select a soft coordinate

Let u=b(a)(X_1+X_2), b(a)=psi^(-1)(2psi(a))/2, for small a. It is bounded and has exactly I(u)=psi(2b)/2=psi(a). Its higher Walsh mass H vanishes, yet d_a=(a-b)^2+b^2~(2-sqrt(2))a^2. Thus a soft FKN estimate based only on H is false. A313 pays the missing singleton pair product.

The independent-selector hierarchy in I131 has exactly I=psi(a) and Delta>=r^2(1-r^2)d_a/4, so it already satisfies S313. This does not cover selector/payload reuse or arbitrary variable amplitudes.

## 8. Precise gap and contribution boundary

The remaining estimate, equivalent up to B313's proved constant to the full target, is

    Delta_r(u)>=c a^4[m^2+q-max_i uhat(i)^2+H].         (Missing E313)

It is proved here when H=0 and in L313's neighborhood, not for unrestricted kernels. Q313 reduces the work to increasing kernels without losing powers of a, but these can retain nonlinear terms and rare events.

For general g=m+ell+h, with ell its first level and h its higher levels, the identity

    D(g)=E[V(g)(g-m)]+E[V(g)(N-1)h]

is exact. The centered law need not be symmetric, and no certificate here pays the second term at the required order. Replacing g by its affine projection can violate [-1,1] and changes exact information; clipping changes both budgets. A sufficient affine-reduction theorem would produce bounded affine v with I(v)=psi(a), Delta(v)<=KDelta(u), and d_a(u)<=K[d_a(v)+a^(-4)Delta(u)]. That operation is not constructed.

The alternative joining route retains a nonnegative sum of losses, but the common-corner margin is multiplied by squared face separation and reserve pooling can be flat. No operation here removes those factors or synchronizes unequal-mean faces at order a^4B. Capacity is used only where independently justified in Sections 2 and 5.

I301/I304's compact Gaussian gap gives no small-a rate. Its fixed-degree invariance, clipping modulus and entropy transfer errors are absolute. Endpoint use must pay the Gaussian reserve, both entropy budgets, clipping and information renormalization on the scale a^4B, which can be arbitrarily smaller than a^4 near a coordinate. An unspecified absolute o(1) is insufficient. L313 requires entrance to c_rad a^Mloc; qualitative marked compactness and a backward square-root bridge supply no such rate.

Even a hypothetical all-kernel production bound R(g)>=c I(g)^2 d_(psi^-1(I(g)))(g) needs a paid link to the original distance along the flow: noise suppresses higher modes, and qualitative entrance is not a linear endpoint transfer. The affine proof supplies its link through coefficient identities; the general case remains unpaid.

The parent extraction, B313, Q313, affine capacity averaging/Jensen and local constant tracking are technical analytic partials. They go beyond suggestions, but do not certify a substantial result for unresolved S313. A new relative-error nonlinear reduction or joining coercivity mechanism could be substantial; neither is proved here. S302's SUBSTANTIAL verdict belongs to its new Gaussian mechanism and is not inherited. No worldwide priority, full endpoint PASS, acceptance or count change is asserted.
