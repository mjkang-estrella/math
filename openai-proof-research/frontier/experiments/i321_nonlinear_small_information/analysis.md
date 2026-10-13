# I321 — nonlinear small-information endpoint analysis

2026-10-13. **Full S313 remains UNRESOLVED.** No exactly normalized counterexample is obtained. The new proved partial is a weighted, spike-tolerant conditional-coordinate tube theorem T321. It includes fixed interior bias and a larger radius than L313. The I320 finite-cube normal form passes an independent coefficient and attainability audit. Neither assertion changes acceptance, contribution status, or the count of fourteen toward twenty.

## 1. Full target and dependency boundary

Let X be uniform on {-1,1}^n, n>=1, and T_r be product noise. All logarithms are natural. Set

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    I(u)=E psi(u)-psi(Eu)=psi(a),
    Delta_r(u)=psi(ra)-I(T_r u),
    d_a(u)=min_(i,s=±1) E|u-s aX_i|².

For every 0<a1<1 and 0<r0<=r1<1, the unrestricted question asks for C=C(a1,r0,r1) such that d_a(u)<=C a^(-4)Delta_r(u) for every finite n, every 0<a<=a1, every r in [r0,r1], and every u in [-1,1]. Bias approaching either endpoint, original endpoint values, rare events and arbitrary complexity are retained. No restricted theorem below is substituted for this question.

The stipulated source is OpenAI/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual primary statements read in this round are `main:soft`, `upgrade:production`, `scalar:profile-convexity`, `capacity:onebit`/`capacity:refined`, and the flow argument. Four local source files match fresh pinned raw retrievals in memory. No new external body is retained. The exact reading ranges and hashes are in input-authentication.json.

I313's complete finalized report, analysis, failure log, authentication and literature note were read. Its B313, affine theorem and local theorem are internal deductions, not additional source stipulations. B313 and the needed one-bit and semigroup operations are rederived below. I304's full finalized review and analysis were read, including its real hypercontractivity proof and its absolute-error Gaussian transfer. Its compact-rectangle theorem supplies no rate as a tends to zero. No live I316/I317/I319 body was read. N131 is not used as a general nonlinear theorem.

## 2. Independent I320 audit

Fix a finite cube, |m|<1, h=1-m², and f=sum_i c_i X_i with Ef²=h. Let g be orthogonal to levels zero and one. Suppose, in the supremum norm of this fixed finite cube,

    u_a=m+a f+a²g+a³j+O(a^4), Eu_a=m, I(u_a)=psi(a).

The fixed-mean identity implies Ej=0. The derivatives of psi at m are 1/h, 2m/h² and 2(1+3m²)/h³ at orders two, three and four. Since Efg=Ef³=0,

    I(u_a)=a²/2+a^4[(||g||²+2Efj)/(2h)
                +m E(f²g)/h²+(1+3m²)Ef^4/(12h³)]+O(a^5).

There is no unaccounted fourth-order linear term: the linear entropy term of the complete perturbation has expectation zero exactly. The O(a^4) perturbation first contributes to quadratic entropy at order a^5. Exact normalization sets the displayed bracket to 1/12.

Write g=sum_(k>=2)g_k and V=Var(f²)=2(h²-sum_i c_i^4). The polynomial f²-h is entirely second level. Noise sends f to rf and g_k to r^k g_k, while E[(rf)T_rj]=r²Efj and E[(rf)²T_rg]=r^4E(f²g_2). Eliminating Efj with the exact input equation gives

    lim Delta_r(u_a)/a^4
      =sum_(k>=2)(r²-r^(2k))||g_k||²/(2h)
       +r²(1-r²)[m E(f²g_2)/h²
                 +(1+3m²)Ef^4/(12h³)-1/12].

Completing the level-two square gives precisely

    r²(1-r²)[m²/(3h)+(1-3m²)V/(12h³)
             +||g_2+(m/h)(f²-h)||²/(2h)]
      +sum_(k>=3)(r²-r^(2k))||g_k||²/(2h).          (2.1)

The unique minimizing correction is g_opt=-(m/h)(f²-h). With kappa=sum_i c_i^4/h² the constant in (2.1) is

    r²(1-r²)[kappa*m²/(3h)+(1-kappa)/6].           (2.2)

The bracket is at least m²/6 and at least (1-kappa)/6, hence at least (m²+1-kappa)/12. This proves positivity of the optimized constant, including when the unsimplified V coefficient is negative. The square and the k>=3 terms are nonnegative.

Attainment is exact, not merely formal. The function

    [I(m+a alpha f+a²g_opt)-psi(a)]/a²

extends analytically to a=0 with value (alpha²-1)/2 and alpha derivative one at alpha=1. The analytic implicit-function theorem gives alpha(a). Third-order cancellation gives alpha'(0)=0. Global sign reversal makes the equation even in a, so uniqueness makes alpha even. Thus alpha=1+O(a²). Fixed finite dimension and a fixed interior mean ensure admissibility for small a. This checks all operations used in I320.

The correction is not affine when m!=0 and f has two active coordinates. At m²>1/3, spreading the leading direction decreases the optimized quartic coefficient relative to a biased coordinate. A transverse local-maximizer claim for every biased coordinate is therefore false. This fact does not cancel (2.2). The audit supplies no uniform jet representation, remainder, or entrance theorem as m approaches an endpoint, n increases, or the fields depend irregularly on a. I313's rare-spike obstruction to uniform quartic expansion still applies.

## 3. T321: weighted nonlinear conditional-coordinate tube

Define, using the fixed correlation rectangle,

    qout=min{3,1+r1^(-2)}>2,
    theta=1/(1+r1²)-1/2 in (0,1/2),
    Mtube=max{2+1/(2theta), 2/(qout-2)}.             (3.1)

For every fixed 0<=m0<1 there are positive a_*, epsilon_*, c_* depending only on m0,a1,r0,r1, with a_*<=a1, such that the following assertion holds for all finite cubes and 0<a<=a_*.

Choose a coordinate, orient it, and let

    m=Eu, b=E[uX_1]>=0,
    v=E[u|X_1]=m+bX_1, w=u-v, delta=||w||_2.

If |m|<=m0, u in [-1,1], I(u)=psi(a), and delta<=epsilon_* a^Mtube, then

    Delta_r(u)>=c_*[a^4 m²+a² L(w)+H(w)],          (T321)
    L(w)=sum_(i!=1) what(i)²,
    H(w)=sum_(|S|>=2) what(S)²,

uniformly for r in [r0,r1]. In particular d_a(u)<=C_* a^(-4)Delta_r(u).

The residual condition concerns the original kernel and its genuine conditional expectation; no clipping or replacement kernel is performed. Original u may take ±1 and w may have fixed-height rare spikes. The mean is in a fixed interior interval and need not tend to zero. The exponent in (3.1) is exactly half of L313's conservative exponent. This is a proved partial with additional hypotheses, not unrestricted S313.

### 3.1 Exact information split and scalar slope

For |x|<1 and |y|<=1 write Bpsi(y,x)=psi(y)-psi(x)-atanh(x)(y-x). For each gamma<1,

    U_gamma=sup_(|x|<=gamma,|y|<=1) Bpsi(y,x)/(y-x)²<infinity,

using psi''(x)/2 on the diagonal. Interior Taylor bounds control the diagonal; continuity controls the remaining compact set, including y=±1. Strong convexity gives Bpsi(y,x)>=(y-x)²/2 globally.

Conditional Jensen gives I(u)>=J(m,b)=I(v). Also J(m,b)>=psi(b): J is even and convex in m, because psi'' is convex and

    J_mm=[psi''(m+b)+psi''(m-b)]/2-psi''(m)>=0.

Endpoint parameters use continuity. Therefore b<=a. With a small enough a_* and |m|<=m0, both v and T_rv lie in a fixed interior interval [-gamma,gamma], gamma<1, independently of n.

Let J=I(v), beta=psi^(-1)(J), and put

    A=E Bpsi(v+w,v), O=E Bpsi(T_rv+T_rw,T_rv).

Since E[w|X_1]=0 and this property is preserved by product noise, both linear Bregman terms have expectation zero. Consequently

    I(u)=J+A=psi(a), I(T_ru)=I(T_rv)+O,             (3.2)
    delta²/2<=A<=U_gamma delta².

For f_r(J)=psi(r psi^(-1)(J)), its derivative at psi(t) is

    k(r,t)=r atanh(rt)/atanh(t), k(r,0)=r².

This decreases with t. Indeed tV'(t)/V(t)=sinh(2V(t))/(2V(t)) increases strictly, and differentiating log k with respect to log t compares this expression at rt and t. Thus f_r is concave, including its smooth extension at zero. Its secant in (3.2) is at least k=k(r,a). It follows exactly that

    Delta_r(u)>=Delta_r(v;beta)+kA-O,              (3.3)
    Delta_r(v;beta)=psi(r beta)-I(T_rv).

At A=0 the same identity has no secant division. Notice that beta, rather than a, is the exact information amplitude of v. This distinction pays the information correction.

If delta<=a², uniform Taylor expansion of the actual one-bit J and (3.2) give, with h=1-m²,

    J=b²/(2h)+O(b^4),
    b²=h a²+O(a^4+delta²)=h a²+O(a^4),             (3.4)
    b=sqrt(h)a+O(a³).

These expansions are uniform on the fixed m/r rectangle; they concern only v, not arbitrary u. Since Mtube>3, the theorem's residual condition implies delta<=a² after reducing epsilon_*,a_*.

### 3.2 The weighted Hessian and its Schur complement

Let Pi z=E[z|X_1]. For arbitrary z define

    Q(z)=k E[z²/(1-v²)]-E[(T_rz)²/(1-(T_rv)²)],
    W(z)=a² sum_(i!=1) zhat(i)²+sum_(|S|>=2) zhat(S)².

We prove, uniformly under (3.4),

    Pi z=0 ==> Q(z)>=cQ W(z),                     (3.5)
    Q(z)>=cQ W(z)-CQ||Pi z||² for arbitrary z.     (3.6)

Expand z on the coordinates other than 1 in blocks

    (alpha_S+X_1 eta_S) chi_S, d=|S|.

For S!=empty write the input multiplier 1/(1-(m+bX_1)²)=A0+A1X_1, and the output multiplier 1/(1-(m+rbX_1)²)=B0+B1X_1. The exact quadratic block has entries

    q11=k A0-r^(2d) B0,
    q22=k A0-r^(2d+2) B0,
    q12=k A1-r^(2d+1) B1.                         (3.7)

All constants and remainders below are uniform for |m|<=m0 and r in the rectangle. For d=1, (3.4) and analytic scalar expansion give

    A0=1/h+(1+3m²)b²/h³+O(b^4),
    A1=2mb/h²+O(b³),
    B0=1/h+(1+3m²)r²b²/h³+O(b^4),
    B1=2mrb/h²+O(b³),
    k=r²-r²(1-r²)a²/3+O(a^4).

Therefore

    q11=r²(1-r²)(2+10m²)a²/(3h²)+O(a^4),
    q22=r²(1-r²)/h+O(a²),
    q12=2mb r²(1-r²)/h²+O(a³).

The dangerous cross term is paid by the exact Schur complement:

    q11-q12²/q22=2r²(1-r²)a²/(3h)+O(a^4).         (3.8)

In particular it stays uniformly positive. Completing the block square yields a lower bound c(a² alpha_S²+eta_S²). To see that both original variables are paid, use q12/q22=O(a) and

    eta_S²<=2(eta_S+(q12/q22)alpha_S)²+C a²alpha_S².

This is the local linearization of I320's level-two quadratic correction; it is not legitimate to drop that correction or to charge both variables at the a^4 scale.

For d>=2, the matrix at a=b=0 is diagonal with entries (r²-r^(2d))/h and (r²-r^(2d+2))/h. Their uniform lower bound is positive because r0>0 and r1<1. The perturbation in (3.7) is O(a) in operator norm uniformly over all d, since all r powers are at most one. Reducing a_* gives c(alpha_S²+eta_S²) for every such block. Orthogonal summation proves (3.5).

The S=empty block has bounded operator norm, and all different S blocks are orthogonal for Q. Removing this one block proves (3.6); W ignores precisely the constant and X_1 terms in Pi z. No dimension-dependent matrix estimate is involved.

The apparent contrast with I320's negative transverse variation at m²>1/3 has no contradiction. Here (3.3) compares to a one-bit v with its *smaller actual information* beta, whose own deficit changes under spreading. T321 does not assert maximality of a fixed biased normalized channel.

### 3.3 Spike-tolerant remainder estimate

We now prove

    kA-O>=cR W(w)                                 (3.9)

under (3.1)'s residual radius. No input Taylor expansion is made on the bad set.

Choose eta=c_eta a², with c_eta positive and small, and split the original residual on disjoint supports:

    g=w 1_(|w|<=eta), z=w 1_(|w|>eta), p=Pr(|w|>eta).

Then p<=delta²/eta². A uniform interior third-derivative bound gives

    kA>= (k/2)E[g²/(1-v²)]-C eta||g||²
                  +(kmin/2)||z||²,                (3.10)

where kmin>0 uniformly. The last term is global strong convexity, valid when u is an endpoint. Since Pi w=0, Pi g=-Pi z. Conditional Cauchy–Schwarz on the two fibers gives

    ||Pi g||²<=2p||z||²,
    ||g||²<=a^(-2)W(g)+2p||z||².                  (3.11)

Real-function hypercontractivity gives

    ||T_rz||_2<=p^theta||z||_2,
    ||T_rw||_(qout)<=||w||_2=delta.                (3.12)

The first estimate is the L_(1+r²)-to-L2 bound followed by the support bound; theta is the minimum support exponent on the rectangle. The second follows from 1+(qout-1)r²<=2. The two-point proof read in I304 is applicable to real functions: for 1<p0<=2, differentiating ||A+tBX||_(p0)² gives a nonnegative square and a term at least 2(p0-1)B² by Jensen for the negative power. Integration across the locally integrable zeros gives ||A+BX||_(p0)²>=A²+(p0-1)B². Minkowski tensorization and duality give (3.12), with constants one. No Boolean-value premise is used.

The output base T_rv stays in a fixed interior interval. For qout<=3 its scalar Bregman expansion has a global remainder bounded by C|y|^qout, including perturbed endpoints: near y=0 use the interior cubic bound; away from zero use continuity on the bounded physical domain. Thus

    O<=(1/2)E[(T_rw)²/(1-(T_rv)²)]+C delta^qout.  (3.13)

Combining (3.10)–(3.13), using (3.6), and expanding the output square gives

    kA-O >= (cQ/2)W(g)-C p||z||²-C eta||g||²
       +(kmin/2)||z||²-C p^(2theta)||z||²
       -C p^theta||g|| ||z||-C delta^qout.

Choose c_eta so that (3.11)'s good-set Taylor cost spends at most cQ W(g)/8. For the cross term, (3.11) and Young's inequality give a cost at most

    (cQ/8)W(g)+C[a^(-2)p^(2theta)+p^(theta+1/2)]||z||².

The remaining bad costs are bounded by

    C[p+p^(2theta)+p^(theta+1/2)+a^(-2)p^(2theta)]||z||².

It suffices to have p<=c_p a^(1/theta), with c_p small. Indeed p^(2theta)<=c_p^(2theta)a², and all other powers above are no larger than p^(2theta) when 0<=p<=1. From eta=c_eta a² and p<=delta²/eta², this is guaranteed by

    delta<=c a^(2+1/(2theta)).                    (3.14)

After these choices we have a fixed positive multiple of W(g)+||z||², except for the output remainder. By disjoint support and (3.11),

    a²delta²<=W(g)+3||z||².

Consequently C delta^qout is absorbed by a further fixed fraction of that positive quantity when

    delta<=c a^(2/(qout-2)).                      (3.15)

Choose epsilon_* to meet both (3.14) and (3.15). Finally

    W(w)<=2W(g)+2W(z)<=2W(g)+2||z||².

This proves (3.9). The proof pays every remainder at its actual weighted scale. At delta=0 it is immediate; no division by delta or p occurs. The split leaves u and I(u) unchanged.

### 3.4 Paying the one-bit bias and original distance

For completeness the inherited one-bit estimate used here is rederived, with its actual scope. At a genuine one-bit field m+tX, let J_t be its information, h=1-m², and D its production. The stipulated capacity gives D>=hF(J_t/h). Since F''>=4/3, subtracting (2/3)J² makes a convex function vanishing at zero, and perspective comparison gives

    D-F(J_t)>=(2/3)(1/h-1)J_t²>=(2/3)m²J_t².      (3.16)

Only genuine one-bit channels are involved. Along the one-bit flow define y(s)=I(T_(exp(-s))v), w0(s)=psi(beta exp(-s)), R=D-F(y), and z0=w0-y. Exact differentiation gives z0'=R-Asec z0, with 2<=Asec<=K=max_[0,psi(a1)]F'. For t=-log r,

    Delta_r(v;beta)=integral_0^t exp(-integral_s^t Asec)R(s)ds.

If Delta_r(v;beta)>=psi(r beta)/2, it is at least r0² beta²/4 and hence at least (r0²/4)m²beta^4. Otherwise y(s)>=y(t)>=r0²beta²/4 for all s<=t. Inserting (3.16), with tmin=-log r1 and tmax=-log r0, proves

    Delta_r(v;beta)>=cB m²beta^4,
    cB=min{r0²/4, tmin exp(-K tmax)r0^4/24}>0.      (3.17)

All fields v used here are interior. More generally the positive-time source flow pays original one-bit endpoints without finite initial production; this is not needed to impose an interior restriction on u.

Equation (3.2) and A<=U_gamma delta² give J>=a²/4 after reducing the constants. Since psi(beta)<=L beta², beta²>=a²/(4L). Equations (3.3), (3.9), and (3.17) therefore prove T321.

To transfer to original distance, the B313 bridge can be checked without any affine substitution. The cancellation E[X_1(u-bX_1)]=0 implies

    psi(a)-psi(b)<=E Bpsi(u,bX_1)
                      <=U_a1 E(u-bX_1)²
                      =U_a1(m²+delta²).

Because b<=a, strong convexity and psi'(b)>=0 give (a-b)²<=2[psi(a)-psi(b)]. Hence the distance to this signed coordinate satisfies

    d_a(u)<=E(u-aX_1)²=m²+delta²+(a-b)²
                  <=(1+2U_a1)(m²+delta²).

Since W(w)>=a²delta²>=a^4delta² for a<=1, T321 yields the advertised endpoint inequality in its tube. The proof does not need to assume that coordinate 1 is already the closest one.

For n=1, w=0 and the result is the one-bit theorem. Zero residual, m=0, closed r endpoints, changing dimension, original u endpoints and rare spikes all satisfy the stated proof. Constants may deteriorate as m0 tends to one, and no uniformity in that limit is claimed.

## 4. An exactly normalized nonlinear endpoint-spike family in the new scope

T321 includes more than a renaming of L313's balanced-coordinate ball. Fix 0<m<m0<1. Let E_k be an atom on k coordinates different from 1 and 2, p=2^(-k), and take

    v=m+bX_1,
    u=v+(1-v)X_2 1_(E_k),                         (4.1)

with b small enough that 0<v<1. On E_k the values of u are 1 and 2v-1; outside it u=v. Thus u is bounded, it takes the exact endpoint +1, Eu=m, and E[u|X_1]=v. The residual has

    delta²=p E(1-v)²<=p.

Its exact information is

    E[(1-p)psi(v)+(p/2){psi(1)+psi(2v-1)}]-psi(m).  (4.2)

For fixed m this is even and strictly increasing in small positive b, and its derivative with respect to b² at p=b=0 is 1/(2(1-m²))>0. At b=0 it is p times a fixed positive scalar. For every small a and dyadic p<=c a^(2Mtube), that value is below psi(a). The analytic inverse in b² (or monotonicity plus the intermediate value theorem) gives a positive b with (4.2)=psi(a) exactly. The expansion is b²=(1-m²)a²+O(a^4+p), so 0<v<1 and delta<=epsilon_* a^Mtube if c is small. The input family is not clipped and its normalization is not approximate.

Here d_a(u)>=m² stays away from zero, while the kernel is nonlinear and may have unbounded dimension. It is outside every L313 balanced-coordinate ball whose radius tends to zero, but is covered by T321. This is a covered family, not a counterexample attempt certified against the full target. No numerical parameters were scanned.

## 5. What remains unpaid

For arbitrary u, define m=Eu, q=sum_i uhat(i)², bmax=max_i|uhat(i)| and H=sum_(|S|>=2)uhat(S)². The same Bregman argument gives B<=d_a<=D0B, where

    B=m²+q-bmax²+H, D0=1+2U_a1.

The lower bound is Parseval and bmax<=a. Thus the original full question is still equivalent, up to D0, to

    Delta_r(u)>=c a^4 B                            (Missing E321)

without added assumptions. T321 proves this only when some coordinate has an original residual delta<=epsilon_* a^Mtube and the mean lies in a fixed interior interval, for small a. The compact-rectangle theorem handles a bounded away from zero but supplies neither of the missing endpoint operations:

1. A quantitative global alternative at vanishing a that either pays a^4B outright or places the original kernel in a conditional tube at the scale in (3.1). No such alternative is proved. A selected coordinate with a qualitative singleton bound is insufficient. Noise at positive time may suppress the original residual, so a smoothed-tube conclusion alone does not pay original higher modes.
2. A uniform replacement for the interior-mean constants as |m| tends to one, or a separate global endpoint-mean argument. Small information does not make relative fluctuations small: I313's exactly normalized rare Boolean outputs rule out that shortcut.

The residual upper bound A<=U_gamma delta², the uniform scalar expansions in (3.4), and the bounded multipliers in (3.7) explicitly use m0<1. They cannot be applied with m0 depending on u and then called uniform. Even inside a fixed mean interval, arbitrary low-information kernels have delta of order a, rather than a^Mtube, and T321 provides no global entrance. A uniform expansion of arbitrary u is false, as the retained I313 rare spikes show.

The I320 normal form has not supplied a representation theorem for all nearly extremal fields. An absolute O(a^5), unspecified Gaussian o(1), or fixed-degree invariance error can greatly exceed a^4B. No clipping/affine-projection correction or backward noise inversion has been paid here. The affine proof is inherited and not counted as new. The unrestricted endpoint is neither proved nor refuted in this record.

## 6. Correctness, contribution and priority

**Correctness scope:** I320's finite-cube, fixed-interior-mean calculation and exact attainability pass this independent audit. T321, including its Schur complement, nonlinear spike payment, exact information split and original-distance transfer, is proved under its explicit conditional-tube and interior-mean hypotheses. The full S313 verdict is UNRESOLVED.

**Contribution scope:** The new operation is conditioning to an actual bounded one-bit channel and comparing the remaining entropy at an exact concave secant, followed by weighted residual coercivity. It pays mean, other singleton and higher modes at different scales and enlarges the earlier conservative local scope. This is a technical partial toward the target; no substantial full-endpoint finding is nominated or inherited from I304/R020.

**World priority:** No worldwide-priority claim is made. Primary comparison in this round covers Yu v5's balanced Boolean local theorems and FKN v1's Boolean first-level theorem. Their actual hypotheses do not supply Missing E321. The literature review is not exhaustive and does not establish novelty in the world literature. Fourteen accepted findings remain unchanged toward twenty.
