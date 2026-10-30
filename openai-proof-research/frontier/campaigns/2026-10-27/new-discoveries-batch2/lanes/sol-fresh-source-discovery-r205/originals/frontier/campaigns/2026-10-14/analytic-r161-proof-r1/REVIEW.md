# Independent correctness review: Analytic161 / T337A161, round 1

**Full-scope verdict: PASS.** Relative to the stipulated pinned source and its operative proofs, the unchanged AUTHOR-PROOF.md establishes the entire unchanged FROZEN-STATEMENT.md. No mathematical repair, changed constant, added hypothesis, restricted multiplicity, or reduced quantifier is needed. This verdict concerns correctness only. It assigns no contribution, acceptance, priority, or campaign count.

Target statement SHA256: `53f35f024803059dd77264ffc0f00d0c20209a3768e61551e8285eccaf7d5b38`.

Target proof SHA256: `22d6114f858c90872c502560f6b814766aab096f65cc16b081ee01d107577e2f`.

All assertions below concern the full scope: every integer n>=3; every proper CAT(0) X without an ambient dimension bound; every nonzero compact integral n-cycle T, with arbitrary signed integer chart multiplicities; every allowed delta, including zero. The existence, boundary, compact support, filling cost, two-sided mass ratio, connectedness, diameter, unique barycenter, mean-square and every-point shell bounds, radius interval, and limiting modulus have all been checked. The derivative notation is the source's chart calculus, not a smooth-support assumption.

## 1. Stipulated input and what is independently checked

Let S be *Sharp integral fillings in CAT(0) spaces* at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The sharp theorem in cycle dimensions n and n-1, the current foundations, Euclidean chart mass and tangent differentiation, and the actual operative proofs in S are stipulated true. Their truth is not being audited. I read the full actual TeX of S Sections 02 through 07, plus its main file, macros and introduction. I checked the hypotheses and internal uses of those proofs when transplanted to the author's new comparison inequality. This applicability check, and every new deduction and constant below, are independent review work.

In particular, filling-volume continuity is an explicit input of S Section 02, `thm:current-background`, lines 151-157 and 217-227. It is not derived from weak lower semicontinuity. The independently read Wenger primary Theorem 1.4 and its proof agree with the source's cycle-continuity interface: completeness, quasiconvexity, local cone inequalities in dimensions 1 through n, and bounded normal masses. Compact CAT(0) Y has these properties. The elementary cone construction in S02 lines 178-205 supplies them without a finite ambient dimension.

BDF2015 is a methodological comparator, not a premise of the author's proof. Its original penalty and comparison proofs were read, along with Theorem 6.2's Euclidean graphical-regularity proof. The latter depends on Euclidean normal coordinates, elliptic integrands and epsilon regularity; none is transplanted here. The smooth companion's introduction was checked to distinguish its finite-perimeter and bounded equality statements. No operative smooth theorem is needed for this shell proof.

## 2. Selection, attainment, nonvanishing, and exact mass estimates

A closed ball Y containing support T is compact and convex. Projection onto Y is 1-Lipschitz and fixes cycles supported there. Thus the compact-filling infimum in X equals the filling infimum in Y. Current compactness in Y and lower semicontinuity attain the latter; inclusion gives a compact filling in X. Symmetry and subadditivity yield |V(B)-V(C)|<=V(B-C), and the cone gives V(B)<=L_Y M(B).

For lambda>0, the two summands of

    Phi(B)=[c M(B)^q-V(B)]+lambda V(B-T)

are nonnegative by the stipulated sharp bound. The lower bound Phi(B)>=c M(B)^q-L_Y M(B) is coercive because q>1. A minimizing sequence with bounded objective therefore has bounded mass and zero boundary. Its weak integral limit is a cycle. Both sequences B_j and B_j-T have bounded mass and zero boundary, so source filling continuity makes both filling terms continuous. Mass lower semicontinuity then attains Phi. There is no semicontinuity sign error in the negative term -V.

Comparison with T gives Phi(A)<=delta L_T. Since delta=lambda^2,

    V(A-T)<=lambda L_T,
    0<=c M(A)^q-V(A)<=lambda^2 L_T.

Consequently

    V(A)>=(1-lambda-lambda^2)L_T,
    c M(A)^q<=V(A)+lambda^2 L_T
              <=V(T)+V(A-T)+lambda^2 L_T
              <=(1+lambda)L_T.

The first lower bound is strictly positive: lambda<=1/4 gives 1-lambda-lambda^2>=11/16. Thus A is nonzero, and the sharp bound gives the other side of the required mass ratio. A minimizing filling of A-T supplies Q, with exactly boundary Q=A-T and M(Q)<=lambda L_T. Every current involved is integral and compactly supported in Y.

Minimality at an arbitrary integral cycle B gives

    c[M(A)^q-M(B)^q]
      <=V(A)-V(B)+lambda[V(B-T)-V(A-T)]
      <=(1+lambda)V(A-B).

For delta=0, A=T and Q=0 work directly. The sharp deficit is nonnegative for every competitor and zero at T, so its global minimality gives the same comparison with lambda=0. No limiting selection or nonzero-limit argument is required.

## 3. Scaling and the comparison-to-Sobolev interface

Under d'=d/rho, j-mass scales exactly by rho^(-j), by the Lipschitz bound for the identity and its inverse. Integral chain groups and boundaries are preserved; filling mass has degree n+1. Since nq=n+1, both terms of the mass-power comparison have this same degree. Dividing its coefficient by H gives

    c_eff=c/H,
    c_eff[m^q-M(B)^q]<=V(A-B),
    m=M_d'(A)=s H^n,
    c_eff q m^(1/n)=1/n.

The chosen rho=R_A/H is positive. No homothety of X is presumed. Rescaled Y stays compact and CAT(0). For H>1, c_eff<c and m>s; those inequalities do not satisfy the source's original positive-extremizer construction. The author correctly replaces that construction with the new comparison and checks the operative proofs.

The full source proof check is as follows.

* S03 `prop:radial`, lines 26-262, constructs a Lipschitz whole-current homotopy and computes spatial and swept comparison determinants. It needs compact Y, a nonzero cycle, its Euclidean metric differential and chart mass. Lines 272-285 use only the comparison inequality with a positive coefficient and the displayed normalization. There is no use of c_eff>c_n or m<s in this operation. Even if the first-order mass decrease has either sign, using the positive upper bound U_h=m-h I_g+O(h^2) before taking its power justifies the argument. This yields the author's (3.1) for each y in Y.
* S04 `prop:small-set`, lines 52-101, fills the boundary of a superlevel restriction, compares B=A-U+R, and uses a coarse n-filling estimate. If d<a<=m/2, the derivative bound is c_eff q(m/2)^(1/n)=2^(-1/n)/n. Therefore d>=a-C_0 a^(1+1/n), with C_0=n K_n 2^(1+2/n). If d>=a the same lower estimate is automatic. Combining with the sharp (n-1)-filling upper estimate supplies the same near-Euclidean perimeter coefficient for sufficiently small a. Only positive finite m and the normalized comparison are needed.
* S04's countable mass tests, intrinsic coarea, generalized-inverse rearrangement, radial Euclidean Sobolev calculation, and truncation all operate on that small-set inequality. The coarea derivatives are the absolutely continuous parts of the level-distribution measures. Atoms and singular continuous parts are explicitly allowed. The rearranged inverse is Lipschitz because its original distribution radius has a uniformly signed slope; its constant intervals carry zero energy. The globalization uses finite m, not m<s. Thus (3.2) follows for the author's current with the exact S_*=n s^(2/n).
* S05 `prop:sobolev-space`, lines 77-207, closes the gradient using A(b,u_j,pi)=-A(u_j,b,pi) on the whole cycle. It first obtains zero signed measures and then restricts them to charts, using extended inverse coordinates. It never integrates by parts on individual Borel chart restrictions. The argument needs nonzero signed integer multiplicities, not their boundedness. Closed-graph approximation supplies chain rules, zero derivative on each fixed level, positive-part continuity, and nonnegative Lipschitz approximation. The radial inequality extends to nonnegative H tests because r is bounded on Y.
* S05 `prop:compact-embedding`, lines 221-378, projects whole weighted currents, obtains a uniform translation estimate in total variation, and then isolates each chart using Lipschitz approximations to its indicator in L2(mu). The fixed chart multiplicity cancels in the comparison of total variation and chart L1. Finite mass controls discarded charts. The already established Lp bound and p>2 upgrade L1 compactness to L2. Neither an ambient dimension bound nor m<s enters.
* S05's operative strict original mass use is its constant-test inequality at lines 424-428, Lambda<=n m^(2/n)<S_*. The opening m<s premise and later narrative also state it, but the subsequent compactness/splitting proof needs Lambda<S_*, not m<s independently. The author assumes exactly Lambda<S_* for contradiction. The positive lower bound for Lambda comes from (3.2), and the critical splitting yields Lambda>=Lambda t^(2/p)+S_*(1-t)^(2/p). For t<1 this exceeds Lambda, so a minimizer exists with no lost critical mass.
* Normalizing that nonnegative minimizer yields v, Q(v)=nW and W=(Lambda/n)^(n/2)<s, with the source Euler equation. S05 `lem:powers` absorbs the Lp tail of v^(p-2), depending on its integrability rather than a global m<s bound. Iteration supplies all finite positive moments and all polynomially weighted energies. `lem:composites` then gives the needed two-variable chain rules by bounded truncations. S06 `lem:chord-tests` checks C1 extensions at v=0 even when beta<1; neither strict positivity nor essential boundedness is assumed.
* S06's weighted chord proof uses radial variation, the Euler equation, quotient minimality, and those tests. It yields J_y(a)<=(1+2aL_y)^(-n/2). Chart tangent density gives the coefficient s/(2^n W), hence L_y<=2(W/s)^(2/n)<2 almost everywhere. The only strict mass here is the newly obtained W<s. S07's opposite average uses the same v, its moments, and CAT(0) variance: radial Cauchy-Schwarz and the Euler test v^(1+2 beta) give W^2<=B_* I(y) for every center; variance at its barycenter gives the weighted average at least 2. This contradicts the strict upper bound.

Thus (3.3), Q(u)>=S_*||u||_p^2, is established for m=s H^n. The constant function need not minimize for H>1; the author does not use that false claim. This is the essential checked compatibility step. The only other strict m<s uses in the source are in constructing its hypothetical extremizer, its separate n=2 contradiction, and its final proof assembly; those operations are not invoked to construct the present selected current or the subthreshold minimizer.

## 4. Connectedness, deletion, density, and diameter

A disconnected compact support admits a disjoint nonempty compact partition with positive distance. A Lipschitz cutoff constant near the two parts has a gap of levels on which the current has no mass. Almost-everywhere slicing there produces integral cycles C,D, with A=C+D and additive masses. Each mass is positive by the definition of support. Set a=M(D)<=m/2. Comparison and the sharp n-filling theorem give

    m^q-(m-a)^q<=H a^q.

For z=m/a>=2, z^q-(z-1)^q is increasing, since q>1. It is at least 2^q-1. But lambda_n<= (2^q-2)/2<2^q-2, so H<2^q-1 throughout the closed allowed parameter interval. This proves connectedness, including lambda=0.

For x in support A set a(r)=mu(B(x,r)), with open balls. Apply intrinsic coarea to -d(x,.) to obtain integral restrictions and P(r)<=a'(r) almost everywhere. The prime denotes the density of the absolutely continuous part; no absolute continuity of a is imposed. Fill its boundary with mass d<=c_(n-1)P^(n/(n-1)). For a<=m/2 and d<=a/2, comparison with A-U+R gives

    [2^(-1/n)/(2n)] a <= c(a+d)^q <= c(3a/2)^q.

The rearranged lower threshold is exactly

    Acrit=[1/(n c 3^q)]^n
          =s(n+1)^n/(n^n 3^(n+1))=4a0.

Here c is the sharp n-filling constant, while the comparison lower bound uses c_eff. Confusing those two coefficients would change this calculation; the author's use is correct. Also

    a0/s=((n+1)/n)^n/(4*3^(n+1)) <1/(4*3^n)<1/2,

and m>=s. Hence whenever 0<a<=a0, a filling with d<=a/2 is impossible. Therefore

    a'(r)>=(a(r)/(2c_(n-1)))^((n-1)/n)

at almost every such radius. At support points a(r)>0 for every r>0. On positive-radius intervals where a<a0, monotonicity and the chain rule for the absolutely continuous derivative give

    (a^(1/n))'>=1/[n(2c_(n-1))^((n-1)/n)].

The singular derivative measure of the monotone composition is nonnegative. Integrating finite differences and then letting the starting radius go to zero yields a(r)>=b r^n until the threshold. The coefficient is exactly

    b=[n(2c_(n-1))^((n-1)/n)]^(-n)=omega_n/2^(n-1).

If an atom jumps across the threshold, monotonicity gives the subsequent a0 bound; at the crossing radius, limits from smaller radii handle the open-ball convention. In general B(x,r) is the increasing union of B(x,r_j), r_j upward to r, so the bound extends to every exceptional radius. Thus a(r)>=min(a0,b r^n) at every support point and every r>0. This also treats singular continuous radius distributions.

With r0=(a0/b)^(1/n), each open r0-ball about the support has mass at least a0. Connectedness makes the image of distance from a diameter endpoint the whole interval [0,d_K]. Points at distance levels 0,3r0,...,3Nr0 have disjoint open r0-balls, where N=floor(d_K/(3r0)). Hence (N+1)a0<=m<=mbar. The stated D=3r0(mbar/a0+1) is a valid, deliberately loose bound. All four constants a0,b,r0,D are positive and depend only on n; none depends on the original containing ball's diameter.

## 5. The new C>1 operation and all constants

The completed-square identity is

    1-r sqrt(1-|Dr|^2)-|Dr|^2+r^2/4
      =(sqrt(1-|Dr|^2)-r/2)^2.

Multiplying by ng>=0 and combining with (3.1) gives (5.1) with the stated inequality direction. For a fixed a>0 and k=(n-2)/2, w(t)=(1+a t^2)^(-k) and f(t)=integral_0^1 z^(n-1)w'(zt)^2 dz are smooth bounded profiles with bounded first derivatives. Their composition with distance is an admissible Lipschitz test on compact Y. Although the diameter D only bounds distances between support points, the profiles and tests are defined throughout Y; no center/test domain is lost.

Differentiating z^n w'(zt)^2 and integrating gives nf+tf'=w'^2. Thus

    Q(w(r))<=n integral [w(r)^2+beta r^2 f(r)]dmu.

For z=a r^2, substitution u=zeta^2 in f gives beta r^2 f=k z^2 integral_0^1 u^(n/2)(1+zu)^(-n)du. The derivative identity

    d/du [u^k/(1+zu)^(n-2)]
      =k u^(k-1)(1-z^2u^2)/(1+zu)^n

proves exactly the scalar identity in the author proof, including its boundary term at u=1. Integrability at zero follows from k>0, including n=3. Tonelli then identifies the right side as n m G(a).

Since ||w(r)||_p^2=(m J(a))^((n-2)/n), (3.3) gives

    (s/m)^(2/n)J(a)^((n-2)/n)=H^(-2)J(a)^((n-2)/n)<=G(a).

Raising to n/(n-2) supplies C=H^(2n/(n-2)). For h=G^(-1/k), the exact relations are

    a G'=k(J-G),
    a h'=h-J G^(-n/(n-2)) >= h-C,
    J<=C h^(-n/2).

In particular (h-C)/a is nondecreasing for a>0. Its initial limit is negative infinity if C>1, so it cannot be integrated from zero as though C=1. The author correctly avoids that step.

The third derivative of (1+t)^(-n) is negative for t>=0. Its quadratic Taylor upper bound, followed by the u integration, yields

    G(a)<=1-(n-2)L a+[n(n+1)k/(2(k+2))] a^2 integral r^4 dnu.

The tangent line to the convex function z^(-1/k) at 1 gives h>=1+(1-G)/k. Since integral r^4<=D^4, the resulting coefficient is

    n(n+1)/(2(k+2))=n(n+1)/(n+2)=gamma,

and h(a)>=1+2La-gamma D^4 a^2. Choosing the strictly positive

    a_*=sqrt((C-1)/gamma)/D^2

balances (C-1)/a_* and gamma D^4 a_*. Monotonicity from this point gives h(a)>=C+aK_* for a>=a_*, where K_*=2L-2D^2 sqrt(gamma(C-1)).

If K_*<=0, L<=D^2 sqrt(gamma(C-1)), which suffices. If K_*>0, the chord bound gives limsup a^(n/2)J(a)<=C K_*^(-n/2). At almost every center the source chart tangent calculation with v=1 gives

    liminf a^(n/2)J(a)>=|theta|/m integral_R^n(1+|z|^2)^(-n)dz
                      >=s/(2^n m).

This is a lower bound obtained by restricting to one chart and applying Fatou along a subsequence realizing the liminf. Unbounded multiplicity causes no uniform-integrability requirement; the nonzero integer value supplies |theta|>=1. The integral is s/2^n by stereographic Jacobian, not omega_n. The coefficient is therefore exactly the one the author uses.

Combining the two sides gives

    K_*<=(2^n C m/s)^(2/n)=4 C^(2/n)H^2=4C,

where C^(2/n)H^2=H^(4/(n-2)+2)=C. Thus L<=2C+D^2 sqrt(gamma(C-1)) in both signs of K_*.

At C=1 one starts at any a_*>0. The same Taylor lower bound gives (h(a_*)-1)/a_*>=2L-gamma D^4 a_*. Letting a_* decrease to zero for fixed a yields h(a)>=1+2La. If L>0, the tangent coefficient and J<=h^(-n/2), with m=s, imply L<=2. If L=0 it is already true. The zero-deficit endpoint is therefore proved without a discontinuity or division by C-1.

## 6. Barycenter, averaging, every-point upgrade, and restored scale

The squared-distance functional is continuous on compact Y and has a minimizer there. Projection onto Y shows this is also a global minimizer in X. CAT(0) strict convexity along the segment between distinct minimizers gives uniqueness. For its probability measure nu, the integrated CAT(0) inequality along o_t=[o,y]_t yields

    integral d(y,x)^2 dnu(x)
      >= integral d(o,x)^2 dnu(x)+d(o,y)^2.

Averaging over y doubles the second moment at o. The chord kernel is bounded and Borel on the support product, so averaging its almost-everywhere center bound is valid; no joint choice of chart derivatives is required. Therefore

    integral d(o,x)^2 dnu(x)<=C+(D^2/2)sqrt(gamma(C-1)).

The all-center radial inequality at o with g=1 gives 1<=integral d(o,x) sqrt(1-|Dr|^2)dnu<=integral d(o,x)dnu. Expanding the square gives

    integral (d(o,x)-1)^2 dnu
      <=C-1+(D^2/2)sqrt(gamma(C-1))=epsilon_n(lambda).

For every x in support A, put t=|d(o,x)-1|. Its radial-error function is 1-Lipschitz. On B(x,min(t/2,r0)) the absolute error is at least t/2. The all-point density bound gives

    epsilon_n m >= (t^2/4)b min(t/2,r0)^n.

When t/2<=r0 this gives t<=2(m epsilon_n/b)^(1/(n+2)); in the other case it gives t<=2(m epsilon_n/(b r0^n))^(1/2). Substitution m<=mbar gives precisely the frozen maximum Psi_n. This proof applies to every support point, including those outside all regular chart centers. If epsilon_n=0, every positive t contradicts the same estimate, so the error vanishes everywhere.

Returning to the original metric multiplies the normalized diameter by rho and replaces d(o,x) by d(o,x)/rho in the two radial statements. The probability measure is unchanged because both numerator and total mass acquire the same factor; the minimizer of the squared-distance functional is unchanged because the functional is multiplied by a positive scalar. Connectedness is unchanged.

Finally R_A/R_T=(M(A)/M(T))^(1/n). Taking the 1/(n+1) power of the mass-ratio-to-the-q inequality and dividing by H proves exactly the stated radius interval. The identity L_T=omega_(n+1)R_T^(n+1) follows from s=(n+1)omega_(n+1). All displayed constants are finite and dimension-only for n>=3. C(0)=1 gives epsilon_n(0)=Psi_n(0)=0, and continuity gives the stated limit as lambda goes to zero.

## 7. Objection disposition and limits of this verdict

No error, unproved compatibility, or counterexample to the frozen statement was found. The potentially decisive objections were checked rather than assumed away: filling continuity; replacing the source's strict mass premise; chart closure without normal chart restrictions; arbitrary radius-distribution singular parts; the C>1 initial condition; the sign of its differential inequality; the exact tangent coefficient; both K_* branches; and every-point upgrade. None requires altering the unchanged author proof.

The r58 original scope and proof selections, and the actual Q286 iteration and experiment selections, were independently read as historical boundary checks. They are not premises of the present PASS. The old T337E scope still concerns a full isometrically embedded Euclidean ball, unit multiplicity, and n>=2; this review does not replace or re-review its disposition. Q286 still asks for a squared full-volume geodesic asymmetry estimate for arbitrary finite-volume finite-perimeter sets in smooth Cartan-Hadamard manifolds; it is not established by the present selected-cycle shell result. There is no new n=2 claim, flat-sphere claim, Euclidean ball-current proximity claim, or control of the original support T.

The exact source/primary/history reading extents, omitted material, navigation exposure and authentication limits are recorded separately. Numerical diagnostics and artifact seals are not proof premises. No worldwide reading, exhaustive project search, or perfect-isolation claim is made.
