# Analytic161 / T337A161: independent contribution review, round 1

**Verdict: TECHNICAL, conditional on correctness, for the entire unchanged frozen statement.**

The object of this judgment is the statement with SHA256 `53f35f024803059dd77264ffc0f00d0c20209a3768e61551e8285eccaf7d5b38`, with author proof SHA256 `22d6114f858c90872c502560f6b814766aab096f65cc16b081ee01d107577e2f`. The judgment includes the displayed epsilon and Psi, every integer n>=3, the complete allowed deficit interval including zero, arbitrary integer multiplicity, unrestricted ambient dimension, and all filling, mass, radius, connectedness and diameter conclusions. It does not replace this statement with a qualitative subsequence result, a Euclidean specialization, or an assertion about another scope.

The positive-deficit estimate is real additional mathematical content relative to a verbatim statement of the source or r58. Nevertheless, the operative proofs already supply the difficult current calculus, the critical threshold, the exact chord kernel and scalar identity, and its large-parameter density comparison. After a standard penalization restores the source comparison inequality, the remaining quantitative step is a one-variable perturbation estimate with a bounded fourth moment. Below I give the entire compatible composition, including its constants. That is the affirmative reason for TECHNICAL. Absence of an identical published theorem, or failure of integration from zero, is not the reason. Neither a correctness verdict nor the dispositions of old work were used as novelty evidence.

This is not a correctness gate. The reconstruction below is an independently articulated contribution comparison and contains new deductions that still require separate correctness review. It does not assign correctness PASS, acceptance, a finding count, or worldwide priority.

## 1. Exact dependencies and what is already paid

Write S for the pinned **Sharp integral fillings in CAT(0) spaces**, and G for **Generalized Cartan–Hadamard isoperimetry and Euclidean equality rigidity**, both at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Their results and operative proofs are stipulated true. The private selected source copies were independently matched by size and Git blob to the complete supplied preprint tree, whose SHA256, 4,858,136 bytes and 13,223 entries were checked. This is authentication, not mathematical evidence.

The operative S dependencies are:

* Section 02, `thm:current-background`, `lem:extremizer`, `prop:chart-mass`, `lem:euclidean-density`: compact reduction, compactness, actual filling continuity, attainment, comparison by replacement, Euclidean chart metrics, and integer mass density. In particular filling continuity is supplied by Wenger's theorem, not deduced from weak lower semicontinuity.
* Section 03, `prop:radial`: its deformation proof requires the comparison inequality and normalization, not the sign of the difference between the comparison coefficient and the sharp constant.
* Section 04, `prop:small-set`, `lem:intrinsic-coarea`, rearrangement and `prop:almost-sobolev`: replacement and coarea provide the almost-sharp critical coefficient without a smooth support assumption.
* Section 05, `prop:sobolev-space`, `prop:compact-embedding`, the proof of `prop:minimizer` after its constant-test step, `lem:powers` and `lem:composites`: gradient closure, L2 compactness, subthreshold attainment and admissible nonlinear tests. The occurrence of m<s in the minimizer construction is specifically the constant test at lines 424–428; subthreshold attainment itself uses Lambda<S_*.
* Section 06, `lem:completed-radial`, `prop:chord-transform`, `lem:chord-density`: the profile, integral identity, differential inequality and asymptotic tangent coefficient. Section 07, `lem:opposite-average`, supplies the contrary average for a hypothetical subthreshold minimizer and proves CAT(0) variance directly.

The actual original r58 T337E proof, sections 1–8, was read. Its n>2 branch already moves the source to the equality threshold, rules out a quotient below S_*, specializes to constant weight, and assembles chord and barycenter bounds. Its n=2 tangent-cone, scalar-normal collapse and degree operations belong to that old exact-equality scope and are not recycled here as new quantitative content. r58's full statement includes all n>=2 and equivalence with a unit-multiplicity Euclidean ball boundary; the present review changes none of that.

Bögelein–Duzaar–Fusco's 2015 paper (BDF), Section 5, already pays the penalized-selection mechanism at current level: minimize a geometric functional plus filling-distance-controlled penalties; subtract a competitor inequality; bound each penalty difference by the mass of a connecting filling. Its Lemma 6.1 pays bounded-support reduction in Euclidean space by cutting a filling into coordinate slabs and rescaling. Its Theorem 6.2 uses Euclidean tubular coordinates and elliptic excess regularity to obtain graphs. I credit all these antecedents, but use neither its graph theorem nor its coordinate-slab reduction as an arbitrary-CAT(0) theorem. [Primary paper](https://ems.press/content/serial-article-files/39832?nt=1).

Wenger's Theorem 1.4 and Propositions 5.8–5.9 explain the filling-continuity input: weakly null bounded cycles are decomposed into small pieces with inexpensive cone fillings plus a residual whose concentration vanishes; iteration and the Euclidean-exponent filling bound finish the estimate. This is an existing input, explicitly also stipulated in S. [Primary paper, v1](https://arxiv.org/pdf/math/0508072v1).

## 2. Selection, including the exact mass and filling estimates

Use precisely the frozen constants s,c,q,lambda_n,mbar,a0,b,r0,D,gamma. Let Y be a compact convex closed ball containing spt T. Nearest projection onto Y preserves cycles supported there and does not increase filling mass, so V_Y=V_X on those cycles. Every relevant infimum in Y is attained by a compactly supported integral current. The linear cone bound is V(B)<=L_Y M(B).

For delta>0, put lambda=sqrt(delta) and minimize

    F(B)=c M(B)^q - V(B) + lambda V(B-T)

over integral n-cycles in Y. This is a direct perturbation of S's extremizer functional by a filling-distance penalty of the BDF type. The first two terms together are nonnegative by the stipulated sharp theorem. Coercivity follows from F(B)>=c M(B)^q-L_Y M(B). On a bounded-mass minimizing sequence, compactness, filling continuity for B and B-T, and mass lower semicontinuity give a minimizer A. Since F(A)<=F(T)=delta L_T,

    V(A-T)<=lambda L_T,
    0<=c M(A)^q-V(A)<=delta L_T.

Subadditivity gives

    V(A)>=(1-lambda-lambda^2)L_T>0,
    c M(A)^q<=V(T)+lambda L_T+delta L_T=(1+lambda)L_T.

This proves nonzero A and both exact mass bounds; an attaining filling of A-T is Q. There is no multiplicity truncation. Comparison against any cycle B gives

    c(M(A)^q-M(B)^q)
      <=V(A)-V(B)+lambda[V(B-T)-V(A-T)]
      <=(1+lambda)V(A-B).                         (2.1)

For delta=0 choose A=T,Q=0. The nonnegative unpenalized deficit is minimized at T, so the same comparison holds with lambda=0. No continuity of selected minimizers in delta is needed.

Set H=1+lambda, R_A=(M(A)/s)^(1/n), rho=R_A/H, and rescale the metric by 1/rho. In the normalized metric,

    m=M(A)=s H^n<=mbar,
    c_eff=c/H,
    c_eff q m^(1/n)=1/n,
    c_eff(m^q-M(B)^q)<=V(A-B).                    (2.2)

Both sides have degree n+1. Metric rescaling requires no ambient geometric homothety. All estimates until section 7 use this normalized metric.

## 3. Source radial and Sobolev inequalities at the new coefficient

S03's actual radial deformation sends x along [y,x] with fraction 1-tg(x). Its endpoint and swept-current estimates are

    M(B_t)<=m-t integral(ng+r Dr.Dg)dmu+O(t^2),
    M(D_t)<=t integral r g sqrt(1-|Dr|^2)dmu,
    boundary D_t=B_t-A.

Insert these into (2.2) and use c_eff q m^(1/n)=1/n. For every center y in Y and nonnegative Lipschitz g,

    integral(ng+r Dr.Dg)dmu
      <=n integral r g sqrt(1-|Dr|^2)dmu.          (3.1)

The proof's determinant calculation uses CAT(0) comparison, not Euclidean graphical regularity. The sign of c_eff-c is absent.

The small-set proof likewise needs only (2.2). Fill the boundary of a superlevel restriction U, of mass a, by R, of mass d, using the sharp (n-1)-cycle coefficient. When d<a<=m/2, comparison with A-U+R gives

    2^(-1/n)(a-d)/n <= K_n(2a)^q.

Thus d>=a-O(a^q). Combining with

    d<=[P/(n omega_n^(1/n))]^(n/(n-1))

recovers S04's almost-Euclidean small-set perimeter coefficient. Its actual coarea proof treats the absolutely continuous density of distributional derivatives and allows atoms and singular parts. Its rearrangement and truncation proof therefore yields, for every eta>0,

    (S_*-eta)||u||_p^2 <= 4/(n-2) E(u)+C_eta||u||_2^2,
    p=2n/(n-2),  S_*=n s^(2/n).                   (3.2)

S05's closed-gradient and compact-embedding proofs use the whole-cycle identity, finite mass, Euclidean chart metrics, and (3.2). They allow unbounded signed integer multiplicities; they do not use m<s. Hence their completed space is available here.

To prove

    Q(u):=4/(n-2) E(u)+n||u||_2^2 >= S_*||u||_p^2, (3.3)

suppose the quotient infimum Lambda<S_*. The source proof after the constant-test line gives attainment: critical splitting, with t=int|u|^p, gives

    Lambda >= Lambda t^(2/p)+S_*(1-t)^(2/p),

forcing t=1. Its normalized minimizer v has W=int v^p=(Lambda/n)^(n/2)<s and satisfies the source Euler equation. S05's powers and composite tests then apply. S06 bounds its weighted chord moments by 2(W/s)^(2/n)<2; S07 bounds their average below by 2. Contradiction proves (3.3).

This is the r58 threshold argument with the unnecessary equality upper test removed. We do not assert that the constant function is a quotient minimizer when H>1, and we do not assert m<s. The move uses no new Sobolev stability theorem.

## 4. Connectedness and dimension-only localization, without graphs

If K=spt A is disconnected, compactness gives a separation K=K1 union K2 into nonempty compact sets at positive distance. A Lipschitz cutoff and a regular empty slice split A into two mass-additive integral cycles. Let the smaller mass be a<=m/2. Apply (2.1) to the other cycle and fill the smaller cycle sharply:

    m^q-(m-a)^q <= H a^q.

For z=m/a>=2, z^q-(z-1)^q is increasing and at least 2^q-1. But lambda<=lambda_n<2^q-2, so H<2^q-1. This proves connectedness, including at both ends of the deficit interval. This is convexity of the already present mass power, not a geometric regularity input.

Fix x in K and let a(r)=mu(B(x,r)), for open balls. For almost every r, U=A restricted to B(x,r) is integral and P=M(boundary U)<=a'(r). Fill its boundary by R with d=M(R)<=c_(n-1)P^(n/(n-1)). If a<=m/2 and d<=a/2, the very same small-set replacement argument, now using the sharp degree-n filling coefficient rather than a coarse K_n, gives

    2^(-1/n) a/(2n)
      <=c_eff[m^q-(m-a+d)^q]
      <=V(U-R)<=c(3a/2)^q.

Algebra forces

    a>=Acrit=s(n+1)^n/[n^n 3^(n+1)]=4a0.

As a0<m/2, for 0<a(r)<=a0 the preceding alternative is impossible. Consequently

    a'(r)>=[a(r)/(2c_(n-1))]^((n-1)/n).

Integrate the absolutely continuous derivative of the monotone function a^(1/n); its singular derivative is nonnegative. At a support point a(r)>0 for every r>0, and integration starting at t>0 followed by t down to zero gives

    mu(B(x,r))>=min{a0,b r^n},
    b=1/[n^n(2c_(n-1))^(n-1)]=omega_n/2^(n-1).   (4.1)

Monotonicity gives the estimate after the threshold is reached; increasing radii from below supply it at exceptional radii. No absolute continuity of the entire ball-mass function is assumed.

Every open r0-ball centered on K therefore has mass at least a0. The continuous distance from a diameter endpoint maps connected K onto [0,diam K]. Choose points at distance levels 0,3r0,...,3Nr0, N=floor(diam K/(3r0)). Their open r0-balls are disjoint. Thus (N+1)a0<=m<=mbar and, in particular,

    diam K<=3 r0(mbar/a0+1)=D.                    (4.2)

This supplies all localization needed below. It is paid by S04's slice replacement and elementary packing, and does not use an ambient covering number. BDF's localization is credited as prior technique, but no coordinate-slab theorem is transplanted into X.

## 5. The finite-defect chord calculation and why it is technical

Fix y in K, let r=d(y,.), nu=mu/m, L=int r^2 dnu, k=(n-2)/2>0, and

    J(a)=int(1+a r^2)^(-n)dnu,
    G(a)=k int_0^1 J(au)u^(k-1)du,
    h=G^(-1/k),  C=H^(2n/(n-2)).

S06's completed square gives

    int(ng|Dr|^2+r Dr.Dg)dmu <= (n/4) int r^2g dmu.

Its explicit profile w(t)=(1+at^2)^(-k) and f(t)=int_0^1 z^(n-1)w'(zt)^2 dz obey nf+tf'=w'^2. Apply the square to g=f(r). The ordinary energy definition, without an Euler equation for 1, yields

    Q(w(r))<=nm int[w(r)^2+r^2 f(r)/(n-2)]dnu=nm G(a).

The final identity is S06's exact scalar identity (lines 286–315), obtained by integrating the derivative of u^k/(1+zu)^(n-2). Since m=sH^n, (3.3) now implies

    H^(-2) J^((n-2)/n)<=G,
    J<=C h^(-n/2),
    a h'=h-JG^(-n/(n-2))>=h-C.                  (5.1)

The source has C=1. For C>1, taking a zero-start derivative of (h-C)/a is uninformative. That failure alone says nothing about contribution size. The following elementary lemma is the entire additional scalar operation.

**Perturbed slope lemma.** If h>0 on [0,infinity), a h'>=h-C for a>0, C>=1, and

    h(t)>=1+ell t-B t^2  (t>=0),

then for C>1, B>0, t_* = sqrt((C-1)/B),

    h(a)>=C+a[ell-2sqrt(B(C-1))]  (a>=t_*).       (5.2)

Indeed (h(a)-C)/a is nondecreasing. Starting at any t>0 bounds it below by ell-(C-1)/t-Bt. Minimize the two error terms by t=t_*. For C=1 let t down to zero to obtain h(a)>=1+ell a. This is an integrating-factor argument and minimization of x/t+Bt. It requires no compactness rate, uniform tangent scale, spectral theorem, regularity improvement, or new geometric comparison.

For the present transform the hypothesis is obtained directly from the kernel, uniformly for all a>=0. Its third derivative has negative sign, so

    (1+z)^(-n)<=1-nz+n(n+1)z^2/2  (z>=0).

Integrate against nu and k u^(k-1)du. With E4=int r^4 dnu<=D^4 this gives

    G(a)<=1-(n-2)La+[n(n+1)k/(2(k+2))] E4 a^2.

Convexity of z^(-1/k) at z=1 yields

    h(a)>=1+2La-gamma D^4a^2,
    gamma=n(n+1)/(n+2).                          (5.3)

Apply the lemma with ell=2L, B=gamma D^4. It gives exactly the author starting parameter a_*=sqrt((C-1)/gamma)/D^2 and slope

    K_*=2L-2D^2 sqrt(gamma(C-1)).

If K_*<=0 the desired moment bound is immediate. If K_*>0, (5.1)–(5.2) give

    limsup a^(n/2)J(a)<=C K_*^(-n/2).             (5.4)

At mu-almost every y, S06's actual tangent-density proof, specialized to weight 1, gives

    liminf a^(n/2)J(a)>=s/(2^n m).                (5.5)

Here a chart is rescaled at a Lebesgue point, Fatou is applied on a fixed coordinate ball, and the radius of that ball is then increased. Its coefficient is |theta| int_R^n (1+|z|^2)^(-n)dz/m=|theta|s/(2^n m). Integer |theta|>=1 is sufficient; neither unit multiplicity nor an upper multiplicity bound is needed. Nothing is required about a rate of tangent convergence. The finite-start estimate is global for all a>=a_*, so it can be compared with arbitrarily large tangent parameters.

Combining (5.4)–(5.5) gives

    K_*<=(2^n C m/s)^(2/n)=4 C^(2/n)H^2=4C,

and hence the exact bound

    L<=2C+D^2 sqrt(gamma(C-1)).                   (5.6)

For C=1 the zero-defect part of the slope lemma gives h(a)>=1+2La; (5.5), now with m=s, implies L<=2. Thus (5.6) includes lambda=0 directly.

This comparison identifies a complete paid path to the central new formula. The fact that the optimal positive starting parameter was not printed in S does not make it a new nonroutine operation: the same kernel has an explicit, globally signed Taylor remainder, the same integrating factor works, and the only new optimization is x/t+Bt. The dimension-only fourth-moment bound has already been supplied in section 4 without a further hypothesis. The lower tangent coefficient is literally the source's proof. This is more than saying 'the proof is short': it isolates all the inputs and shows that the potentially missing bridge is elementary and fully supplied at the exact hypotheses.

## 6. Barycenter and every-point assembly

The probability measure nu is compactly supported in Y. Squared-distance minimization on Y and CAT(0) strict convexity give its unique barycenter o. Projection onto Y lowers squared distance to its support, so this is also the unique barycenter in X. The variance proof in S07 gives

    int d(y,x)^2 dnu(x)>=int d(o,x)^2dnu(x)+d(o,y)^2.

Average in y and use (5.6). The distance kernel is bounded and Borel, so no common chart-derivative null set is needed. It follows that

    int d(o,x)^2dnu(x)<=C+(D^2/2)sqrt(gamma(C-1)).

The all-center radial inequality (3.1) with center o and g=1 gives

    1<=int d(o,x)sqrt(1-|D d_o|^2)dnu<=int d(o,x)dnu.

Subtracting twice the latter mean from the second moment and adding 1 proves exactly

    int(d(o,x)-1)^2dnu<=C-1+(D^2/2)sqrt(gamma(C-1))
                       =epsilon_n(lambda).       (6.1)

For any x in K put t=|d(o,x)-1|. The distance function is 1-Lipschitz. On B(x,min(t/2,r0)) its absolute deviation from 1 is at least t/2. By (4.1) and (6.1),

    m epsilon_n >= (t^2/4)b min(t/2,r0)^n.

The cases t/2<=r0 and t/2>=r0 yield, respectively,

    t<=2(m epsilon_n/b)^(1/(n+2)),
    t<=2(m epsilon_n/(b r0^n))^(1/2).

Since m<=mbar, their maximum is exactly the frozen Psi_n(lambda). This is the elementary conversion of an L2 estimate for a Lipschitz function to a uniform estimate using a lower ball-mass bound. It covers every support point, not only the rectifiable full-measure set used in (5.5). If epsilon_n=0 it forces t=0 everywhere.

## 7. Full-scope coverage and restored units

Metric rescaling leaves nu and its barycenter unchanged. Restoring the factor rho gives diam K<=D rho and the stated deviations of d(o,x)/rho. The already proved mass ratio satisfies

    (1-lambda-lambda^2)^(1/(n+1))<=R_A/R_T
       <=(1+lambda)^(1/(n+1)),

so division by H gives both exact radius bounds. Q and its mass were obtained in the original metric. Continuity of the displayed C,epsilon and Psi at lambda=0 gives Psi_n(0)=0 and the claimed limit. This is not a numerical or small-lambda-only argument: the Taylor bound is global, the finite parameter can be any positive value, and lambda_n ensures positivity and the strict connectedness inequality throughout the closed allowed interval.

There is no upper dimension restriction: k>0 and the u^(k-1) integrability hold for every n>=3, and the lower-dimensional filling used for n=3 is exactly the stipulated integral 2-cycle theorem. No n=2 quantitative statement is inferred. The chart arguments retain arbitrary signed integer multiplicities. Compactness is used only after properness and compact support give Y. There is no geometric convergence across varying ambient spaces and no ambient doubling or dimension assumption. Thus the composition covers the full frozen package, not only its central moment estimate.

## 8. Stronger comparisons and rejected shortcuts

BDF proves squared filling asymmetry to flat disks in Euclidean space, with constants depending on its dimension and codimension. In the frozen notation its perimeter deficit is related to ours by D_BDF=(1-delta)^(-n/(n+1))-1 after matching cycle dimension; the measures of asymmetry are different. Its main proof passes through a limiting unit disk, penalized minimizers, density/support convergence, Euclidean spherical graphs, moment normalization, and a Fuglede-type estimate. The graph step cannot be asserted in arbitrary proper CAT(0). The present TECHNICAL judgment uses none of it; the complete replacement route is sections 2–7 above. The paper's printed dimension notation differs from the frozen cycle dimension by one. [BDF primary](https://ems.press/content/serial-article-files/39832?nt=1).

Bianchi–Egnell's actual local proof projects a Euclidean Sobolev function onto the Aubin–Talenti optimizer manifold, removes its tangent directions, and uses a spectral gap for the weighted Euclidean operator in a quadratic expansion. Its global proof adds compactness modulo translations and dilations. These are not facts about an arbitrary current's chart Sobolev space. The more recent Dolbeault–Esteban–Figalli–Frank–Loss proof obtains explicit dimension dependence using competing conformal symmetries and continuous rearrangement, then a local spherical estimate. Its actual Section 3.1 and final assembly still require the Euclidean optimizer family, conformal invariance and rearrangements. They do not provide an automatic identification of the current space with that setting. No such identification is used here. The nominee instead uses the already stipulated exact threshold and tests its explicit kernel directly. [Bianchi–Egnell primary](https://people.dimai.unifi.it/bianchi/lavori/bianchi_egnell_sobolev.pdf); [DEFFL author-hosted primary](https://people.math.ethz.ch/~afigalli/papers-pdf/Sharp-stability-for-Sobolev-and-log-Sobolev-inequalities-with-optimal-dimensional-dependence.pdf).

Hoisington's Theorem 1.4 proof and its zero-curvature consequence Proposition 4.2 give a smooth hypersurface chord-integral refinement via geodesic flow, winding multiplicity and Jacobian comparison. This is substantive chord antecedent work. It does not supply the present current selection or the upper second moment from the frozen filling deficit: its volume-squared inequality has a different chord integrand, and its geodesic-flow measures require a smooth finite-dimensional ambient manifold. The present quantitative path uses S's stronger compatible current kernel. [Hoisington, v1](https://arxiv.org/pdf/2111.06860v1).

G's actual sharp hypersurface Sobolev proof and its exact-rigidity moment proof were read. The latter expands at a constant with zero slack and uses logarithm coordinates after equality regularity and constant mean curvature. A positive constant slack cannot be removed by differentiating twice. The nominee avoids that issue by current selection and (5.3); it does not prove a quantitative version of G's regularity or flatness. Stadler's density-one equality proof is also an exact statement; no quantitative rigidity is extracted from it. [Stadler, Proposition A.1, v1](https://arxiv.org/pdf/2212.07100v1).

The original Q286 calculations were read independently, including the explicit oscillatory sphere patch with amplitude k^(-3/2), perimeter deficit O(k^(-1)) and curvature-energy growth at least ck, the radial-excess divergence estimate, finite-volume approximation, and the logarithmic volume-distortion obstruction. Q286 asks for a quadratic bound on geodesic-ball volume asymmetry of the original finite-perimeter set in all smooth Cartan–Hadamard manifolds, including unbounded/disconnected sets and all dimensions >=2. The selected-current shell theorem neither has that statistic nor that rate or support scope. Its relation to those obstacles explains why it can be proved, but does not confer substantial status automatically. No scope or disposition of Q286 or T337E is revised.

The author correctly identifies a genuine difference between C=1 and C>1. I disagree only with elevating that difference, after the strongest compatible reductions, to a substantial-contribution judgment: (5.2) and (5.3) pay it entirely by elementary calculus with an already available bounded moment. There is no unpaid stronger theorem in this comparison. The nontrivial source operations remain fully credited to the source; the complete application is useful but technical under the requested standard.

## 9. Limits of this conclusion

This is a selective primary-proof comparison, not an exhaustive literature search. The exact read extents, navigation-only acquisitions, truncation recoveries and omissions are in READING-AND-ISOLATION.md and the private records. In particular I did not independently reread every theorem imported by BDF's regularity theorem or every foundational theorem in Wenger, and I did not read DEFFL's entire local-stability and rearrangement-appendix proofs. None is used as a bridge in sections 2–7. The affirmative technical derivation rests on the stipulated S operative arguments that were read, r58's already present threshold operation, and the elementary deductions displayed here. Those limits prevent an exhaustive or priority claim; they do not leave a missing primary premise in that derivation.
