# I239 — independent analytic check

**Verdict: PASS.** This is an independent proof check of finalized I236, analytic SHA-256 `a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931`, relative to the stipulated OpenAI package at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No substantive repair or additional hypothesis is needed. The expansions below verify the abbreviated operations; they are not replacements for a failed estimate.

## 1. Quantified statement and proof dependencies

For every integer m>=1, every fixed 0<tau<infinity, and every finite C0>=0, suppose V is continuous on R^m x R and is a viscosity solution of

    G_tau(DV,D²V)=tr(A_tau(D_xV)D²V)=0,
    A_tau(p)=[tau I+p p^T, p; p^T, 1].

At every center z=(x,t) and every R>0, suppose some p in R^m and a in R satisfy

    |V(x+h,t+l)-V(x,t)-p.h-(a-|p|²/2)l| <= C0 R
    for every |l|<=R and |h-pl|<=R.                         (FIT)

The p,a may depend on both z and R; one C0 works everywhere. The conclusion is that V is affine. Upper tests mean G_tau>=0, lower tests G_tau<=0, including horizontal gradient zero. No bounded-gradient assumption on V, local regularity theorem REG_tau, p-approximation convergence, or uniformity in tau is used.

The stronger intermediate contact theorem is also proved: on any connected open Omega, a continuous locally spatially semiconcave G_tau-subsolution u below a continuous G_tau-supersolution v agrees with v throughout Omega if they agree somewhere. Spatial semiconcavity must have one finite constant on each sufficiently small product cylinder. The proof only requires local constants, which may depend on the cylinder and tau.

Accepted inputs from the pinned package are the equation-independent theorem of sums; the fit comparisons, growth, moduli and geometric compactness in source 04; and finite barycentric attainment, duality, continuity, semiconcavity and the extremal measure construction in source 05. The original homogeneous Liouville conclusion, finite Hamiltonian slopes and source 06–08 propagation are not applied to the altered equation. Every place involving a changed PDE is checked below.

## 2. Lemma 2.1: spatial semiconcavity really gives time Lipschitz continuity

Choose a larger compact product cylinder and a smaller one of base points with uniform positive spatial and time margins. Let K>=0 bound spatial semiconcavity on the larger cylinder and M bound |u| there. At each base (x0,t0), concavity of u(.,t0)-K|.|²/2 supplies a supergradient p with

    u(x0+z,t0)<=u(x0,t0)+p.z+K|z|²/2  (|z|<=r).

The fixed radius r can be chosen for all base points. Evaluating this inequality at z=+/-r e gives a uniform bound on |p.e| for every unit e, hence |p|<=L. This works for every such supporting p; no measurable or continuous selection is necessary. Supporting inequalities at two spatial points also give the usual uniform interior spatial Lipschitz bound.

Fix p for this base and maximize

    h(t)=max_{|z|<=r}[u(x0+z,t)-p.z-(K+1)|z|²/2].

At t0 the center is the unique maximizer and the entire boundary has deficit at least r²/2. Uniform continuity of u on the larger compact cylinder supplies one time modulus omega, independent of x0,t0,p. Choosing s within the time margin and with omega(s)<r²/8 leaves boundary deficit at least r²/4 relative to the central competitor for |t-t0|<s. All maximizing points are interior, for the whole interval, with the same r,s. Also |h|<=H=M+Lr+(K+1)r²/2.

If psi is an upper scalar test of h at t and z is any maximizing displacement, then psi(T)+p.(Y-x0)+(K+1)|Y-x0|²/2, adjusted by a constant, is a genuine local upper test of u at (x0+z,t). Its mixed Hessian is zero, its spatial Hessian is (K+1)I, and its horizontal gradient has norm at most L+(K+1)r. Therefore

    psi''(t)>=-C,
    C=(K+1)[(L+(K+1)r)²+tau m].

The scalar implication is in the correct direction: every upper test of h+C(t-t0)²/2 has nonnegative second derivative, hence that function is convex. To verify without regularity assumptions, failure of a chord inequality gives an interior maximum above the chord; subtract a sufficiently small concave quadratic from that positive excess to get an upper touching quadratic of strictly negative curvature. This contradicts the test inequality. Bounded convex functions have bounded secant slopes on an interval a fixed distance from its endpoints. Thus h is Lipschitz on |t-t0|<s/2 with a bound depending only on H,C,s.

Since u(x0,t)<=h(t) and h(t0)=u(x0,t0), this gives the upper estimate for u(x0,t)-u(x0,t0). It does not give the lower estimate by itself. For that estimate, repeat the entire construction with base (x0,t) and compare its support maximum at t0. All constants remain the same, so reversing the two times gives the opposite inequality. Combining with the spatial estimate proves local full Lipschitz continuity. This pays the delicate missing time estimate and makes no claim of space-time semiconcavity.

For W=C_t V-kappa²t/2, the accepted envelope identity gives D_xx W<=I/t. Every positive-time compact cylinder has a uniform constant 1/t_min, and W is continuous. The lemma therefore applies to the actual W.

## 3. Full-space cone infimum and recovery of original contact

Take a full Euclidean ball with a larger compact neighborhood where u has Lipschitz constant L0. Choose L>L0 and r>0 small enough that z+h stays in that neighborhood for the considered z and |h|<=r. Define

    v_L(z)=min_{|h|<=r}[v(z+h)+L|h|].

The shift set is compact, so minima are attained and the minimum is continuous. For every competitor,

    v(z+h)+L|h|>=u(z)+(L-L0)|h|.

Thus u<=v_L<=v. At original contact the minimizer is h=0. For any minimizing h one also has (L-L0)|h|<=v(z)-u(z); continuity at contact confines all minimizers to |h|<r/2 on a smaller neighborhood.

If phi touches v_L from below at z and h attains the minimum, then phi(z')<=v_L(z')<=v(z'+h)+L|h| nearby, with equality at z. Translate this fixed test to z+h. The equation is autonomous and independent of the value of v, so the translated test proves G_tau[phi]<=0. There is no differentiation of h or |h|. The truncation does not affect this argument.

For nearby z,z', take h minimizing at z and use h+z-z' as the competitor at z'. It is admissible because of the interior margin. This gives v_L(z')-v_L(z)<=L|z-z'|; reversing the points gives local L-Lipschitz continuity. Crucially v_L(z)=u(z) forces (L-L0)|h|=0. Hence h=0 and v(z)=u(z). Equality for the regularized pair really does recover equality for the original pair.

## 4. Viscosity-to-weak passage for the explicit exponential flux

Let P=(p,q), a(P)=exp((q+|p|²/2)/tau)(p,1). Direct differentiation gives

    Da(P)=exp((q+|p|²/2)/tau) A_tau(p)/tau.

This is symmetric positive definite. On every full gradient ball |P|<=M it has fixed positive lower and finite upper eigenvalue bounds. For example use A[(xi,s)]=(p.xi+s)²+tau|xi|² and s²<=2(s+p.xi)²+2M²|xi|² for the lower bound. The time component q must be bounded to bound the exponential; Lemma 2.1 and the full cone, not horizontal Lipschitz continuity alone, provide that bound.

For a locally M-Lipschitz viscosity subsolution f, first choose an outer bounded neighborhood and a compact inner region containing the test support. Full-variable sup convolution over the outer neighborhood is sufficient; no extension preserving the PDE outside that neighborhood is assumed. The maximizing y satisfies |y-z|<=2M epsilon by comparison with y=z, so for small epsilon all needed optimizers and translated contacts stay inside the outer neighborhood. The convolution is locally M-Lipschitz, converges uniformly, and is semiconvex with D²f^epsilon>=-I/epsilon. A fixed optimizing shift pulls an upper test back to f, with identical derivatives; autonomy preserves the viscosity subsolution inequality exactly.

At almost every Alexandrov point the quadratic expansion plus delta|z-z_*|² is an upper test on a sufficiently small ball. Letting delta decrease to zero proves

    tr(Da(Df^epsilon)D²f^epsilon)>=0 a.e.

At fixed epsilon, mollify on the inner region. The smooth f_j^epsilon satisfy the same gradient bound and lower Hessian bound, hence

    div a(Df_j^epsilon)>=-n Lambda_M/epsilon.

This is a uniform-in-j, locally integrable lower bound; it need not be uniform in epsilon. The mollified Hessians converge almost everywhere to the Alexandrov Hessian. More explicitly the distributional Hessian of a semiconvex function is a locally finite matrix measure, whose singular positive part has zero Lebesgue density almost everywhere and whose absolutely continuous density is the Alexandrov Hessian. Approximate identities give the claimed a.e. convergence. This is the precise fact discussed in Julin–Juutinen, Remark 3.3, and is used after fixing epsilon.

For nonnegative smooth compactly supported phi, dominated convergence for the bounded flux and one-sided Fatou for the divergence give

    -int a(Df^epsilon).Dphi
       =lim_j int phi div a(Df_j^epsilon)
       >=int phi tr(Da(Df^epsilon)D²f^epsilon)>=0.

The finite left side also bounds the nonnegative density integral locally. The proof has not equated the distributional Hessian with its a.e. density or thrown away singular curvature of the wrong sign. Reversing the inequality uses inf convolution, an upper Hessian bound, and Fatou for minus the divergence.

The nonlinear epsilon-limit is separately paid. At a differentiability point z of f write y=z+epsilon b_epsilon for any maximizer. The b_epsilon are bounded. Differentiability of f yields a uniform o(epsilon) error over all these displacements. Compare the maximizing value to the admissible displacement epsilon Df(z) and complete the square to obtain

    |b_epsilon-Df(z)|²/2=o(1).

At differentiability points of f^epsilon, differentiating the fixed active quadratic gives Df^epsilon=b_epsilon. Along any countable epsilon sequence, remove the null sets for f and all its convolutions. Their gradients then converge a.e., and a(Df^epsilon) converges in L¹ on the support by boundedness. The inf-convolution argument has displacement -epsilon Df(z) and gradient -b_epsilon. Thus locally Lipschitz subsolutions satisfy div a(Df)>=0 and supersolutions satisfy <=0.

Only this implication is needed. If the phrase “bounded-gradient weak equivalence” is used, its converse also follows locally: for a Lipschitz weak subsolution, an upper test with G_tau<0 gives a smooth strict weak supersolution on a small ball; lower it by a small constant so it still dominates on the boundary but is below f at the center. Test the difference inequality with its positive part. Strict monotonicity of a on the bounded gradient range forces that part to vanish, a contradiction. Make contact strict by adding a fourth-order term first if needed. Lower tests reverse the argument. None of these statements applies to an arbitrary continuous V without the prior Lipschitz reduction.

## 5. Linear replacement, Harnack, traces, and contact propagation

For a locally Lipschitz ordered sub/supersolution pair set d=v-u>=0. On a sufficiently small outer ball both gradients lie in one ball |P|<=M a.e. Define

    B(z)=int_0^1 Da(Du+s(Dv-Du)) ds.

It is measurable, symmetric, uniformly bounded and uniformly positive definite. The gradient segment remains in that same ball. The fundamental theorem of calculus gives B Dd=a(Dv)-a(Du), so

    int B Dd.Dphi>=0 (phi>=0), i.e. div(B Dd)<=0.

For every ball B_r(z0) within this neighborhood, solve the linear Dirichlet problem for w with w-d in H¹_0(B_r) by the bounded coercive bilinear form and Lax–Milgram. Negative-part testing gives w>=0. Subtract the inequality for d from the equality for w and test with (w-d)^+ in H¹_0. Approximation by nonnegative smooth tests is legitimate because the bounded coefficients and H¹ gradients define a continuous functional. The result is the energy of (w-d)^+<=0; thus 0<=w<=d a.e.

Interior Hölder continuity and Harnack apply to this weak solution w with measurable symmetric elliptic coefficients. Since d is continuous and d(z0)=0, w's continuous representative satisfies w(z0)=0. Solution Harnack on cubes and a finite chain inside the ball give w=0 everywhere in that ball. No Harnack assertion for general supersolutions has been substituted. In dimension n=2 the same standard conclusion holds; if one uses a presentation of the proof employing the n>2 Sobolev exponent, lift w and B to one extra coordinate with coefficient diag(B,1), apply local three-dimensional solution Harnack, and restrict back.

Now w-d in H¹_0 and w=0 imply zero Sobolev trace of d on this ball. The original d is Lipschitz on a neighborhood of its closure. Its trace is its continuous restriction to the sphere. A continuous function zero surface-a.e. on a sphere is zero everywhere there (a nonzero value would persist on a relatively open set of positive surface measure). Therefore d vanishes on the entire sphere. Repeating for every r below a fixed local margin proves d=0 throughout a neighborhood of z0, not just on one boundary sphere.

For the original pair with v merely continuous, apply this reasoning to (u,v_L) around every contact. Section 3 recovers contact with v throughout that neighborhood. The original contact set is open, closed by continuity, nonempty, and contained in connected Omega. It is all of Omega. This proves the submitted contact theorem and SC_tau for the actual W,V.

## 6. Altered-tau source normalization, compactness and slices

The source frame is

    U(y,s)=[V(x0+R(y+p0 s),t0+Rs)-V(x0,t0)]/R
             -p0.y-(a0+|p0|²/2)s.

With B=[I,p0;0,1], its Hessian is R B^T D²V B, horizontal gradient D_xV-p0, and B(D_yU,1)=(D_xV,1). Also Delta_y U=R Delta_x V. Consequently G_tau[U]=R G_tau[V] at corresponding test jets. Tau is unchanged, and the source fit calculation gives (p,a)->(p-p0,a-a0) with the same C0. This is a viscosity test pullback, not just a smooth heuristic.

Source 04's fit comparisons use function values and give centered growth O(K(1+log K)²), local moduli and uniform subquadratic spatial tails. These inputs are unchanged. Only its PDE-identification step changes: use continuity of G_tau and strict test contacts to pass a locally uniform centered limit. At each fixed center and radius choose a subsequence of bounded fit coefficients; on the limiting closed box use h_j=p_j l+(h-p l). This proves every required fit, including its boundary, for the already fixed limit. The coefficient subsequence may depend on the center/radius. No common choice over uncountably many pairs is needed. A varying tau_j converging to a fixed positive tau would also work in this step; no tau-uniform theorem follows.

If C0=0, each fitted open box gives a local affine representation. Overlap and connectedness identify all gradients and intercepts.

If every horizontal slice is affine, write V=P(t).x+c(t). For each fixed t,l>0,R>=l, a radius-R fit centered at (x,t) has |p-P(t)|<=C0 by testing l=0. Testing that same fit at (pl,l) and (-pl,-l) gives the displayed second-difference expression (6.2) of I236. Its only unbounded-in-x term is [P(t+l)+P(t-l)-2P(t)].x; all others are bounded uniformly in x because p is. Therefore that coefficient vanishes. Continuity implies P(t)=bt+d. Centered growth at x=+/-K e, |t|<=K bounds |P(t)| by O(log²K), forcing b=0. A frame changes the intercept of P and translates/scales time but cannot remove a nonzero b. For constant P, the test P.x+psi(t) has G_tau=psi'', so c satisfies both viscosity inequalities for c''=0 and is affine.

Otherwise a nonaffine continuous slice has a nonzero midpoint defect. Reflection V(x,t)->-V(x,-t) makes it positive when necessary; direct test pullback changes G_tau to -G_tau and transforms fits by (p,a)->(-p,a). This uses both inequalities because V is a solution. All slice alternatives are covered.

## 7. Extremal defect, finite attainment, synchronized trace sum

Normalize each finite horizontal configuration by a fit at its barycenter with R equal to its root-mean-square radius. Its mean becomes zero, its second moment one, and the defect/radius is unchanged. Centered growth bounds its integral uniformly, proving 0<kappa<infinity. All configurations of every normalized function still obey the original kappa bound because this quotient is frame invariant.

For maximizing configurations, centered compactness fixes a limit Vhat. Tightness of their probability measures follows from the unit second moments. First-moment tails are <=1/M, preserving zero mean; second moments of the limit are <=1. For the value integrals, uniform subquadratic tails give

    int_{|y|>M}|V_j(y,0)| dmu_j
      <=sup_{j,|y|>M}|V_j(y,0)|/|y|² ->0.

Use compact cutoffs and weak convergence for the rest. Thus the limiting defect is exactly kappa. The finite-configuration Jensen bound passes to Vhat. The accepted barycentric duality lemma extends its envelope to finite-second-moment measures without changing the value, so mu is a valid competitor. At parameter 1/kappa it gives a gap >=kappa/2; the universal sandwich gives <=kappa/2. Equality also forces second moment one. Scaling with R=1/kappa and translating to time 1 sends an envelope parameter sigma to R sigma and divides its gap by R. Hence the new gap is kappa²/2 at (0,1), with the same fixed tau and kappa.

Finite attainment in source 05 is applicable: for g(y)=V(y,t)-|y|²/(2s), subquadratic tails force maxima of g-A.y to remain compact for bounded A, and its dual value is coercive in A. At a minimizing A, the barycenter is in the convex hull of maximizing positions. A finite convex combination (at most m+1 positions suffice) attains the envelope; zero weights are discarded. Thus no infinite family of jets is summed.

Here is the full altered common-time calculation. Fix positive weights, a C² upper test Phi of sum theta_i V(y_i,t), and strictify it with fourth powers. With independent times let tbar=N^(-1)sum t_i and chi(T)=sum(t_i-tbar)²/2. Maximize

    sum theta_i V(y_i,t_i)-Phi^sharp(Y,tbar)-lambda chi(T)

on a small closed product. Boundedness forces chi->0; strictness makes the maximizers converge to the original diagonal contact and eventually lie in the interior. For fixed lambda set A=D²(Phi^sharp(Y,tbar)+lambda chi) and q_i=theta_i^(-1)D_yi Phi^sharp at its maximum. The pinned theorem of sums gives actual closed superjets (D_i Psi,X_i) of theta_i V, with diag(X_i)<=A+eta A². Dividing by theta_i supplies a closed superjet of V with horizontal gradient q_i. Continuity of the operator justifies its viscosity inequality on the closed jet:

    X_i[(q_i,1)]+tau sum_k X_i[(e_k,0)]>=0.

The factors theta_i have cancelled; there is no remaining unequal time speed. Sum these inequalities. Test the matrix bound on zeta=((q_i,1))_i and separately on E_k=((e_k,0))_i, multiplying the latter inequalities by tau. The error is eta times the finite sum |A zeta|²+tau sum|A E_k|². First send eta to zero for fixed lambda. Then D²chi vanishes on zeta and all E_k, so the resulting inequality involves only D²Phi^sharp and bounded horizontal derivatives. Send lambda to infinity. The possibly unbounded individual time derivatives never enter G_tau. This produces precisely (6.5), without assuming differentiability of V.

For the upper test of W, finite attainment makes

    Phi(Y,t)=phi(sum theta_i y_i,t)+kappa²t/2
               +sum theta_i|y_i-sum theta_j y_j|²/(2t)

a genuine upper test of the weighted sum. Its q_i=p+(y_i-x)/t have weighted mean p. Along ((q_i),1) the variance term is affine, so its second variation is zero. Along each common spatial translation the offsets are constant and the mean translates by e_k; its variance again contributes zero. Equation (6.5) is therefore exactly G_tau[phi]>=0. This proves the actual W is a subsolution, and the geometric identity supplies its required spatial semiconcavity.

## 8. Global contradiction, drift, and scope

SC_tau gives W=V on the connected positive-time half-space. At any fixed t>0, subquadratic tails make V(y,t)-|y|²/(2t) tend to minus infinity. Let y* be a global maximizer. Integrate its supporting inequality over a finite configuration of mean y*. The identity sum theta_i|y_i-y*|²=sum theta_i|y_i|²-|y*|² gives C_tV(y*,t)<=V(y*,t); the singleton gives equality. But W=V requires C_tV-V=kappa²t/2>0 at every point. This is the contradiction, independent of uniqueness of the maximizer or any differentiability of V.

For constant drift b, set U(y,t)=V(y+bt,t). The drifted PDE pulls back to G_tau[U]=0. Its natural fit has |h-(p+b)l|<=R and time coefficient a-|p|²/2-b.p. Substitution gives ordinary FIT for U with the same p,a,C0. Thus affinity transfers back. It does not justify using an unchanged shear for the drifted equation.

The local constants may deteriorate with tau, the gradient range, and the neighborhood. No REG_tau, uniform finite-p gradient theorem, or tau-infinity estimate is obtained. The divided limiting equation Delta_x V=0 still admits sin t with FIT (p=a=0,C0=1). That fact does not contradict the finite-tau theorem. The accepted count remains nine; contribution is a separate gate.
