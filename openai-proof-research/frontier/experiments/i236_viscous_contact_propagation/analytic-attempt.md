# I236 — contact propagation for the actual viscous envelope

**Final research verdict: SC_tau is proved below, and the finite-positive-tau fitted-class affinity follows.** This is a mathematical candidate, not an independent proof/contribution gate or a count increment. All pinned OpenAI results and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. No REG_tau theorem for arbitrary fitted solutions is assumed or proved.

The early record identified horizontal cone infima and an unpaid comparison step. The completed argument pays that step differently: derive time Lipschitz continuity of the spatially semiconcave **subsolution**, make a local Lipschitz supersolution by a cone infimum, and then use the exponential divergence structure. Neither full space-time semiconcavity nor an unchecked nonlinear strong-comparison theorem is used.

## 1. Exact statements and conventions

Let m>=1, n=m+1, and 0<tau<infinity. For P=(p,q) in R^m x R set

    A_tau(p) = [[tau I+p p^T, p], [p^T, 1]],
    G_tau(P,X) = tr(A_tau(p) X).

The time derivative q does not enter G_tau. A continuous viscosity subsolution satisfies G_tau(Dphi,D²phi)>=0 at upper C² tests; a supersolution satisfies <=0 at lower tests. These conventions include every jet, including p=0.

**Contact theorem.** Suppose Omega is connected and open in R^m x R, u,v are continuous, u is a G_tau-subsolution, v is a G_tau-supersolution, and u<=v. Assume u has locally uniform spatial semiconcavity: on every sufficiently small product cylinder its slices satisfy D_xx u<=K I with a common finite K. If u(z0)=v(z0) at one interior point, then u=v throughout Omega.

The proof actually establishes the intermediate version with u locally Lipschitz in all variables, without requiring its spatial semiconcavity. Spatial semiconcavity plus the subsolution PDE supplies that Lipschitz property in Section 2. No Lipschitz hypothesis is imposed on v.

**SC_tau for I231.** Take exactly the extremal pair

    W(x,t)=C_t V(x,t)-kappa² t/2 <= V(x,t),  t>0,
    W(0,1)=V(0,1)=0,  kappa>0,

where V is the entire fitted G_tau-solution constructed in I231 and

    C_s V(x,t)=sup_{sum theta_i y_i=x}
       [sum theta_i V(y_i,t)-sum theta_i |y_i-x|²/(2s)].

Then W=V on R^m x (0,infinity). Indeed source 05's geometric envelope identity, with I231's checked trace-aware subsolution calculation, gives all hypotheses of the contact theorem. Section 6 spells out the construction and resulting contradiction.

**Finite-tau affinity.** For every m>=1, 0<tau<infinity and finite C0>=0, every V in C(R^m x R) solving G_tau=0 and satisfying the following exact quantifiers is affine: for every (x,t) and every R>0, there are p in R^m and a in R such that

    |V(x+h,t+l)-V(x,t)-p.h-(a-|p|²/2)l|<=C0 R
    whenever |l|<=R and |h-p l|<=R.                     (FIT)

No common gradient bound, differentiability, energy hypothesis, or uniformity as tau tends to zero/infinity is added.

## 2. The missing time estimate for the actual envelope

**Lemma 2.1.** A continuous G_tau-subsolution with locally uniform spatial semiconcavity is locally Lipschitz in all n variables.

Here is a local proof with all uniformity needed for the conclusion. Work inside a product cylinder with compact closure in the domain, and choose a smaller cylinder of base points (x0,t0). Choose r>0 so every closed B_r(x0) stays inside the larger spatial ball. Enlarge a spatial semiconcavity constant to K>=0. Continuity gives a common bound M and a common time modulus omega on the larger compact cylinder.

For every base point there is a spatial supergradient p such that

    u(y,t0)<=u(x0,t0)+p.(y-x0)+K|y-x0|²/2,   |y-x0|<=r.    (2.1)

This follows by taking a supporting hyperplane to the finite concave function u(.,t0)-K|.|²/2. Evaluating the supporting inequality at fixed opposite spatial increments bounds |p| by a common L. The same argument yields a common spatial Lipschitz bound on a smaller ball. These constants are uniform in t0 because M and K are uniform.

Put K'=K+1 and, with this p held fixed, define

    h(t)=max_{|y-x0|<=r}
       {u(y,t)-p.(y-x0)-K'|y-x0|²/2}.                  (2.2)

At t=t0 the unique maximizer is y=x0, h(t0)=u(x0,t0), and every boundary competitor is at most u(x0,t0)-r²/2. Choose s>0, uniformly for all base points, with omega(s)<r²/8 and with the whole time interval (t0-s,t0+s) inside the larger cylinder. For such t the boundary competitors are at most u(x0,t0)-3r²/8, whereas the central competitor is at least u(x0,t0)-r²/8. Hence all maximizers in (2.2) are interior. Also h is continuous and uniformly bounded in absolute value by

    H=M+Lr+K'r²/2.

If a scalar C² test psi touches h from above at t and y is an attaining maximizer, then

    phi(Y,T)=psi(T)+p.(Y-x0)+K'|Y-x0|²/2

(after the contact constant is adjusted) touches u from above at (y,t). Its mixed Hessian is zero. The actual subsolution inequality gives

    0<=psi''(t)+K'(|p+K'(y-x0)|²+tau m).

Consequently every upper test of h satisfies

    psi''>=-C,   C=K'[(L+K'r)²+tau m].                 (2.3)

The elementary one-dimensional viscosity characterization of convexity implies h(t)+Ct²/2 is convex. One may use C(t-t0)²/2 instead. For clarity, that characterization follows by contradiction from failure of the chord inequality: a line interpolating the endpoints, raised by a sufficiently small strictly concave quadratic and then by the smallest constant that dominates the function, has an interior upper contact with negative second derivative. This contradicts the nonnegative-second-derivative test condition.

Bounds for slopes of a bounded convex function between its endpoint chords now give a uniform Lipschitz bound for h on (t0-s/2,t0+s/2), for example 8H/s+4Cs. Since u(x0,t)<=h(t) and equality holds at t0,

    u(x0,t)-u(x0,t0)<=C1 |t-t0|,   |t-t0|<s/2.        (2.4)

Repeat the construction with base point (x0,t), using the same uniform constants, to obtain the reverse inequality. Thus u is uniformly Lipschitz in time on the smaller cylinder. Combining this with its spatial Lipschitz bound proves Lemma 2.1.

This proof does not infer time regularity from the slice property alone. It uses G_tau at the lifted upper test with **fixed bounded spatial Hessian and zero mixed Hessian**. It proves Lipschitz continuity, not space-time semiconcavity or C¹ regularity. It also works for tau=0 as a local subsolution observation, but the later strictly elliptic divergence argument requires tau>0.

For W, the source envelope identity says

    C_t V(x,t)=|x|²/(2t)+Conc[V(.,t)-|.|²/(2t)](x),

where Conc is the least concave majorant. Thus D_xx W<=I/t. On each compact positive-time cylinder, K=1/t_min works, and continuity provides M and omega. Lemma 2.1 applies exactly to W.

## 3. A local Lipschitz supersolution preserving contact

Suppose u is locally Lipschitz, u<=v, and u(z0)=v(z0). Choose a Euclidean ball around z0 whose larger concentric ball is compactly contained in Omega; all z+h used below lie in that larger ball. Let L0 be a Lipschitz constant of u there, fix L>L0 and a small r>0, and set

    v_L(z)=min_{|h|<=r} {v(z+h)+L|h|}.                 (3.1)

The minimum is attained and v_L is continuous locally. Every competitor satisfies

    v(z+h)+L|h| >= u(z+h)+L|h|
                       >=u(z)+(L-L0)|h|.             (3.2)

Therefore u<=v_L<=v, and at z0 the only minimizer is h=0, with v_L(z0)=u(z0). For every minimizing h,

    (L-L0)|h|<=v(z)-u(z).                              (3.3)

Continuity and contact imply that, on a smaller neighborhood N of z0, every minimizer has |h|<r/2.

The function v_L is a viscosity supersolution. Indeed, at a lower test phi at z choose a minimizing h. Near z,

    phi(z')<=v_L(z')<=v(z'+h)+L|h|,

with equality at z. Translation of phi-L|h| is therefore a lower test for v at z+h, with the identical gradient and Hessian. Autonomy and independence of the function value give G_tau[phi]<=0. This argument does not differentiate the minimizer or the cone.

It is also L-Lipschitz on a still smaller convex N. If h minimizes at z and |z-z'|<r/2, the admissible shift h'=h+z-z' for z' gives

    v_L(z')<=v(z+h)+L|h+z-z'|<=v_L(z)+L|z-z'|.

Reverse the roles of z,z'. Thus u and v_L are both locally Lipschitz sub/supersolutions on N. Finally,

    v_L(z)=u(z)  ==>  h=0 by (3.2)  ==>  v(z)=u(z).   (3.4)

Consequently equality propagated for the reduced pair transfers back to the original v. It is not sufficient merely to note v_L<=v; (3.2) is the essential recovery step.

## 4. The exponential flux and the viscosity-to-weak passage

Define the smooth flux on the full gradient space by

    H(p,q)=q+|p|²/2,
    a(p,q)=exp(H(p,q)/tau)(p,1).

Direct differentiation gives

    Da(P)=exp(H(P)/tau) A_tau(p)/tau,                  (4.1)
    div a(Df)=exp(H(Df)/tau) G_tau[ f ]/tau            (4.2)

for C² f. In particular Da is symmetric positive definite. For |P|<=M one possible pair of bounds is

    lambda0=1/max(2,(1+2M²)/tau),
    Lambda0=M²+1+tau,
    lambda_M=exp(-M/tau) lambda0/tau,
    Lambda_M=exp((M+M²/2)/tau) Lambda0/tau,
    lambda_M I<=Da(P)<=Lambda_M I.                    (4.3)

Indeed A_tau(p)[(xi,s)]=(p.xi+s)²+tau|xi|². The lower bound follows from s²<=2(s+p.xi)²+2M²|xi|²; the upper bound follows by writing A as (p,1)(p,1)^T+diag(tau I,0).

**Lemma 4.1.** If f is locally Lipschitz and a viscosity G_tau-subsolution, then div a(Df)>=0 in distributions. For a locally Lipschitz supersolution, div a(Df)<=0.

We give the proof rather than assert that continuous viscosity solutions are finite-energy minimizers. Work with a fixed compact test support inside a bounded open set where f is M-Lipschitz, using a further compact margin. For small epsilon take the ordinary full-space-variable sup convolution

    f^epsilon(z)=sup_y {f(y)-|z-y|²/(2epsilon)}.

The optimizing y stay within 2M epsilon of z. On the compact region in question this function is M-Lipschitz, semiconvex with D² f^epsilon>=-I/epsilon in distributions, and converges uniformly to f. It is an exact G_tau-subsolution: an upper test pulled to an attaining translate of f has the same first and second derivatives. This is the same fixed-shift argument as Section 3, now for a supremum. It uses no convexity of G in the gradient.

At almost every Alexandrov twice-differentiability point, the viscosity inequality yields

    tr(Da(Df^epsilon) D² f^epsilon)>=0.                (4.4)

For example, add delta|z-z_*|² to the second-order Taylor polynomial to obtain an upper test on a small neighborhood, then let delta decrease to zero. The positive factor in (4.1) preserves the sign.

Mollify f^epsilon on a smaller region, writing f^epsilon_j. Then |Df^epsilon_j|<=M and D² f^epsilon_j>=-I/epsilon. Thus

    div a(Df^epsilon_j)>=-n Lambda_M/epsilon.          (4.5)

For fixed epsilon this is an integrable lower bound independent of j. Moreover Df^epsilon_j->Df^epsilon and D²f^epsilon_j->D²f^epsilon almost everywhere. The second assertion is the standard mollification fact for a semiconvex function: its distributional Hessian is a locally finite matrix measure, its absolutely continuous part has the Alexandrov Hessian as density, and the mollifications of the singular part tend to zero at almost every Lebesgue point. This is exactly the fact identified in Julin–Juutinen, Remark 3.3; semiconvexity is obtained from their semiconcave version by negation.

For nonnegative phi in C_c^infinity, integration by parts, bounded-gradient convergence and Fatou applied using (4.5) give

    -int a(Df^epsilon).Dphi
      =lim_j int phi div a(Df^epsilon_j)
      >=int phi tr(Da(Df^epsilon)D²f^epsilon)>=0.       (4.6)

This also shows that the last nonnegative density is locally integrable. Singular convex curvature has the favorable sign; it has not been discarded by writing only an almost-everywhere PDE.

We must still pass epsilon to zero in the nonlinear flux. This is particularly simple because f was proved Lipschitz beforehand. At a differentiability point z of f, for any maximizing y=z+epsilon b_epsilon, |b_epsilon|<=2M. Taylor expansion at z is uniform over these bounded b. Comparison with y=z+epsilon Df(z) gives

    |b_epsilon-Df(z)|²/2=o(1).

At a differentiability point of f^epsilon its gradient equals b_epsilon (all attaining translates give that same gradient). Along any fixed sequence epsilon_j decreasing to zero, discard the null sets of nondifferentiability of f and all f^epsilon_j. Then Df^epsilon_j->Df almost everywhere and the gradients are uniformly bounded. Consequently a(Df^epsilon_j)->a(Df) in L¹ on the compact support, by dominated convergence. Letting epsilon_j decrease in (4.6) proves div a(Df)>=0.

For supersolutions use inf convolution. It is semiconcave with D²f_epsilon<=I/epsilon and remains a supersolution. Its smooth mollifications have div a(Df_epsilon,j)<=n Lambda_M/epsilon. Apply the preceding Fatou argument to the negative divergence. At differentiability points, comparison of minimizers with y=z-epsilon Df(z) proves Df_epsilon->Df. The result is div a(Df)<=0. This is not obtained by claiming that -f solves the same nonlinear equation.

This proof adapts the autonomous convolution and one-sided Fatou argument of Julin–Juutinen, Section 3, to the **explicit smooth monotone flux (4.1)**. Their p-Laplace theorem is not being substituted for this equation. Full bounded gradients supply both the bounded flux and the lower/upper bounds needed for Fatou; no exponential-energy integrability of an arbitrary continuous V is assumed.

## 5. Linear divergence contact propagation and SC_tau

First consider any locally Lipschitz pair u<=v of G_tau sub/supersolutions on a connected open set. Locally |Du|,|Dv|<=M almost everywhere. Put d=v-u>=0 and

    B(z)=int_0^1 Da(Du(z)+s(Dv(z)-Du(z))) ds.           (5.1)

This is a measurable symmetric matrix, with lambda_M I<=B<=Lambda_M I. The fundamental theorem of calculus on the gradient segment gives

    a(Dv)-a(Du)=B Dd

almost everywhere. Lemma 4.1 therefore gives

    div(B Dd)<=0,
    int B Dd.Dphi>=0 for every nonnegative phi in C_c^infinity. (5.2)

Thus d is a continuous nonnegative weak supersolution of a **linear divergence** equation with bounded uniformly elliptic measurable coefficients. It is not an asserted viscosity Pucci inequality with an unpaid drift.

Here is a precise reduction of its strong minimum principle to the standard Harnack theorem for weak **solutions**, so no mismatch of subsolution hypotheses is concealed. Suppose d(z0)=0, and choose any ball B_r(z0) compactly contained in the region with the displayed ellipticity constants. By the coercive bilinear form int B Dw.Dphi and Lax–Milgram there exists a unique w in H¹(B_r) such that w-d belongs to H¹_0(B_r) and

    int B Dw.Dphi=0,   phi in H¹_0(B_r).

The negative-part test gives w>=0, because d has nonnegative boundary trace. The test (w-d)^+ in the difference of this equation and (5.2) gives

    int B D(w-d)^+.D(w-d)^+<=0,

so 0<=w<=d almost everywhere. In particular w is locally bounded. The classical interior Hölder and Harnack conclusions for weak solutions with bounded measurable symmetric uniformly elliptic coefficients give a continuous representative of w, and w(z0)=0. Harnack on interior cubes, followed by an overlapping chain, gives w=0 throughout B_r. These are the exact solution hypotheses in Crescimbeni–Forzani–Perini, Sections 2–3, equations (2.1), (2.2), (2.5), and Theorems 3.1–3.2.

Since w-d belongs to H¹_0 and w=0, d has zero boundary trace on this ball. The original d is Lipschitz on a neighborhood of its closure, so its trace is its continuous restriction; hence d=0 on the entire sphere. The radius r was arbitrary below the distance to the local boundary. Every point in the smaller neighborhood lies on such a sphere about z0. Therefore d=0 near z0. This proves the strong minimum principle here using only linear weak-solution Harnack, Sobolev traces and the displayed elementary energy comparisons.

Now return to u locally Lipschitz and v merely continuous. At every point of their contact set apply Section 3 to obtain v_L. The preceding argument gives v_L=u on a neighborhood. Equation (3.4) then gives v=u on that neighborhood. Thus the original contact set is open; continuity makes it closed. It is nonempty, and Omega is connected, so it is all of Omega. Finally apply Lemma 2.1 to the spatially semiconcave subsolution u to prove the contact theorem of Section 1.

For the actual I231 pair, Omega=R^m x (0,infinity) is connected, W is the semiconcave subsolution, V is the continuous supersolution, and the original contact is (0,1). This proves **SC_tau** with exactly its actual hypotheses.

## 6. Complete implication to finite-tau fitted-class affinity

We spell out all slice alternatives and the inputs reused from I231. Let V satisfy (FIT) and G_tau=0.

### 6.1 Zero fit constant and affine slices

If C0=0, each fitted open box agrees exactly with an affine function. Overlapping open boxes identify their slopes, and connectedness gives a globally affine V without a PDE.

Suppose C0>0, enlarging it to max(C0,1) for geometric estimates when useful. Normalize a radius-one fit by source 04's shear/scale

    U(y,s)=[V(x0+R(y+p0s),t0+Rs)-V(x0,t0)]/R
             -p0.y-(a0+|p0|²/2)s.                    (6.1)

Its Hessian and horizontal gradient give G_tau[U]=R G_tau[V], since D_yy U=R D_xx V. Tau is unchanged. Fits become (p-p0,a-a0) with the same C0. Source 04's equation-free comparisons then give centered growth C K(1+log K)² and compactness; the only PDE limit step uses continuity of G_tau on finite jets. In particular the spatial tails are uniformly subquadratic on compact time intervals.

If **every** horizontal slice is affine, write V(x,t)=P(t).x+c(t), with P,c continuous by evaluations at 0 and the coordinate vectors. A fit at (x,t) of radius R gives |p-P(t)|<=C0 by using l=0. For l>0 take R>=l and evaluate that same fit at (h,l)=(p l,l) and (-p l,-l). Adding cancels its affine increments and yields

    |[P(t+l)+P(t-l)-2P(t)].x
       +l p.[P(t+l)-P(t-l)]
       +c(t+l)+c(t-l)-2c(t)|<=2 C0 R.                 (6.2)

For fixed t,l,R, |p|<=|P(t)|+C0 uniformly as x varies. All terms other than the displayed coefficient of x remain bounded. Sending x to infinity in any direction forces P(t+l)+P(t-l)=2P(t). Continuity implies P(t)=b t+d. For a centered version of V, the growth bound at x=+/-K e and |t|<=K gives |P(t)|<=C(1+log K)². Therefore b=0. For constant P, tests P.x+psi(t) reduce the actual PDE to psi''=0 for c, so c is affine. Thus this alternative is fully rigid without the envelope-contact argument.

Otherwise there is a nonaffine horizontal slice. Its continuous function has a nonzero midpoint defect. The transformation V(x,t)->-V(x,-t) preserves both the equation and FIT (p,a)->(-p,a), and reverses that defect. We may choose it positive.

### 6.2 The extremal configuration and changed-PDE inputs

Let kappa be the supremum over all times and finite positive-weight probability configurations of

    [sum theta_i V(y_i,t)-V(sum theta_i y_i,t)]/r,
    r²=sum theta_i|y_i-sum theta_j y_j|²>0.

It is positive. It is finite: normalize a radius-r fit at the barycenter using (6.1). The normalized configuration has mean zero and second moment one. The centered growth bound is at most C(1+|y|²); integrating it bounds the normalized defect uniformly. The quotient and tau are invariant under (6.1).

Normalize configurations approaching kappa to mean zero and second moment one. The corresponding centered solutions have a locally uniform limit Vhat, still solving G_tau=0 with the exact all-center/all-radius fits. Their probability measures have a weakly converging subsequence mu, with mean zero and second moment <=1. Uniform subquadratic tails make the varying value integrals uniformly integrable. Therefore

    int Vhat(y,0)dmu-Vhat(0,0)=kappa.

For every function in this closure, the Jensen bound gives

    0<=C_s V-V<=sup_r[kappa r-r²/(2s)]=kappa²s/2.       (6.3)

The admissible measure mu in C_(1/kappa) gives the reverse equality kappa/2 at the origin; it also forces its second moment to equal one. The source geometric envelope lemma allows such measures and gives finite attainment. A radius-1/kappa frame and time translation as in I231 put the equality at parameter 1 and time 1. Rename the resulting solution V. Then

    W=C_t V-kappa²t/2,
    V-kappa²t/2<=W<=V,
    W(0,1)=V(0,1)=0,
    C_1 V(0,1)-V(0,1)=kappa²/2>0.                    (6.4)

The source's finite-Hamiltonian-slope conclusion is NOT used. Its original proof of the affine-slice alternative is replaced by (6.2), and its original homogeneous subsolution input is replaced by the following explicit trace check from I231.

In the synchronized-time theorem of sums for sum theta_i V(y_i,t), add to the usual common-time vector ((q_i,1)) the m common spatial translation vectors ((e_k,0)). The individual viscous inequalities, multiplied back by theta_i after dividing the jets, add up to

    D²Phi[((q_i)_i,1)]
          +tau sum_k D²Phi[((e_k)_i,0)]>=0.            (6.5)

The time-synchronization penalty has zero second variation on all these vectors. At an upper test phi of W use an attaining configuration and

    Phi(Y,t)=phi(sum theta_i y_i,t)+kappa²t/2
           +sum theta_i|y_i-sum theta_j y_j|²/(2t).

Here q_i=D_x phi+(y_i-x)/t. Along ((q_i),1), the centered offsets scale by 1+h/t, so the variance divided by 2(t+h) is affine in h. Along common spatial translations the variance is constant. Thus (6.5) is exactly G_tau[phi]>=0. This proves the actual W is a subsolution. The source geometric identity gives spatial semiconcavity D_xx W<=I/t. Consequently the now-proved SC_tau applies to (6.4), yielding W=V on the entire positive-time half-space.

### 6.3 The final contradiction

Fix t>0. Subquadratic spatial growth implies that y->V(y,t)-|y|²/(2t) attains a global maximum at some y*. For every finite configuration of mean y*, the maximum inequality implies

    sum theta_i V(y_i,t)-sum theta_i|y_i-y*|²/(2t)
        <=V(y*,t).

The cancellation uses sum theta_i|y_i-y*|²=sum theta_i|y_i|²-|y*|². The singleton configuration gives equality, so C_t V(y*,t)=V(y*,t). But W=V requires C_t V-V=kappa²t/2>0 at every point. Contradiction. Thus the nonaffine-slice alternative is impossible, completing the finite-tau affinity theorem.

A constant drift b is covered with exactly the natural fitted shear: for D²V[(D_xV+b,1)]+tau Delta_x V=0, assume FIT with |h-(p+b)l|<=R and affine time coefficient a-|p|²/2-b.p. Then U(y,t)=V(y+bt,t) satisfies the zero-drift theorem with unchanged C0. Hence V is affine. Constants in local Euclidean estimates may depend on b; there is no uniform tau-limit estimate here. The tau=infinity PDE-only counterexample V=sin t from I231 remains valid and is not contradicted.

## 7. Failed shortcuts and admissible checks

The direct viscosity/Pucci attempt is not the proof. Even bounded horizontal gradients do not imply a Hessian-independent estimate for the variation of G_tau in p. This failure occurs on actual smooth solution jets: take m=1, N>0, solve

    p_N(x)^3/3+tau p_N(x)=N x+1/3+tau,
    f_N'=p_N,   V_N(x,t)=f_N(x)-N t²/2.

The strictly increasing cubic defines a smooth entire p_N. Since (p_N²+tau)p_N'=N, V_N solves G_tau=0 classically. At (0,0), p_N=1 and X=diag(N/(1+tau),-N). Replacing p=1 by 1+delta changes G by N(2delta+delta²)/(1+tau). Thus no bound C(M)|delta| independent of X holds even for solution jets with bounded gradient at the contact (and on a sufficiently small neighborhood). These V_N are not claimed to satisfy global FIT. They refute the local operator shortcut, not the affinity theorem.

Nor does ordinary spatial smoothing preserve the needed subsolution inequality. Take instead the smooth p defined by p³/3+tau p=x, so p is odd, f'=p, and V=f(x)-t²/2 is an exact smooth solution. For any nontrivial even smooth probability mollifier eta with compact support, at x=0

    D_x(V*_x eta)=0,
    G_tau[V*_x eta](0,t)
      =tau int [1/(p(y)²+tau)] eta(y)dy-1<0.

The convolution therefore fails the subsolution inequality. This is a genuine local smooth PDE example, not just a matrix pattern; its slices have bounded semiconcavity on compact sets. In Section 4 it is the **sup/inf convolution** that preserves the PDE. Subsequent linear mollification is used only with the one-sided Hessian bound and Fatou, not claimed to preserve G_tau.

Finally slice semiconcavity alone cannot yield the time estimate. The exact-fit example f(t)=t log|t|, f(0)=0, independent of x, has C_s f=f, spatial Hessian zero and is not Lipschitz at t=0. It has FIT with C0=7: when |t0|<=2R use p=0, a=log R and scale t0=Rs, l=Ru to bound the remainder by 6 log(3)R; when |t0|>2R use a=f'(t0) and |f''|<=1/(|t0|-R) to bound it by R/2. It is not a G_tau-subsolution across the relevant neighborhoods. Lemma 2.1 uses precisely the missing PDE input.

## 8. Scope and contribution limits

The result pays SC_tau for the actual I231 contact pair and proves finite-tau fitted-class affinity. It does not prove REG_tau for arbitrary fitted solutions, any tau-uniform estimate, any p-harmonic gradient convergence theorem, or an accepted tenth finding. No I234 or other live output was read. The substantial new-to-project bridge is the combination of the envelope-specific time estimate, contact-preserving cone infimum, and fully checked viscosity-to-divergence passage. The convolution/Fatou mechanism and linear Harnack theorem are established methods, and the exponential operator already occurs in primary literature. No worldwide novelty claim follows.
