# Exact local entropy balance for the Source363 pair

This author proof addresses exactly FROZEN.md, SHA256 `1e4dbb6345bf6f0c61bb589b394e6454f382f329f87eddbd3a91b1e18ce2f212`. It uses the truth of both pinned Source363 papers and all their operative proofs as instructed. It does not audit or reprove their nonuniqueness. No mathematical grade, acceptance or count is assigned.

All integrals below use Lebesgue measure in velocity and volume-one periodic spatial measure. The sphere has ordinary surface area. The notation, kernel, priming convention and Maxwellian M are exactly those in the frozen statement. Write <v>=(1+|v|²)^(1/2), log^+z=max(log z,0), and log^-z=max(-log z,0). Products z log z and z|log z| at z=0 are defined to be zero. Constants may depend on the single fixed source construction, the indicated finite time horizon, and the indicated moment order. No uniformity over source parameter choices is claimed.

## 1. Source inputs and the unchanged pair

Use the October 5 construction, including its global continuation, compactness and final separation. Let F^(1) be its dormant global limit and F^(2) one of its cap global limits that the final separation argument proves distinct from F^(1). These have one and the same F_0, not merely a sequence of approaching data. Both retain the exact local conservation identities and entropy admissibility of def:admissible. The source proves positive space-time-velocity measure separation after continuation and passage to the limits. We do not change these solutions, their data, their parameters, or their limiting sequences.

The source rotates space and velocity together and works on R³/Lambda, where Lambda is the correspondingly rotated unit lattice. In these intermediate coordinates the jet axis is e_3. This rotation is an isometry, preserves spatial covolume, the hard-sphere kernel and ordinary sphere area, polynomial radial weights, and the radial M. Thus it suffices to prove the additional assertions in these coordinates and rotate back. Here bar v=(v_1,v_2) denotes the transverse projection in these coordinates.

Fix a finite horizon tau>0. The following are operative October inputs, with exact labels identifying their proofs.

* The datum and finite colored systems are given in Section 4. The geometric scales are s_j=s_0 exp(-j eta), j>=1, with fixed 0<s_0<1 and eta>0. The transverse widths are d_s=d_0 s^10 with fixed d_0 small. Each cold color is active up to L_s=s^(-1/2), then transferred to the bath/hot component without changing the total density.
* cold:geometry gives disjointness of all active enlarged tubes. Let A_s(t) be the union of their scale-s periodic representatives, as in Section 8; it is empty for t>L_s. Different A_s(t) are disjoint at each t. On [0,tau], |A_s(t)|<=C_tau s². At a point in A_s(t) there is at most one main active color. The other colors are covered by cold:nonmain.
* cold:upper and cold:barrier bound each active color by U_i=f_i+epsilon_s m_i, with epsilon_s=C_*L_s d_s/s. The center U of m_i satisfies |U|<=1+alpha<2. Its velocity factor is Gaussian with width comparable to d_s and coefficient at most C s^(-1)d_s^(-3). The factor exp(t/L_s) is at most e during activity. The free core is bounded by the same barrier. cold:nonmain bounds the total of all nonmain U_i by theta_0(s_0)exp(-4|v|²), including all periodic copies.
* cold:core-amplitude proves that the free-core velocity measure at fixed (t,x) is the pushforward of

      [K S(gamma(z_c-t p_3)/s)/(s+t alpha gamma S(gamma(z_c-t p_3)/s))] J(w) dw,
      bar p=d_s bar w,  p_3=a_s^sigma(z_c-t p_3)+d_s w_3,

  with spatial masks bounded by one. The coefficient is <=C/(t+s). Here J is fixed, bounded, smooth and supported in the unit ball; a product Gaussian also dominates J. Differentiation of the implicit axial equation gives dp_3/dw_3=d_s/[1+t(a_s^sigma)'(z_c-t p_3)], and monotonicity gives |p_3-U|<=d_s|w_3|. The barrier remainder epsilon_s m_i has mass <=C L_s d_s/s²=C d_0 s^(15/2), Gaussian width comparable to d_s and bounded center. In particular its mass is <=C/(t+s) while active.
* The early bath/cap estimates and global continuation in Sections 6–7 give a common upper bound C_tau H(v) for the non-cold part of every finite evolution, including all retired colors. Here

      H(v)=exp(-|v|²)<v>^(-100)(1+|bar v|^(-q)),  1<q<2,

  with fixed q. Thus H has all polynomial moments, as does H times log^+(1/|bar v|).
* Proposition prop:global-limits and comp:moment-envelope give, for every k>=0,

      R_k(t,x):=integral <v>^k F(t,x,v) dv <= C_tau,k a(t,x),
      a(t,x)=1+sum_s 1_A_s(t)(x)/(t+s).                         (1.1)

  The source proves uniform integrability of all polynomially weighted pair products and Q^+,Q^-, identifies their nonlinear limits, and supplies every-time weak convergence and the strong mild formula comp:path-formula. In particular F is continuous into every weighted L1 space and Q^++Q^- has every polynomial weight in space-time L1 on [0,tau]. Its entropy inequality comp:limit-entropy gives integral_0^tau D(F)<infinity.

These inputs apply separately to either of the two fixed limits. In the rest of the proof F denotes either one. We prove an additional property of those existing limits; we do not take a further compactness limit of solutions or dissipations.

## 2. Logarithmic envelopes inherited by the limits

Put

  ell(v)=log^+(1/|bar v|),  e_s=1+|log s|,
  b(t,x)=1+sum_s 1_A_s(t)(x)e_s/(t+s),
  c(t,x)=1+sum_s 1_A_s(t)(x)e_s.                              (2.1)

The values on the velocity axis, a null set, do not matter. Disjointness implies b<=c a pointwise.

First, a main cold upper bound satisfies

  U_i(t,x,v)<=C s^(-31) exp(-4|v|²).                         (2.2)

For the Gaussian barrier, use t<=L_s, bounded U, and d_s sufficiently small. The elementary completion of squares

  -|v-Ue_3|²/d²+4|v|²
    =-(d^(-2)-4)|v-Ue_3/(1-4d²)|²+4U²/(1-4d²)

has a uniformly bounded last term for d<=1/4 and |U|<=2. The coefficient s^(-1)d_s^(-3) is C s^(-31). The factor epsilon_s is bounded. The compactly supported free-core J gives the same bound, or one may use f_i<=m_i. All other colors and the non-cold part are bounded by C_tau H. Hence at every time, almost everywhere,

  log^+F(t,x,v)<=C_tau c(t,x)+q ell(v).                      (2.3)

Indeed off the active tubes F<=C_tau H. On A_s the additional term in (2.2) has logarithm at most C+31|log s|. Also log(1+|bar v|^(-q))<=log 2+q ell(v). Constants absorb bounded scalar factors. The polynomial and Gaussian factors of H cannot increase this upper logarithm.

Second, for each k>=0,

  J_k(t,x):=integral <v>^k F(t,x,v)ell(v)dv
       <=C_tau,k b(t,x).                                    (2.4)

Here the exact transverse variable in the source core formula matters. Since bar p=d_s bar w and d_s<1,

  ell(p)<=|log d_s|+log^+(1/|bar w|),
  <p>^k<=C_k<w>^k.

The second inequality uses |p_3-U|<=d_s|w_3| and bounded U. The integral of <w>^k[1+log^+(1/|bar w|)] against the fixed Gaussian dominating J is finite: the transverse integral near zero is a constant times integral_0^1 r|log r|dr. The core contribution is therefore at most C_k(1+|log d_s|)/(t+s). Since 1+|log d_s|<=C e_s, it has the required bound. The remainder has Gaussian width comparable to d_s, bounded axial center, and mass <=C s^(15/2); applying the same change of variables bounds its logarithmic moment by C_k e_s s^(15/2)<=C_k e_s/(t+s). No lower bound on the axial compression Jacobian was used. The H part has the required logarithmic moment because integral_0^1 r^(1-q)|log r|dr is finite for the fixed q<2. The nonmain Gaussian part does as well. This proves (2.4) for every finite colored approximation.

For clarity, these bounds persist at EVERY time of the selected limit, not only almost every time. The source extracts every-time weak L1 convergence. The actual deterministic upper bound C_tau H+sum of the main U_i is integrable in (x,v) at each time, by the source core-amplitude and tube-volume estimates. Testing with nonnegative bounded functions transfers this upper bound to F(t). This proves (2.3) by the preceding deterministic bound. For (1.1) and (2.4), truncate the nonnegative velocity test functions, multiply by any nonnegative bounded spatial test, pass through every-time weak convergence, and use monotone convergence. This yields the pointwise spatial moment inequalities for each t. This argument does not require the looser s^(-31) Gaussian bound itself to be integrable over all scales.

The key space-time integrability is

  integral_0^tau integral_T³ c(t,x)a(t,x)² dx dt < infinity.  (2.5)

Off the active tubes the integrand is one. On A_s it is bounded by C e_s[1+(t+s)^(-2)]. Thus, using |A_s(t)|<=C_tau s²,

  integral_0^tau integral c a²
    <=C_tau[1+sum_s e_s s²(tau+integral_0^tau (t+s)^(-2)dt)]
    <=C_tau[1+sum_s e_s(s²+s)]<infinity.                   (2.6)

This is an actual logarithmic summability calculation, not an inference from unweighted collision integrability. For J>=1 and rho=exp(-eta), the exact geometric sum is

  sum_(j>=J) s_j e_(s_j)
    =s_J[(1+|log s_J|)/(1-rho)+eta rho/(1-rho)²].           (2.7)

In particular the contribution of all s<epsilon is at most C epsilon(1+|log epsilon|), for 0<epsilon<=s_0. Constants here depend on the fixed mesh eta, not uniformly on arbitrary data.

## 3. A uniform outgoing-sphere logarithm estimate

For c_0 in R³ and r>0, ordinary surface area satisfies

  (1/(4 pi)) integral_S² ell(c_0+r sigma) d sigma
       <=1+log^+(1/r).                                    (3.1)

To prove it, let sigma be uniform on S². For 0<epsilon<=1,

  P(|bar c_0/r+bar sigma|<epsilon)
     <=P(|(c_0)_1/r+sigma_1|<epsilon)<=epsilon,

because sigma_1 is uniform on [-1,1]. Layer cake gives E log^+(1/|bar c_0/r+bar sigma|)<=integral_0^infinity exp(-u)du=1. Finally log^+(1/(r z))<=log^+(1/r)+log^+(1/z). This includes spheres tangent to the axis, centers on or off the axis, and arbitrarily small r; there is no excluded collision-angle regime.

In the source normalization, the one-child output law from input p,xi is

  integral_S² |(p-xi)·omega| phi(p-[(p-xi)·omega]omega)d omega
    =(|p-xi|/2) integral_S² phi((p+xi)/2+(|p-xi|/2)sigma)d sigma.  (3.2)

This is the source outgoing-sphere identity. One can also check its coefficient directly: align p-xi with e_3, write omega in polar coordinates, and put sigma=e_3-2(e_3·omega)omega. On each of the two hemispheres the surface Jacobian is 4|e_3·omega|; the two preimages give the factor |p-xi|/2. The total one-child rate is consequently 2 pi|p-xi|, exactly the source loss frequency normalization. At p=xi both sides are zero. Nonnegative measurable test functions follow by monotone approximation, including ell.

Apply the collision involution to the gain and then (3.1)–(3.2). With R_k as in (1.1), Tonelli gives

  integral_R³ Q^+(F,F)(v)ell(v)dv
    <=2 pi integral F(p)F(xi)|p-xi|[1+log^+(2/|p-xi|)]dp dxi
    <=C R_0 R_1.                                          (3.3)

The last step uses z log^+(2/z)<=2/e and |p-xi|<=|p|+|xi|, with R_0<=R_1. Thus the possible logarithm at a degenerate output sphere is suppressed by the exact collision rate. The same change of variables with phi=1 gives

  integral Q^+dv=integral Q^-dv<=C R_0 R_1.                (3.4)

No angular normalization, kernel cutoff, velocity restriction or independent-packet assumption has been introduced.

## 4. Absolute integrability of both collision terms against log F

All integrals in this section include 0<t<tau and x in the torus unless a velocity integral alone is displayed. The hard-sphere frequency is

  nu_F(v)=2 pi integral |v-p|F(p)dp<=C<v>R_1,
  Q^-=F nu_F.                                             (4.1)

From (2.3), (2.4), and b<=c a,

  integral Q^- log^+F dv
    <=C R_1(c R_1+J_1)<=C c a².                           (4.2)

From (2.3), (3.3) and (3.4),

  integral Q^+ log^+F dv<=C c R_0 R_1<=C c a².             (4.3)

Both right sides are integrable by (2.5).

For negative loss logarithms use the elementary inequality, valid for z>=0 and w>=1,

  z log^-z<=w z+C exp(-w/2).                              (4.4)

If z>=exp(-w), the first term suffices. Otherwise write z=exp(-u), u>w, and use u exp(-u)<=C exp(-w/2). At z=0 use the zero convention. Taking w=<v>² and using (4.1) gives

  integral Q^- log^-F dv<=C R_1(R_3+1)<=C(a²+a).            (4.5)

Consequently the loss is absolutely integrable against |log F|.

It remains to control the gain at small values of F; no pointwise lower Maxwellian is available or needed. On collision space put

  A=F(v')F(v_*'),  B=F(v)F(v_*),
  dmu=|(v-v_*)·omega|dt dx dv dv_* d omega.

The source entropy inequality gives integral Phi(A,B)dmu<infinity. Also integral(A+B)dmu<infinity by (3.4), (1.1), (2.5). This is a statement about the fixed solution F, not a claimed convergence of approximate entropy productions.

The already established loss-log estimate gives

  integral B[|log F(v)|+|log F(v_*)|]dmu<infinity.          (4.6)

The involution (v,v_*)<->(v',v_*') preserves dmu. It follows that

  integral A|log A|dmu
    <=integral A[|log F(v')|+|log F(v_*')|]dmu<infinity.    (4.7)

At A=0 the weighted expressions in this formula are defined to be zero. For A,B>0,

  A|log(A/B)|<=2 Phi(A,B)+(log 2)(A+B).                   (4.8)

For A/B>=2, A-B>=A/2; for A/B<=1/2, B-A>=A. For 1/2<A/B<2 use |log(A/B)|<=log 2. These three cases prove (4.8). Combining it with (4.7) yields

  integral A|log B|dmu<infinity,                           (4.9)

on the positive quadrant.

The zero sets are harmless for a proved reason. Finiteness of the nonnegative extended Phi implies that A=B=0 almost everywhere on {AB=0} in collision measure. In particular

  integral 1_{F(v)=0} A dmu=0.

By Tonelli, Q^+(F,F)=0 almost everywhere on the phase-space-time zero set of F. The loss also vanishes there by (4.1); R_1 is finite almost everywhere by (1.1). Expressions involving A and logarithms in (4.7)–(4.9) are assigned zero where A=B=0. Null collision sets with only one of A,B zero do not contribute.

Where A,B>0,

  log^-F(v)<=|log B|+log^+F(v_*).

Multiplication by A, integration, (4.9), and the already proved positive gain-log estimate (4.3), with v and v_* exchanged, give

  integral Q^+(F,F)log^-F<infinity.                        (4.10)

Together (4.2), (4.3), (4.5), and (4.10) prove

  integral_0^tau integral_Omega (Q^++Q^-)|log F|<infinity, (4.11)

with the required zero-set convention justified rather than imposed to hide a divergence. Since |log M(v)|<=C<v>² and the source gives all polynomial gain/loss moments, we also have

  integral (Q^++Q^-)[1+|log(F/M)|]<infinity,               (4.12)

using the same zero-set convention for its logarithmic part.

## 5. Weighted entropy continuity at every time

For z>=0, the relative entropy density eta_M(z,v) is continuous in z, nonnegative, and obeys

  eta_M(z,v)<=z log^+z+C<v>²z+M(v).                        (5.1)

For any k>=0, (2.3)–(2.4) therefore give

  integral <v>^k eta_M(F(t,x,v),v)dv
     <=C_tau,k[c(t,x)R_k(t,x)+J_k(t,x)+R_(k+2)(t,x)+1].    (5.2)

Let U_epsilon(t)=union_(s<epsilon) A_s(t). The sets are disjoint, and on A_s the right side of (5.2) is at most C_tau,k e_s[1+(t+s)^(-1)]. Hence, uniformly for EVERY t in [0,tau],

  integral_(U_epsilon(t)×R³) <v>^k eta_M(F(t),v)dx dv
    <=C_tau,k sum_(s<epsilon) e_s(s²+s)
    <=C_tau,k epsilon(1+|log epsilon|).                    (5.3)

For the complement of U_epsilon(t), only finitely many scales can be main. The deterministic bound (2.2) and the common H bound give an upper bound

  F(t,x,v)<=G_epsilon(v)
     :=C_tau,epsilon[H(v)+exp(-4|v|²)]                    (5.4)

there, uniformly in t and x. There is no claim that this bound holds uniformly as epsilon tends to zero. By (5.1) and the monotonicity of z log^+z, the entropy density on this complement is bounded by

  D_epsilon,k(v)=<v>^k[G_epsilon log^+G_epsilon
                          +C<v>²G_epsilon+M],             (5.5)

an integrable function of v. Its integrability near the transverse axis follows from q<2 and the single extra logarithm, and at infinity from the Gaussian factor. Since the spatial torus has finite volume, it is an integrable phase-space dominator as well.

Estimates (5.3) and (5.5) prove both uniform integrability and velocity tightness of the family

  {<v>^k eta_M(F(t),v):0<=t<=tau}.                          (5.6)

To be explicit, first choose epsilon so that (5.3) is small. For any measurable set E in phase space, its integral on U_epsilon(t) is then small for every t, although that tube set moves. On E outside U_epsilon(t), absolute continuity of the integral of D_epsilon,k makes the integral small when |E| is small. Similarly, choose a large velocity radius so that the tail of D_epsilon,k is small, and use (5.3) for the remaining small tubes. No compactness of the moving tube boundaries is required.

If t_n tends to t in [0,tau], the source strong L1 continuity gives F(t_n)->F(t) in L1 and hence locally in measure. On each bounded velocity set, continuity of z->eta_M(z,v), with M bounded away from zero, gives convergence of the entropy densities in measure. Apply Vitali using (5.6), then remove the velocity restriction with its uniform tails. It follows that

  integral_Omega <v>^k |eta_M(F(t_n),v)-eta_M(F(t),v)|dx dv ->0. (5.7)

This holds for every t, including t=0 and any retirement time; neither solution nor its trace was redefined at exceptional times. The same argument works for every real k>=0 (or one may dominate by a larger integer weight). Thus property 3 of the frozen statement holds. Taking velocity integrals yields continuity of s into L1_x, and using k=1 yields continuity of J into L1_x.

This argument also makes clear why weak convergence and conservation of mass alone would not suffice: the additional estimate is the uniform logarithmic small-tube tail (5.3). We do not assert a uniform rate of entropy continuity in time.

## 6. The characteristic chain rule, including vacuum and the initial trace

The source gives F in C([0,tau];L1) and Q in space-time L1, as well as the distributional unrenormalized equation. Define free-transport representatives

  f#(t,x,v)=F(t,x+t v,v),   q#(t,x,v)=Q(F,F)(t,x+t v,v).

Spatial translation on the torus preserves measure. The distributional equation becomes partial_t f#=q#. With the strong initial trace this yields, in L1 for every t,

  f#(t)=F_0+integral_0^t q#(u)du.                          (6.1)

For example, subtract the right side from f# and test its zero distributional time derivative; it is a time-constant L1 function, and the initial trace sets the constant to zero. This also agrees with comp:path-formula. Fubini then supplies an absolutely continuous characteristic curve for almost every (x,v). This is the needed justification for using a mild chain rule, rather than simply identifying renormalized and distributional classes.

For 0<delta<=1 put

  eta_delta(z,v)=M(v)[(z/M(v)+delta)log(z/M(v)+delta)
                                  -(z/M(v)+delta)+1].      (6.2)

Along each of the absolutely continuous curves (6.1), the ordinary scalar chain rule gives

  D eta_delta(F,v)=Q(F,F)log(F/M+delta).                   (6.3)

On a fixed characteristic and compact time interval, F is continuous and bounded and M(v)>0 is fixed, so the derivative of eta_delta with respect to z is bounded on the range of that curve. This justifies the scalar chain rule before integration over phase space; no global L-infinity bound on F is assumed.

For G=F/M>0,

  |log(G+delta)|<=|log G|+log 2.                            (6.4)

On {F=0}, both collision terms vanish almost everywhere by Section 4, so the right side of (6.3) is zero regardless of log delta. Thus (4.12) supplies an integrable dominator for the right side of (6.3), uniformly in delta. Also eta_delta is nonnegative and

  eta_delta(F,v)<=C[M+F+F log^+F+|log M|F],                (6.5)

uniformly for 0<delta<=1. The right side and its product with |v| are space-time integrable on [0,tau] by Sections 1–2 and (5.2). The same bounds hold at time zero. Formula (6.5) follows from (z+delta)log^+(z+delta)<=C[1+z+z log^+z] and M z log^+z<=F[log^+F+|log M|].

Integrate the characteristic identity against smooth compactly supported tests in time and velocity, periodic in space, retaining the boundary term at zero from (6.1). Dominated convergence using (4.12), (6.4), and (6.5) lets delta decrease to zero. This gives the kinetic entropy identity

  D eta_M(F,v)=Q(F,F)log(F/M)                              (6.6)

as a distribution with initial trace eta_M(F_0,v). The right side is defined as zero on {F=0}, consistently with its proved integrability. This step does not infer an entropy equality from the original bounded-derivative renormalization class; it establishes the unbounded logarithmic renormalization using (4.12).

To remove velocity localization, choose smooth radial cutoffs chi_R(v) between zero and one, equal to one on |v|<=R and supported on |v|<=2R. Test (6.6) with phi(t,x)chi_R(v). Since transport differentiates only t and x, it does not differentiate chi_R. The terms with partial_t phi and v·grad_x phi are dominated by the integrable zeroth and first velocity moments of eta_M. The collision term is dominated by (4.12), and the initial term by the finite initial entropy. Let R tend to infinity. We obtain

  integral [s partial_t phi+J·grad_x phi]
     +integral s_0 phi(0,x)
     +integral phi(t,x) [integral Q(F,F)log(F/M)dv]dt dx=0. (6.7)

There is therefore no unaccounted velocity-flux or initial entropy defect.

## 7. Identification of the local dissipation and every-endpoint equality

By (4.11), for almost every (t,x) every term needed below is absolutely integrable in collision variables. Exchange of v and v_* and the elastic involution preserve the collision measure. On the positive quadrant, with A and B as in Section 4,

  integral Q(F,F)(v)log F(v)dv
    =(1/2) integral (A-B)log B |a|dv dv_*d omega
    =-(1/2) integral (A-B)log A |a|dv dv_*d omega
    =-(1/4) integral (A-B)log(A/B)|a|dv dv_*d omega
    =-d_F(t,x).                                          (7.1)

The equality of the first two integrals follows by exchanging v and v_*; the sign change in the next expression follows by priming both velocities. Averaging the two expressions gives the factor 1/4. Absolute integrability justifies each change of variables and Fubini. Where A=B=0 the integrands are zero. Where just one of A,B vanishes, the collision measure is null by finiteness of Phi, as proved in Section 4. Thus the extended dissipation in the frozen statement is exactly the quantity in (7.1).

Since log M is a linear combination of 1 and |v|², the same collision symmetries give

  integral Q(F,F)log M dv=0.                              (7.2)

All terms here are absolutely integrable by the source polynomial gain/loss estimates and finite velocity moments. Equivalently one can first truncate and then pass by absolute integrability; the elastic equality |v|²+|v_*|²=|v'|²+|v_*'|² gives the cancellation. Consequently the velocity integral on the right of (6.6) equals -d_F. The source entropy inequality already ensures d_F in L1([0,tau]×T³).

Substitution into (6.7) gives exactly

  integral_0^infinity integral_T³
       [s partial_t phi+J·grad_x phi-d_F phi]
       +integral_T³ s_0 phi(0,x)=0.                        (7.3)

The sign of the dissipation is negative in the distributional equation partial_t s+div_x J=-d_F, as required. Both s and J are continuous into L1_x by Section 5. Thus the identity has the prescribed initial trace and no additional defect measure.

Taking a test function constant in space shows that the continuous function H_M(F(t)) has distributional derivative -D(F(t)) in L1(0,tau). Therefore it has an absolutely continuous representative, which agrees with the original continuous H_M(F(t)) at every time. The initial term in (7.3) fixes its value at zero. For every 0<=a<=b<=tau,

  H_M(F(b))+integral_a^b D(F(t))dt=H_M(F(a)).               (7.4)

There are no excluded endpoints. Since tau is arbitrary, this proves the frozen global assertion.

## 8. Compatibility and what has, and has not, been proved

Sections 2–7 apply to either member of the unchanged October pair. Their data, strong traces, nonnegativity, renormalized equations, exact local mass/momentum/energy conservation, polynomial collision integrability, and positive-measure separation remain those already proved by the source. Section 4 adds absolute logarithmic collision integrability, Section 5 adds every-time weighted entropy continuity, and Sections 6–7 give exact local entropy balance and all-endpoint global entropy equality. This proves the author-level implication claimed in FROZEN.md, conditional only on the stipulated pinned source truths.

The added hypotheses used in Sections 2–7 are not imposed on a hypothetical empty subclass. The deterministic tube and Gaussian-sheet estimates belong to the source construction itself and were proved for its finite colored evolutions before passing to each chosen limit. The same fixed construction parameters satisfy all the bounds above; no additional smallness inequality, free parameter, or restriction of the cap family is introduced. In particular q remains the source's fixed exponent strictly between one and two. We do not claim the endpoint q=2 or uniform constants as q approaches it.

The positive-measure distinction is preserved because neither solution undergoes a new selection, gluing or limiting step. Compact initial velocity support is used only as an initial property. The proof permits velocity tails immediately afterward. Vacuum is treated by the collision-measure argument and the characteristic chain rule, not by an assumed positive lower bound. No claim is made that all solutions with this F_0 satisfy the additional identity.

The H-theorem algebra and the chain-rule mechanism are classical paid operations; their primary proofs and the source's strongest global interfaces are compared in COMPARISON.md. The additional calculation is the verification of the logarithmic collision and every-time entropy-tail estimates for this particular singular, nonunique construction. Whether that additional calculation meets the campaign's substantial-contribution criterion requires a separate review; this author proof assigns no such judgment and makes no worldwide-priority claim. The pinned Lean declaration ends in `sorry` and covers only the earlier interface; no formal proof support is claimed for this result.
