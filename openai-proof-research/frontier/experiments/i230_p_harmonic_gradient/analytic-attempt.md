# I230 — actual p-harmonic gradient convergence

## Status and scope

The unrestricted large-p gradient problem is **not closed**. A complete restricted theorem is proved below: uniformly close, smooth, noncritical, quasiconcave p-harmonic functions converge in their actual gradients at a power rate to a noncritical C^{1,alpha} comparator. The proof supplies the gradient control, rather than assuming equicontinuity of the approximating gradients. This includes convex-ring potentials after using their known structural properties. It is a quantitative refinement of an existing qualitative convex-ring argument, not an independently substantial finding under the original exclusion of standard transfers.

All pinned OpenAI results and lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. I224 R/S are available as proved local results but are not needed in the restricted proof. No new accepted-count claim is made.

## 1. Exact restricted theorem

Let n>=2, 0<alpha<=1, 0<m<=M<infinity, K>=0. Put

    B = 2 + K/(1+alpha),
    delta_0 = min{16^{-(1+alpha)}, (m/(4B))^{(1+alpha)/alpha}}.

For every real p>=2, suppose:

* u belongs to C²(B1), Du never vanishes in B1, and div(|Du|^{p-2}Du)=0 there;
* u is quasiconcave on B1: each strict superlevel set {u>c} intersected with B1 is convex;
* v belongs to C^{1,alpha}(B1), m<=|Dv|<=M, and [Dv]_{C^{0,alpha}(B1)}<=K;
* delta=||u-v||_{L-infinity(B1)} satisfies 0<delta<=delta_0.

Then, for a finite explicit constant C=C(alpha,m,M,K), independent of p and u,

    ||Du-Dv||_{L-infinity(B1/2)} <= C delta^{alpha/(1+alpha)}.       (Q)

One may take, with E=(4B+2K)/m,

    C = B + M E²/2 + 4MB/m.

The alpha-dependence is already contained in B and delta_0. If delta=0, the conclusion is immediate. No boundary agreement is required. No equation is required of v. There is no hypothesis of a uniform C¹ or C^{1,beta} norm of u, nor a quantitative positive lower bound on |Du|. Nonvanishing of Du, quasiconcavity, and the exact p-equation are essential hypotheses of this proof; they are not inferred for arbitrary p-harmonic approximants.

### 1.1 Normal estimate from values and convex superlevels

Set h=delta^{1/(1+alpha)} and T=B h^alpha/m; then h<=1/16 and T<=1/4. Fix z in B3/4, write a=Dv(z), e=a/|a|, and n=Du(z)/|Du(z)|. Taylor's estimate is

    |v(z+y)-v(z)-a·y| <= K |y|^{1+alpha}/(1+alpha).              (1)

For any unit omega perpendicular to e, set t=2T and

    y_±=h(t e ± sqrt(1-t²) omega).

These points lie in B1. By (1) and ||u-v||<=delta,

    u(z+y_±)-u(z)
      >= m h t - K h^{1+alpha}/(1+alpha) - 2delta
       = B h^{1+alpha} > 0.

Quasiconcavity implies n·y_±>=0. Indeed, along the segment from z to z+y_± all sufficiently short positive increments have u>=u(z), and the one-sided directional derivative at z is nonnegative. Summing yields n·e>=0. Taking both signs for every omega gives

    sqrt(1-t²) |n-(n·e)e| <= t(n·e).

Since |n|=1, n·e>=sqrt(1-t²), and therefore

    |n-e|²=2(1-n·e)<=2t²,
    |n-e|<=4T.                                                (2)

This is an estimate on the actual unit normal at every z in B3/4. It does not use differentiability of a limiting normal or any gradient modulus for u.

### 1.2 The equation supplies monotone speed

The same quasiconcavity shows D²u(z)[tau,tau]<=0 for tau perpendicular to Du(z). For completeness, the strict superlevel has supporting plane through z with inward normal n. If a tangent point z+s tau had u>u(z), the open superlevel would lie on both sides of that supporting plane, which is impossible. Thus u(z+s tau)<=u(z) for small s, and the second derivative inequality follows.

Let g=|Du|. In an orthonormal frame with last direction n, put T_u=trace_{n-perp}D²u<=0. The p-equation, at the nonzero gradient, reads

    (p-1)u_nn + T_u = 0.

Consequently u_nn>=0 for every p>=2. For the unit-speed ascending gradient flow

    gamma'(s)=n(gamma(s)), gamma(0)=x,

one has

    d/ds g(gamma(s)) = Dg·n = u_nn >=0.                         (3)

For x in B1/2 this flow exists on [-h,h] and stays in B_{1/2+h} subset B3/4. To justify continuation, n is C¹ and has length one; a trajectory of length at most h stays in a compact interior ball where n is C¹ and Du is nonzero. No p-uniform Lipschitz bound on the vector field is needed for existence on this fixed time interval.

### 1.3 Upper and lower gradient magnitudes

Fix x in B1/2, put a=Dv(x), and use the flow above. Along gamma, d(u(gamma(s)))/ds=g(gamma(s)). From (3),

    h g(x) <= u(gamma(h))-u(x).

Taylor's estimate for v and |gamma(h)-x|<=h give

    g(x) <= |a| + B h^alpha.                                  (4)

For the lower bound, (3) yields

    h g(x) >= u(x)-u(gamma(-h)).

The map q -> q/|q| obeys |q/|q|-q'/|q'||<=2|q-q'|/m when both norms are at least m. Hence (2), the Hölder bound on Dv, and |gamma(s)-x|<=h give

    |n(gamma(s))-a/|a|| <= E h^alpha,
    E=(4B+2K)/m,  -h<=s<=0.

For two unit vectors b,e, e·b=1-|b-e|²/2. Therefore

    a·(x-gamma(-h))
      = integral_{-h}^0 a·n(gamma(s)) ds
      >= h |a| (1-E² h^{2alpha}/2).

Applying (1) at x and subtracting the two possible value errors gives

    g(x) >= |a| - B h^alpha - (M E²/2) h^{2alpha}.              (5)

Since h<=1, (4)-(5) imply |g(x)-|a||<=(B+M E²/2)h^alpha. Finally,

    |Du(x)-Dv(x)|
      <= |g(x)-|a|| + |a| |n(x)-a/|a||
      <= [B+M E²/2+4MB/m] h^alpha.

This proves (Q), including all domain margins and p-independence.

### 1.4 Application to actual convex-ring potentials

Let n>=3, let Omega=Omega_0\K be a bounded convex ring, with K a nonempty compact convex subset of the open bounded convex Omega_0, and with positive separation from its outer boundary. Let v be the infinity potential with values 0 on the outer boundary and 1 on K; let u_p be the corresponding p-potential, for p>n. Extend both by 1 on K when discussing convex superlevels.

Use the known structural conclusions for these potentials: u_p is smooth and noncritical in Omega and has convex superlevel sets (Lewis, as used in Peng–Zhang–Zhou, Sections 3–4); v is noncritical (Peng–Zhang–Zhou Theorem 1.1). Fix any compact E subset Omega and a finite covering by balls B_{2r}(z) compactly inside Omega. On this covering the stipulated family-377 estimate gives v a common C^{1,alpha_n} bound. Continuity and nonvanishing give a positive minimum m on the enlarged compact covering.

With delta_p=||u_p-v||_{L-infinity(Omega)}, rescale each ball and apply (Q). Once delta_p is sufficiently small,

    ||Du_p-Dv||_{L-infinity(E)} <= C_E delta_p^{alpha_n/(1+alpha_n)}.      (6)

Here C_E depends on the ring, the interior buffer, and v's indicated norms and positive lower bound; it does not depend on p. These are the actual, unmollified gradients.

Under the exact additional hypotheses of Bungert Theorem 1 — a uniform bound H on [u_p]_{C^{0,alpha_p}(Omega)}, alpha_p in [1-n/p,1], the stated Sobolev/continuous solution class, and identical boundary data — delta_p=O(p^{-1/4}), and (6) gives

    ||Du_p-Dv||_{L-infinity(E)} = O(p^{-alpha_n/(4(1+alpha_n))}).          (7)

If also ess inf_{Omega}|Dv|>0, Bungert gives delta_p=O(p^{-1/2}) and the exponent in (7) improves to alpha_n/(2(1+alpha_n)). The latter is a global-gradient condition for the value theorem; the local minimum on the covering alone does not justify it. Alternatively, either value estimate may simply be assumed explicitly. No unchecked assertion about arbitrary boundary regularity or a uniform H is hidden here.

For the variational convex-ring problem the H condition can also be paid. Put d0=dist(K,partial Omega_0)>0 and choose the fixed Lipschitz boundary extension

    g(x)=min{1,dist(x,partial Omega_0)/d0} on Omega_0.

It is 1 on K and 0 on the outer boundary, and has Lipschitz constant at most 1/d0. Thus g belongs to W^{1,infinity}(Omega), the prescribed boundary values have a global Lipschitz extension, and both its gradient Lp norms and its C^{0,1-n/p} seminorms stay bounded as p->infinity. Take u_p to be the minimizer with u_p-g in W_0^{1,p}(Omega), as in Bungert Definition 2.1. Its energy is at most that of g. Bungert Remark 2.5, which uses zero-extension Morrey estimates, now gives H<infinity for alpha_p=1-n/p. The continuous representative has the prescribed trace for p>n in this setting. Hence (7) applies to these actual variational convex-ring potentials without a separate H assumption. The optional p^{-1/2} value improvement still requires a global positive essential gradient infimum, not just the interior one.

These are restricted quantitative corollaries. Peng–Zhang–Zhou already prove qualitative local uniform convergence of the full gradient, and their proof uses essentially the same convex-normal and magnitude information. Thus (Q)-(7) are not nominated as a tenth independent finding. The flow proof is a paid alternative derivation, but is still a quantitative transfer from existing convex geometry.

## 2. Unrestricted anisotropic route: exact regimes

Let epsilon=1/(p-2), p>2. At a nonzero test gradient the p-equation is equivalent to

    D²u[Du,Du] + epsilon |Du|² Delta u = 0.                    (8)

Upper tests have the nonnegative sign; lower tests the nonpositive sign. For actual weak p-solutions these necessary viscosity inequalities hold. All rescaled contacts used below have nonzero physical gradient eventually, so there is no deletion of a critical-gradient condition.

### 2.1 Why the affine lift is not allowed

For a smooth solution and U(y,b)=u(y)+b,

    Delta_inf U + epsilon |DU|² Delta U = epsilon Delta u,

by (8), which generally is not zero. Equivalently its p-divergence has the nonzero residual

    (|Du|²+1)^{(p-4)/2} Delta u.

The infinity-harmonic lift contract in the pinned source cannot be used to create a p-harmonic lift. The local restricted theorem avoids this operation entirely.

### 2.2 Source-width normalization

Suppose a nonzero fitted slope has been rotated to c e_n, with c bounded above and away from zero. No such fit is assumed for all p-solutions here; this calculation is conditional on its availability. Put x in R^{n-1} and

    u(z+r(sqrt(lambda)x,t))=u(z)+rc(t+lambda V(x,t)).

For a test phi set b=(D_x phi,1+lambda phi_t) and

    Q=lambda|D_x phi|²+(1+lambda phi_t)².

The transformed equation is exactly

    D²phi[b,b] + (epsilon/lambda) Q (Delta_x phi+lambda phi_tt)=0.       (9)

Indeed Du=c(sqrt(lambda)D_xphi,1+lambda phi_t), the Hessian is
(c/r)[Dxx phi, sqrt(lambda)Dxt phi; sqrt(lambda)Dtx phi,lambda phi_tt],
and Delta_inf u=(lambda c³/r)D²phi[b,b].

For sequences lambda_i->0, epsilon_i->0 and locally uniformly convergent V_i, viscosity stability at strict contacts gives:

* epsilon_i/lambda_i ->0: D²V[(D_xV,1)]=0, the stipulated homogeneous equation.
* epsilon_i/lambda_i ->nu in (0,infinity):

      F_nu[V] := D²V[(D_xV,1)] + nu Delta_x V=0.               (10)

* epsilon_i/lambda_i ->infinity: divide (9) by that ratio; the only resulting equation is Delta_x V=0.

The last limit alone is insufficient even with the exact inherited fits. V(x,t)=sin(t) is a nonaffine entire classical solution of Delta_x V=0, and, for every center and R>0, p=0,q=0 give

    |V(x+h,t+l)-V(x,t)|<=|l|<=R

on |l|<=R, |h-p l|<=R. Thus the source all-center/all-radius fit contract holds with C0=1. This is a counterexample to a proposed Liouville statement for that weakened limit, not a constructed counterexample to p-harmonic gradient convergence. At finite nu, V=sin t does NOT solve (10).

The radius r has canceled from (9). I224's choice r/lambda->0 does not force epsilon/lambda->0. Failure of a power estimate for a family with varying p does not supply that relation: the selection may choose p only logarithmically large relative to 1/r, or scales with lambda much smaller than epsilon. Those regimes cannot be dropped.

### 2.3 The different normalization when lambda/epsilon ->0

To retain longitudinal curvature in that regime one would use the wider transverse scale sqrt(epsilon)r:

    u(z+r(sqrt(epsilon)x,t))=u(z)+rc(t+lambda W(x,t)),
    mu=lambda/epsilon,
    Qtilde=(lambda²/epsilon)|D_xphi|²+(1+lambda phi_t)².

The exact equation becomes

    D²phi[(mu D_xphi,1+lambda phi_t)]
       + Qtilde(Delta_x phi+epsilon phi_tt)=0.                 (11)

If mu->0 and the W_i converge locally uniformly, its limit is the full harmonic equation Delta_x W+W_tt=0. This is a proved conditional limit statement, not a compactness theorem. The old source cylinder controls only |x| up to sqrt(lambda/epsilon) in these coordinates; that width tends to zero. Its value bound therefore does not supply local boundedness or compactness of W_i on a fixed full-dimensional box. A new wider-cylinder estimate is required before using harmonic Liouville here.

### 2.4 Finite transverse viscosity: exact variational structure

For nu>0 define

    H(P,q)=q+|P|²/2,
    L_nu(P,q)=exp(H(P,q)/nu).

For C² V, the Euler equation div_{x,t} D L_nu(D_xV,V_t)=0 is exactly

    exp(H/nu)/nu² [F_nu[V]]=0.

To check: D_P L=L P/nu, D_q L=L/nu. Thus the divergence is
L/nu² [H_t+D_xV·D_xH+nu Delta_xV], and H_t+D_xV·D_xH equals the first term in (10).

The integrand is strictly convex: for increments (xi,tau),

    D²L_nu(P,q)[(xi,tau)]
      = L_nu(P,q) [ |xi|²/nu +(P·xi+tau)²/nu² ] >0

unless both increments vanish. The finite-viscosity limit is therefore an actual different variational equation, not simply a forced infinity equation with bounded prescribed f. Dividing or estimating Delta_xV as if it were a bounded forcing would assume the missing second-derivative estimate.

The same integrand follows directly on compact sets of bounded first jets from the p-energy. In the source-width normalization its density after removing the constant c^p and the Jacobian is Q^{p/2}. If epsilon/lambda->nu in (0,infinity), p lambda->1/nu and

    Q^{p/2} -> exp((V_t+|D_xV|²/2)/nu)

uniformly on each bounded set of first jets, by the expansion log Q=lambda(2V_t+|D_xV|²)+O(lambda²). This proves the local density limit only; no Gamma-convergence, minimizer compactness, or global gradient bound is asserted.

A conditional rigidity fact helps locate the gap. If a C³ entire solution of (10) has a globally bounded full gradient DV, it is affine. Differentiate its divergence equation: every derivative V_j solves div(A DV_j)=0, A=D²L_nu(DV). The formula above and bounded DV give global positive ellipticity bounds and bounded coefficients. Each V_j is bounded. Let b=inf_{R^n}V_j and w=V_j-b>=0. The scale-invariant Harnack inequality on cubes (Li–Zhang, Theorem 1.1, restating and proving the classical Moser inequality) gives

    sup_{Q_R} w <= C inf_{Q_R} w,

because the equation holds on Q_{6R}, with C independent of R. As R->infinity the infimum tends to inf_{R^n}w=0. Every fixed point is eventually in Q_R, so w vanishes everywhere. Every derivative is therefore constant. The additional global bound on DV is NOT an output of the source affine fits. Consequently this conditional fact does not close the finite-nu regime.

## 3. Independent fixed-cutoff / local-excess route

Let u be weakly p-harmonic, ell=a·x+b, ||u-ell||<=delta on a ball, and eta a compactly supported C¹ cutoff. Write A_p(q)=|q|^{p-2}q and q=Du. Testing the difference between u and ell with eta²(u-ell) gives the exact identity

    integral eta² (A_p(q)-A_p(a))·(q-a)
      = -2 integral eta (u-ell)(A_p(q)-A_p(a))·Deta.            (12)

There is no derivative-of-eta factor p. Algebra also gives

    (A_p(q)-A_p(a))·(q-a)
      = (|q|^{p-2}+|a|^{p-2})|q-a|²/2
        + (|q|^{p-2}-|a|^{p-2})(|q|²-|a|²)/2
      >= (|q|^{p-2}+|a|^{p-2})|q-a|²/2.

Combining this with |A_p(q)-A_p(a)|<=|q|^{p-1}+|a|^{p-1} yields a fully paid estimate

    integral eta² (|q|^{p-2}+|a|^{p-2})|q-a|²
      <=4delta integral eta |Deta| (|q|^{p-1}+|a|^{p-1}).      (13)

This is genuinely a different test from eta^p, but does not control its right-hand flux by a p-independent unweighted quantity. Relative to |a|^{p-2}, regions with |q|>|a| can have exponential weight. A nonzero limiting gradient supplies neither the missing flux bound nor a p-uniform conversion from a weighted excess to pointwise gradient control.

A sharper linearized flux-angle estimate also degenerates. At a=e1,

    D A_p(a)=diag(p-1,1,...,1).

For h=(p-1)^(-1/2)e1+e2 and q=a+s h, let s->0 with p fixed. Then

    [(A_p(q)-A_p(a))·(q-a)] / [|A_p(q)-A_p(a)| |q-a|]
      -> 2 / sqrt(p(1+1/(p-1))) = O(p^(-1/2)).

Thus a uniform positive lower bound for this flux angle is false, even arbitrarily near a nonzero affine gradient. The Hessian of |q|^p/p has eigenvalue ratio p-1 there. Bounded away from zero is not the same as uniformly elliptic in p.

A local-excess closure would need, for example, a p-independent estimate converting (12) into decay of unweighted gradient oscillation on a smaller ball for solutions merely close in value to an affine function. Neither (13), the affine-gradient lower bound for v, nor the classical fixed-p estimates supply it. No such estimate is assumed or nominated here. The quasiconcave route in Section 1 avoids this failure by imposing actual geometric structure and using the sign of u_nn instead of controlling the flux.

## 4. Exact remaining claims that would be sufficient, and verdict

A direct noncritical target would be: for each n,m,K,M there exist C,theta>0,p0 such that, whenever p>=p0, v is infinity-harmonic on B1 with m<=|Dv|<=M and [Dv]_{alpha_n}<=K, and u_p is p-harmonic with ||u_p-v||<=delta, then

    ||Du_p-Dv||_{B1/2} <= C(delta+1/p)^theta,                  (G)

with no quasiconcavity, prescribed sign of Delta u_p, or prior gradient equicontinuity. This remains UNPROVED. It would give an actual rate after a suitable value theorem. No necessity or optimal exponent is claimed for the displayed additive 1/p formulation.

For a general p-independent C^{1,beta} theorem, one must additionally handle critical fitted gradients, supply uniform qualitative flatness for the actual p-family, and treat all epsilon/lambda regimes. Even assuming nonzero fitted slopes, the source argument leaves (i) rigidity or another estimate for finite positive transverse viscosity with exactly inherited fits, and (ii) wider-cylinder compactness in the dominant-viscosity regime. The sin(t) example proves that simply applying Liouville to Delta_xV is invalid.

Verdict: no unrestricted theorem and no tenth independent finding. The restricted theorem (Q) and conditional limit/density calculations are paid mathematics. The strongest restricted p-rate here is (7), with the improved exponent only under Bungert's global-gradient/value hypotheses. The convex-ring rate is a standard quantitative extension of Peng–Zhang–Zhou once the stipulated Hölder estimate is supplied, so it does not clear the contribution standard. No worldwide novelty is claimed.
