# Forward construction carried to local analytic solutions, tail solutions, and the compact matching interface

PREFREEZE calculation. The direction is smooth positive-time continuation of the actual terminal metric from 03-terminal-geometry.md, with a prescribed asymptotic expanding core. This has not become a viable frozen full theorem. The source weak continuation and all backward matching operations are credited in full. The following calculations distinguish actual local conclusions from the unclosed global steps.

## 1. Time sign and the forward profile equation

For an invariant flat metric v=xG(x/rho), rho=sqrt(t), t>0, the fixed-momentum equation is v_t=v^2 S_xx. Set y=x/rho and S=rho^-1 R(y), R=-y^-9[y^10(G-1)]''. Direct differentiation gives

 v_t=-y^2 G'(y)/(2rho),
 v^2 S_xx=y^2G(y)^2 R''(y)/rho,
 R''=-G'/(2G^2).

A cone limit G(infinity)=c and the differentiated decay R'(infinity)=0 give

 R'=(1/G-1/c)/2.                                      (F1)

Since R'=-y^-2 Q(D)(G-1), this is exactly

 Q(D)(G-1)=-y^2/2(1/G-1/c),
 Q(D)=(D-1)(D+9)(D+10).                               (F2)

The sign is opposite to the supplied shrinker. Time reversal of the source is not a forward Calabi solution. Smoothness at the point requires G(0)=1, and the cone parameter c=(1+d)^-1 is already fixed by the source. A formal parameter a=G'(0) remains to be matched, not a proven family of global solutions.

At the origin G=1+a y+(d/264)y^2+(a/624)y^3+..., with all further coefficients fixed recursively. At infinity formal matching gives

 G=c+b/y^2+..., b=180c^2(1-c)>0,
 R=90(1-c)/y-56b/y^3+... .                            (F3)

In particular this tail approaches c from above, unlike the sign of the shrinking tail. The physical homothetic dilation exponent is still 1/(2c), as follows from u_t=-S and the same affine-gauge calculation with t>0. This is compatible with the terminal cone, but is not yet an existence proof.

## 2. Analytic origin construction with a fully quantified disk

This construction is independent of floating integration. Use the Banach algebra of analytic series on |y|<=1 with norm sum |coefficient|. Write G=1+h, h(0)=0, h_1=a. For coefficients of degree k>=2, Q(k)=(k-1)(k+9)(k+10)>=132. Define the diagonal inverse T on those degrees. Equation (F2) is equivalent to

 h=a y+T{ y^2/2 [d+h/(1+h)] }.

For 0<d<=401/1000, |a|<=1/20 and ||h||<=1/10, its image norm is at most

 1/20 + [401/1000+(1/10)/(9/10)]/264
 =11219/216000 < 1/10.

Its Lipschitz constant is at most 1/[264(9/10)^2]=25/5346<1/200. Hence it has a unique analytic origin solution for each such a,d, real for real parameters, with G>=9/10 on real [0,1]. This proves positivity on an actual interval and analytic parameter dependence there. It does not preserve positivity on the remaining half-line.

## 3. Uniform real two-dimensional tail construction

Put s=(27/16)^(1/3)(y/c)^(2/3) and G=c(1+p). The equation becomes

 p'''+(30/s)p''+(751/4s^2)p'-(1215/4s^3)(p-d)-p/(1+p)=0.

Equivalently, with C=1215/4,

 p'''-p=f(s,p,p',p''),
 f=-(30/s)p''-(751/4s^2)p'+(C/s^3)p-(Cd/s^3)-p^2/(1+p).    (F4)

The constant companion matrix for p'''=p has eigenvalues 1 and lambda_+/-=-1/2 +/- i sqrt(3)/2. In coordinates z along eigenvectors (1,lambda,lambda^2), all entries taking f into a diagonal coordinate have modulus 1/3. Real p corresponds to a real growing coordinate and conjugate stable coordinates.

On s>=S=100, use ||z||_3=sup s^3 max_j |z_j(s)|. Prescribe conjugate stable amplitudes A_+/- at S, |A_+/-|<=75/S^3, and suppress the growing mode by

 z_1(s)=-kappa_1 integral_s^infinity exp(s-r) f(r,z(r))dr,
 z_j(s)=exp(lambda_j(s-S))A_j
        +kappa_j integral_S^s exp(lambda_j(s-r))f(r,z(r))dr, j=+,-,
 |kappa_j|=1/3.

These are actual convergent Volterra/anti-Volterra integrals. For r<=s,
 (s/r)^3<=exp(3(s-r)/S),
 so the stable convolution norm, including |kappa_j|, is at most
 K=[3(1/2-3/S)]^-1=100/141.
The unstable norm is <=1/3<=K. The homogeneous stable norm is <=75 because 3/S<1/2. For ||z||_3<=Z=600, |p|<=3Z/S^3=9/5000, so no denominator can vanish. Let

 L=30/S+(751/4)/S^2+C/S^3=255263/800000.

Using |p|,|p'|,|p''|<=3Z s^-3, the map has norm at most

 75+K[3LZ+C(401/1000)+18Z^2/S^3]
 =538917/940 <600.

The factor 18 uses |p^2/(1+p)|<=2|p|^2. With a0=9/5000, the Lipschitz constant is at most

 K[3L+3 a0(2+a0)/(1-a0)^2]
 =6430686806303/9366190456000 <69/100.

Thus contraction gives a REAL two-dimensional family of genuine positive tails for each fixed admissible d. This is a local-at-infinity family; it is not a family satisfying the origin conditions. The finite rational inequalities above are checked by forward_bounds.py, using Fraction only. The kernel estimates and quantified infinite interval are proved here rather than inferred from sampled values. The first run used a smaller ball/seed pair (Z=400, seed25); the present file records the subsequently enlarged, rechecked domain.

The tail has p=Cd s^-3+O(s^-6). One rigorous route to the leading remainder is to subtract p0=Cd s^-3, including its first two derivatives in the companion vector. Its residual in (F4) is O(s^-6). Linearize the difference exactly using the bounded secant coefficient of p^2/(1+p). The same Green formulas in weight 6 have K_6=[3(1/2-6/100)]^-1=25/33, with linear plus nonlinear norm less than 3 K_6 L + 3 K_6 a0(2+a0)/(1-a0)^2 <1. The prescribed stable difference at S has finite weight-6 norm. Solving this linear difference equation in weight 6 and using weight-3 uniqueness identifies it with the already constructed tail. The residual coefficient depends on d but is finite uniformly on the compact d interval. This proves (F3), including the stated derivatives. Higher differentiated expansions can be obtained by subtracting more recursively determined s^-3j terms and increasing S for each desired weight; no such expansion is used as a substitute for finite matching.

## 4. A global uniqueness consequence, and why the slope is not free

Suppose two positive bounded analytic-origin solutions of (F2) exist for the SAME c on [0,infinity). Define w=1-G. Then

 R(y)=y^-9 [y^10 w(y)]'',
 w(y)=y^-10 integral_0^y (y-s)s^9 R(s)ds,              (F5)
 R'(y)=F_c(w(y)), F_c(w)=(w-(1-c))/[2c(1-w)].          (F6)

The integration constants in (F5) vanish by origin analyticity. For w<1,
 F_c'(w)=1/[2(1-w)^2]>0.

If R_2(0)>R_1(0), the positive Volterra kernel in (F5) and the first-crossing argument give R_2-R_1>=R_2(0)-R_1(0) throughout every common finite interval. Indeed as long as the difference is positive, w_2-w_1 is positive and (R_2-R_1)' is positive; a first loss of positivity is impossible. Consequently

 w_2(y)-w_1(y)>=[R_2(0)-R_1(0)]y/110.

This contradicts boundedness of both G_i on the half-line. If R_2(0)=R_1(0), the analytic recursion and ODE uniqueness identify the solutions. Therefore at most ONE positive bounded global expander exists for each c, and at most one origin slope a=-R(0)/110 can be admissible. This is an actual compatibility argument; neither the shooting slope nor the two tail amplitudes can be counted as an established geometric freedom.

The same observation does not prove existence. A first-zero or blowup shooting partition needs a valid separation/compactness theorem. Simultaneous grazing of auxiliary shooting boundaries cannot be dismissed by a second-order maximum principle. The third-order system (F2) does not supply such a principle. The positive comparison above compares different origin slopes while BOTH solutions exist; it does not guarantee a globally positive limiting trajectory.

## 5. Bounded numerical exploration and the remaining finite match

forward_explore.py was inspected as authored code and run only in bounded standard-library loops. Its fourth-order Runge-Kutta computation is FLOATING POINT, starting at y=.005 from a degree24 analytic series, with maximum log-step .0015. It has no certified truncation or roundoff enclosure. It is not a proof of an inequality, global positivity, or matching.

Eleven trial slopes at Y=20 and 43 bisections for each Y=20,40,60 were run. Matching only the leading approximation G(Y)=c+b/Y^2 gave slopes approximately

 Y=20: -0.0285814767151,
 Y=40: -0.0289533012951,
 Y=60: -0.0289547863300.

Their derivative endpoint values were NOT imposed and do not equal a certified tail. For example the Y=60 computation gives D G approximately -.0110084 and D^2 G approximately .0512495. This finite-endpoint scalar condition does not kill the actual growing coefficient at infinity. The central numerical d was used, not a certified common matching interval for every source d. No uniform or rigorous existence inference is made from this experiment.

The analytic origin and tail constructions reduce global existence at the actual certified source c to a concrete three-coordinate match: one origin slope and two real conjugate stable-tail amplitudes must match G,DG,D^2G at a common positive y, through a positive finite-interval solution. The tail section s=100 corresponds to y=c(16/27)^(1/2)100^(3/2). The exact match also needs control of the actual d within its source certificate enclosure, not just its midpoint. This matching and positivity have not been proved. The source shrinker certificate pays a DIFFERENT-sign matching problem and does not certify this one.

## 6. Carry the proposed forward model through the compact interface

Even if that finite match were closed, the remaining compact operation is not automatic. Let v0 be the actual terminal profile from note03. Near zero,

 v0-cx=O(x^(1+delta)),
 d_x^j(v0-cx)=O(x^(1+delta-j)) for the available weighted jets.

Adding v0-cx directly to a smooth forward core leaves a nonsmooth origin at every t>0. The strongest basic smooth trial uses a MOVING cutoff theta(x/rho), zero for x/rho<=1 and one for x/rho>=2:

 v_app=xG_+(x/rho)+theta(x/rho)[v0(x)-cx]

near the point, followed by a fixed outer interpolation to the full v0 profile. Its tail discrepancy is x(G_+-c)=O(t/x), with differentiated remainders. Its momentum trace is v0. Positivity of this trial follows for small core radius from G_+>=g0>0 and |v0-cx|<=Cx^(1+delta), and on the outer region from the positive terminal profile. At x=0 its derivative is exactly1, and the divisor must retain the original smooth endpoint derivative -1. The fixed complex gauge must be integrated with u_t=-S+110; it is not an independent time-varying dilation.

The moving-cutoff correction in H is O(rho^(-1+delta)) in the annulus x~rho, but its time derivative is O(rho^(-3+delta)). Thus its residual occupies the full intended forcing weight. It does not become small merely by taking t down to0. The amplitude inherited from V0 can be made small in the source construction, and the core geometric error is lower order. The paid inner/outer commutator cancellation should be retained in any forward parametrix; a naive cutoff error alone is not the claimed obstruction.

To see the actual new linear problem, put z auxiliary in R^24 with x=|z|^2, zeta=z/t^(1/4), tau=log t, V=rho^-1 w(tau,zeta), h=(G_+-1)/y. The flat linearization becomes

 rho^3 P_+ V = w_tau+B_+ w,
 B_+= G_+(|zeta|^2)^2 Delta_zeta^2/16
      -(zeta/4).grad -1/2 + yG_+'(y)/G_+(y).          (F7)

The potential term follows from 2yG_+ Ahat h and the exact forward model equation G_+^2 Ahat h=(h+yh')/2=G_+'/2. This verifies its sign. At infinity the transport is -(zeta/4).grad, opposite the backward construction's confining rescaled drift. A correction with prescribed terminal trace behaves as

 w approximately exp(delta tau/2)|zeta|^(-2+2delta)

in the overlap. The leading drift-plus-constant part of B_+ acts on that spatial power by -delta/2. Thus the terminal trace lies at the corresponding asymptotic transport rate; it cannot simply be discarded or assigned by the source's future-forcing choice of unstable modes.

A required forward inverse must solve (F7) in a space with this prescribed singular initial trace (or explicitly subtract a legitimate evolution of it), control all four spatial derivatives and one time derivative, and remain compatible with the outer projective initial-value problem. The source backward right inverse does not have those trace data. Smooth dependence on compact negative-time intervals supplies none of these bounds. The rough-data He-Zeng result needs a small bounded complex Hessian relative to a smooth background; (12) in note03 violates boundedness. Guan's CP1-bundle evolution estimates explicitly assume BOTH endpoint codimensions are1, whereas this projective point has complex codimension10. Its extremal-soliton quadrature also solves a different equation from (F2). Those complete available reductions do not yield the missing forward inverse here.

After such an inverse, one would still have to execute a contraction with the moving cutoff residual, verify both endpoint jets and fixed FS class, integrate the affine gauge, prove convergence to the ACTUAL phi0, and use the EVI identification to show it is the already-existing weak continuation. None of those is replaced by a flat formal solution.

## Disposition

The concentration/gauge/cone calculation and the origin/tail/uniqueness constructions above are durable integrated progress. They do not close a new substantial full-scope theorem. No theorem is frozen. The first unclosed operation is a positive finite-interval origin-to-tail expander match at the actual source cone parameter. A second independent unclosed operation is a forward weighted inverse with the prescribed terminal trace and compact matching. Report PREFREEZE/no nominee, with no correctness/contribution/acceptance/count assigned.
