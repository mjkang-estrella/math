# r232 prefreeze feasibility calculations

Authorized Codex / GPT-6 Astra / xhigh / default service tier. Source356 only. No grades or counts. Written after complete canonical operative reading and the primary selections recorded separately. This is feasibility, not a frozen author-proof nominee.

Consider n>=3, p>n/3, full-support unreduced RCD(0,n), m=H_d^n, complete separable. Assume 0<=rho<=1 bounded continuous and the ORIGINAL GLOBAL tensor inequality R(X,Y,Y,X)(f)>=-integral f rho |X wedge Y|^2 dm. Fix o and m(B_r(x))>=v r^n for x in B(o,2), 0<r<=1. Set delta=||rho||_{Lp(B(o,3))}. Candidate conclusion: every chosen side sigma of every triangle with vertices in B(o,1) and perimeter<=1 obeys
 d(p0,sigma_t)^2 >= (1-t)d(p0,x)^2+t d(p0,y)^2-t(1-t)d(x,y)^2 - C(n,p,v) delta^{p/(p+3n)}.
The vertex is denoted p0 to avoid collision with integrability p.

Paid first step: monotonicity gives RCD(-(n-1),n); tensor >=-1 and Source356 give CBB(-1). Dimension and exact measure stay n and H^n. This is not the new conclusion.

Retain rho in the source Riccati identity, while its acceleration-error estimate continues to use the coarse bound -1. At positive viscosity, replace the -kappa wedge term by +rho wedge squared. Boundedness of rho and the paid strong weighted velocity convergence pass this term. Every other source heat, density, trace, frame and countable trial operation stays paid. Linear parallel trials on [epsilon,1], followed by epsilon downarrow0, give
 H_{q_a}(Z,Z) <= (1+D_a)|Z|^2 m, q_a=d(a,.)^2/2,
 D_a(x)=d(a,x)^2 max_{gamma:a->x} integral_0^1 t^2 rho(gamma_t)dt.
The maximum is over all minimizing constant-speed paths. Properness and continuity of rho make D upper semicontinuous. The source's canonical radial path is unique for m-a.e. x, hence the maximum equals its value there. The Hessian measure has nonpositive singular part, by the countable-infimum argument with one initial trial.

For terminal m|B(a,2), radial contraction T_t has (T_t)#m|B(a,2)<=t^{-n}m. This follows from the unreduced CD(0,n) density inequality by approximating the Dirac initial endpoint and using uniqueness at a.e. terminal point. Thus, by Minkowski,
 ||D_a||_{Lp(B(a,2))} <= 4 integral_0^1 t^{2-n/p}dt ||rho||_{Lp(B(a,2))}
 =4/(3-n/p) ||rho||_{Lp(B(a,2))}.
This is why p>n/3 is imposed; it is a sufficient exponent, not a sharpness assertion.

Flatten q with chi'(q)=theta(q), theta=1 on r<=1, theta=0 on r>=2, theta nonincreasing smooth. F_a=chi(q_a) is bounded globally 2-Lipschitz. Its weak Hessian is <=(1+theta D_a)|Z|^2m. The negative chi'' radial term and singular part are retained with their signs. Put Dtilde=theta D_a. Bounded usc Dtilde>=0 has decreasing bounded continuous Lipschitz majorants D_j(x)=sup_y(Dtilde(y)-j d(x,y)). Apply the FULL companion to F_a,1+D_j and then dominated convergence, to obtain the Green inequality on every minimizing path with Dtilde. There is no unsupported restriction of an m-a.e. tensor to a curve.

Quantitative geodesic stability, to check in detail: in a CBB(-1) space let A,x,y lie in this order on a minimizing segment, d(A,x)=h in (0,1/8], d(x,y)=L<=1, h+L<=1, and d(x',x),d(y',y)<=r<=1/8. If z=gamma_t for ANY minimizer from x' to y', w lies at distance tL from x on [xy], then d(z,w)<=30 sqrt(r/h). Hyperbolic point-side comparison gives
 cosh d(A,z)>=a_t(l')cosh d(A,x')+b_t(l')cosh d(A,y')
 >=cosh(h+tL)-200r,
 where a_t(l)=sinh((1-t)l)/sinh l and b_t(l)=sinh(tl)/sinh l.
On l in [0,2], |a_t'|,|b_t'|<=8; the last error is <=136r, so 200 is safe. At x, the backward and forward directions have angle pi. The three-angle sum is <=2pi. Hinge comparison then gives
 cosh d(z,w)<= [sinh(h+tL)/sinh h]cosh d(x,z) - [sinh(tL)/sinh h]cosh d(A,z).
Use d(x,z)<=tL+3r, sinh(h+tL),sinh(tL)<=2, sinh h>=h and sinh(tL+3r)<=4. Subtract the exact degenerate identity to obtain cosh d(z,w)-1<=424r/h. Therefore d(z,w)^2<=848r/h<900r/h. Degenerate cases are direct or by continuity. This uses actual AKP hinge/point-side proofs, not nonbranching compactness alone.

Endpoint ball transports: ball radius r has density <=(v r^n)^{-1}; the unreduced RCD(0,n) interpolation keeps this bound. Along a strictly trimmed side, expected Dtilde is bounded by (v r^n)^{-1/p}||Dtilde||p. The Green kernel integrates to t(1-t)/2<=1/8. F_a is 2-Lipschitz, so comparison to the prescribed trimmed side costs <=60 sqrt(r/h). Endpoint errors cost 2r; speed correction costs <=r. The integrated defect costs <=[5/((3-n/p)v^{1/p})] delta r^{-n/p}.

Choose physical trim h<=1/8, r=h^3/4096. Then the path error is <=15h/16 and 3r<=h; total <=2h plus defect. For the original side use f(s)=q_a(sigma_s)-s^2/2. It is 2-Lipschitz for perimeter<=1. Comparing chords on [h,l-h] and [0,l] costs <=4h. For l<=4h the direct Lipschitz estimate costs <=8h. A uniform safe q-error is
 10h + B delta h^{-3n/p}, B=5*4096^{n/p}/((3-n/p)v^{1/p}).
Optimizing h=(B delta)^{p/(p+3n)} gives q-error <=11(B delta)^alpha when h<=1/8. For larger delta the trivial squared-distance bound <=1 suffices. Candidate squared-distance constant: 22 B^alpha. Delta=0 follows by h downarrow0.

Compatibility work to finish: on S^2 x S^2 (n=4), the product has Ricci=1 and mixed sectionals 0. A local small conformal perturbation u_epsilon=a epsilon^2 phi(x/epsilon), phi quadratic positive near the center, creates negative mixed sectionals while retaining Ricci>=0, a uniform coarse sectional bound -1, exact H^4, and uniform noncollapse. Prove all bounds quantitatively using finite coordinate constants before using this as non-vacuity evidence. No claim that the rate is sharp. Uniformly bounded continuous rho is not replaced by an arbitrary Lp representative.

Outstanding before freezing: verify all constants and the global defect-index/usc approximation/domain steps; read closest actual comparison antecedents; perform refined guarded history query for this exact construction; preserve primary exposure and proof-reading limitations. No theorem frozen yet.
