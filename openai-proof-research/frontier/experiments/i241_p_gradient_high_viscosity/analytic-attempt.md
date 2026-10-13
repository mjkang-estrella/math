# I241 — restoring ellipticity on a selected larger cylinder

**Final status:** a complete actual-p cylinder estimate and exclusion of the nonzero-slope, high-viscosity bad-scale regime are proved below. No unrestricted p-uniform gradient theorem, count increment, or contribution-gate approval is asserted. The prerequisite of obtaining a suitable noncritical selected family from arbitrary value-convergent p-harmonic functions is not proved here.

All pinned OpenAI statements and lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. The full finalized I236 proof was read; its SHA-256 equals the supplied a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931. Its finite-positive-tau theorem is available, but the new high-viscosity proof does not use it or infer a uniform estimate from it.

## 0. Early partial record and notation

The first partial notes identified two routes: strengthen the bad-scale selection to obtain r/lambda^N -> 0, and examine exact p-energy on a second spatial scale. They explicitly left growing-box bounds unpaid. The resolution is to retain the **growing fitting parameter** at a larger radius and apply a small-solution theorem on an inscribed ellipsoid. No boundedness of the original normalized functions on enlarged boxes is claimed. The energy route is recorded in Section 6.

Write Z_eta(z,H;P) for the Euclidean cylinder with axis N=P/|P|, axial radius H and transverse radius sqrt(eta)H. A fit means

    |u(z+h)-u(z)-P.h| <= eta H,   h in Z_eta(0,H;P).

Goodness at parameter eta means existence of a nonzero P with this property. It need not be monotone in eta. Every cylinder used below lies in the domain of the same actual solution.

## 1. Uniform small-solution input

For 0<=e<=1, 0<=b<=1, gradient q=(q_x,q_t), and symmetric matrix X, put

    v=1+e b q_t,
    Q=e b²|q_x|²+v²,
    F_{e,b}(X,q)=X[(b q_x,v)] + Q(tr_x X+e X_tt).             (1)

This includes both parameter endpoints as polynomial operators. It is independent of position and value, and is elliptic in X everywhere: its matrix is an outer product plus Q diag(I,e).

On |q|<=1/8 its quadratic form on (xi,s) is

    (b q_x.xi+v s)²+Q(|xi|²+e s²),

where v>=7/8, Q>=49/64, and |b q_x|<=1/8. This bounds |xi|²+s² above and below by positive dimension constants. On |X|,|q|<=1/8 the first two derivatives of F also have common bounds. All the operators vanish at X=0.

Savin, *Small Perturbation Solutions for Elliptic Equations*, Theorem 1.3, applies. Its assumptions are global ellipticity in X and smooth uniform ellipticity only near zero jets; it does **not** assume small gradients of the unknown solution. The needed uniformity is not inferred merely from the theorem's words “depending on F”: Proposition 4.1 and its proof, PDF pp. 15–17, choose the quadratic-improvement radius from the local C² bound K, jet-neighborhood radius, dimension and ellipticity constants, and run the contradiction over varying F_k with these bounds. Consequently there exist sigma_n>0 and rho_n in (0,1/8) such that every continuous viscosity solution of any (1) on B1 with norm <=sigma_n is C² on B1/2, with gradient and Hessian bounded by rho_n. A stronger C^{2,alpha} conclusion is available but unnecessary here.

We also need the proportional consequence. Suppose w solves F_{e,1}=0 and A=||w||_B1<=sigma_n. For A>0 put b=A/sigma_n and W=w/b. Since the operator is linear in X, W solves F_{e,b}=0 and has norm sigma_n. Therefore

    ||Dw||_B1/2 + ||D²w||_B1/2 <= C_n A.                    (2)

A=0 is immediate. One uniform threshold is used for the whole b-family. No original gradient is divided out.

## 2. Actual-p cylinder theorem

**Theorem A.** For every integer n>=2 and m>0 there exist d_*(n,m)>0, k_*(n,m)>0 and C_*(n,m)<infinity with the following property. Let p>=3 be finite, e=1/(p-2), H>0, and P a vector of length c>=m. Let u be a continuous weak p-harmonic function on an open neighborhood of Z_eta(z,H;P). Assume

    0<eta<=d_* e,
    |u(z+h)-u(z)-P.h|<=eta H on Z_eta(0,H;P).               (3)

In coordinates with P=c e_n, set

    T_e=diag(sqrt(e)I_{n-1},1),
    L=(H/4)sqrt(eta/e),    E_L=z+L T_e B1.

Then u is C² on E_{L/2}, its gradient there is nonzero, and throughout that ellipsoid,

    |D_perp u|<=C_* sqrt(eta),
    |D_n u-c|<=C_* sqrt(e eta),
    ||T_e D²u T_e||<=C_* e/H.                              (4)

At z put P_new=Du(z). For every 0<lambda<=e and 0<r<=k_*L,

    sup_{h in Z_lambda(0,r;P_new)}
      |u(z+h)-u(z)-P_new.h| <= C_* e r²/H.                 (5)

Thus lambda is good if also C_* e r/H<=lambda.

No differentiability, nonvanishing, gradient modulus, energy-mass bound, or curvature sign of u is assumed. The nonzero vector in (3) is a **value-fit slope**.

**Proof.** Translate and rotate. Choose d_*<=1. E_L lies strictly inside the fitted cylinder: its axial radius is <=H/4 and its transverse radius is H sqrt(eta)/4. Define w on B1 by

    u(z+L T_e y)=u(z)+c L y_n+c e L w(y).                  (6)

Then

    ||w||_B1 <= eta H/(c e L)=(4/c)sqrt(eta/e)=:A.          (7)

Choose d_* so A<=sigma_n. At nonzero physical test gradients, the weak p-equation has viscosity form

    D²u[Du]+e |Du|² Delta u=0.                             (8)

Weak-to-viscosity equivalence is the standard p-Laplace result recorded in Julin–Juutinen, Definitions 2.1–2.3 and its introduction. At zero physical gradient (8) has both sides zero; thus these continuous test inequalities also hold there. No division by |Du| is made.

For a test in (6), the physical gradient and Hessian are

    c(sqrt(e)D_xw,1+e w_t),
    (c/L)[D_xxw, sqrt(e)D_xtw; sqrt(e)D_txw,e w_tt].

Equation (8), divided by the positive c³e/L, is exactly F_{e,1}(D²w,Dw)=0. This polynomial jet identity is also a valid viscosity transformation. Section 1 proves (2) and the absolute derivative bounds <=rho_n. In particular D_n u>=c(1-rho_n)>c/2. The first two estimates (4) follow from (2),(7). Also

    T_e D²u T_e=(c e/L)D²w,
    (c e/L) C_n A=16 C_n e/H,

which proves the last estimate.

Let N_new=P_new/|P_new|. The formula for the physical gradient and |Dw|<=rho_n give |T_e^{-1}N_new|<=C_n. For h=s N_new+v with |s|<=r and |v|<=sqrt(lambda)r,

    |T_e^{-1}h|<=C_n r+sqrt(lambda/e)r<=C'_n r.             (9)

Choose k_* sufficiently small that the segment from z to z+h stays in E_{L/2}. Taylor's theorem, the Hessian estimate and (9) prove (5). P_new is nonzero, so (5) is precisely the claimed good fit. This proves A.

The constants are independent of p, but the hypothesis and ellipsoid retain e explicitly. This is not a uniform C¹ estimate on a fixed Euclidean ball.

## 3. A single larger fit excludes high viscosity

**Corollary B.** Let e_i in (0,1], lambda_i->0, tau_i=e_i/lambda_i->infinity, and let u_i be actual p_i-harmonic functions, p_i=2+1/e_i. Let z_i,r_i be centers and positive radii, with lambda_i bad at (u_i,z_i,r_i). Suppose kappa_i>=1, kappa_i/tau_i->0, and there are slopes Q_i with |Q_i|>=m>0 giving fits at

    H_i=tau_i² r_i,     eta_i=kappa_i lambda_i.              (10)

Then such a sequence cannot exist.

**Proof.** eta_i/e_i=kappa_i/tau_i->0, so A applies. Its ellipsoid has

    L_i/r_i=(1/4)tau_i^(3/2)sqrt(kappa_i)->infinity.

Use (5) at r_i, since lambda_i<=e_i eventually. The error divided by lambda_i r_i is at most

    C_* e_i r_i/(lambda_i H_i)=C_*/tau_i ->0.

This makes lambda_i good, contradicting its choice. No compactness on a box of width sqrt(tau_i) was assumed. The growing value error eta_i H_i was used explicitly; its second normalization has small oscillation.

## 4. Running maxima really supply the larger fit

This is a conditional application to specified selection data, not an assertion that arbitrary p-approximating families have already been put in that selection.

Let G be bounded and D(z)=dist(z,partial G). Let b(s), 0<s<=s_*, be the supremum of bad parameters over a family of actual p-harmonic functions, centers in G and radii <=sD(z). Suppose b(s)->0 and b has no power bound. The family need not share p. The pinned running-maximum operation, strengthened using its unbounded quotient, gives gamma_i->0, s_i->0 such that

    b(s)/s^gamma_i <=2 b(s_i)/s_i^gamma_i, s_i<=s<=s_*,
    b(s_i)/s_i^gamma_i >=i,
    b(s_i)/4<lambda_i<=b(s_i),
    r_i<=s_i D(z_i),                                      (11)

with lambda_i bad for u_i. All suprema may be approximated; their attainment is unnecessary. For every fixed N and all large i,

    s_i/lambda_i^N <=(4/i)^N s_i^(1-N gamma_i)->0.            (12)

Suppose this selected branch has e_i<=1 and tau_i=e_i/lambda_i->infinity. Put

    R_i=tau_i²<=lambda_i^(-2),
    kappa_i=K_0(4R_i)^gamma_i,
    eta_i=kappa_i lambda_i,                               (13)

where K_0>max(8,Lambda) is fixed; Lambda is the base good-fit multiplier below. For Lambda=32 take K_0=64.

By (12), R_i s_i->0. For centers within 2R_i r_i the distance to the boundary is >=D(z_i)/2 eventually. Every radius <=R_i r_i is admissible and

    beta_{u_i}(z,r)<=b(4R_i s_i)
       <=8 lambda_i(4R_i)^gamma_i<eta_i.                   (14)

Thus eta_i is good at all those centers and radii. It tends to zero since eta_i<=C lambda_i^(1-2gamma_i). It is **not** replaced by the fixed multiple Lambda lambda_i on growing boxes. Also

    kappa_i/tau_i=K_0 4^gamma_i tau_i^(2gamma_i-1)->0.        (15)

For the nonzero slope required in B, assume explicitly that a base good Lambda lambda_i fit P_i exists at radius r_i with

    0<c_*<=|P_i|<=C_*<infinity.                             (16)

Compare it with an eta_i-fit Q_{i,0} at the same radius. Their common inscribed ball of radius sqrt(Lambda lambda_i)r_i gives

    |P_i-Q_{i,0}|<=C_Lambda kappa_i sqrt(lambda_i)->0.        (17)

For two eta_i-fits at concentric H,H', H<=H'<=2H, evaluation on the common inscribed ball gives directly

    |Q-Q'|<=3sqrt(eta_i).                                  (18)

This vector estimate needs no lower bound on the slopes' norms. Chain dyadic radii from r_i to R_i r_i, with one final ratio <=2. The resulting coarse slope Q_i satisfies

    |Q_i-P_i|<=C kappa_i sqrt(lambda_i)
               +C sqrt(eta_i)(1+log R_i)->0.                (19)

Indeed kappa_i<=C lambda_i^(-2gamma_i), and log R_i<=2log(1/lambda_i). A positive power of lambda beats the logarithm because gamma_i->0. Thus |Q_i|>=c_*/2 eventually. Equations (10),(15) and Corollary B contradict lambda_i being bad.

**Conclusion:** every actual-p sequence satisfying (11),(16), with lambda_i->0, is excluded on its e_i/lambda_i->infinity branch. Only concentric larger fits were necessary. The larger error parameter, domain availability and nonzero coarse slope have all been paid.

## 5. What this does and does not prove about gradients

In source-width coordinates

    u(z+r(sqrt(lambda)x,t))=u(z)+rc(t+lambda V(x,t)),

the exact equation is

    D²V[(D_xV,1+lambda V_t)]
     +(e/lambda)Q(Delta_xV+lambda V_tt)=0,
    Q=lambda|D_xV|²+(1+lambda V_t)².                       (20)

The vanishing ratio uses the stipulated homogeneous Liouville theorem once its fits and compactness are supplied. Completed I236 handles a finite positive ratio under its exact fit contract. Section 4 excludes the infinite ratio by an actual finite-p estimate. It does not pass (20) to Delta_x V=0.

This closes the specified high-viscosity branch **for an admissible nonzero selected sequence**. It does not prove that every p-family admits that sequence. The pinned source obtained uniform qualitative flatness and nonzero fitted slopes using the exact infinity equation and a linear lift. That lift does not preserve the p-equation. No replacement of those prerequisites is proved here. Uniform value convergence to v and inf|Dv|>0 do not themselves prove (16) at arbitrarily tiny selected radii, or b(s)->0 uniformly over approximants.

The still-unsubmitted full target is: for each n,m,M,K, positive constants C,theta and p0 such that for every p>=p0, every infinity-harmonic v on B1 with

    m<=|Dv|<=M,     [Dv]_{C^{0,alpha_n}(B1)}<=K,

and every p-harmonic u_p on B1,

    ||Du_p-Dv||_B1/2 <= C (||u_p-v||_B1+1/p)^theta.

No such theorem is asserted. The exact unpaid task is deriving a noncritical qualitative/selection input from these hypotheses without assuming a p-uniform C¹ modulus. If critical selected slopes cannot be excluded, they require a separate argument.

A narrower standard consequence is available: if m<=|a|<=M and ||u_p-a.x-b||_B1<=delta<=c(n,m)/p, normalize on a fixed-longitudinal-radius e-ellipsoid centered at each x in B1/2. Its oscillation is O(delta/(|a|e)), so (1),(2) give

    ||Du_p-a||_B1/2<=C(n,m,M)sqrt(p)delta.

This assumes only values, not gradient equicontinuity. It is a small-perturbation corollary, not the main nomination. The known general value rates do not meet its smallness threshold.

## 6. Independent energy route and counterchecks

### 6.1 Energy alone

In (6) the exact p-density, after removing c^p and the Jacobian, is

    Q^{p/2}=[e|D_xw|²+(1+e w_t)²]^{p/2}.

On bounded first jets, as e->0, it tends to exp(w_t+|D_xw|²/2). Without a bounded first-jet range this gives neither a uniform flux integral nor passage of the weak equation on growing domains. The longitudinal Hessian of the density has no global uniform positive lower bound near zero physical gradient. The earlier weighted excess estimate also leaves uncontrolled relative p-flux mass. The energy route alone is insufficient. Theorem A first obtains the first-jet bound from the actual PDE; subsequent local energy coercivity is no longer the missing step.

### 6.2 Infinite-viscosity PDE and exact fits

V(x,t)=sin t solves Delta_x V=0 and satisfies the entire all-center/all-radius fit contract with p=q=0 and C0=1. It is nonaffine. It solves no finite-positive-tau G_tau equation. It is not asserted to arise from a selected actual p-sequence. Sections 2–4 prevent a selected nonzero sequence satisfying the stated growing-scale constraints from supporting that obstruction.

### 6.3 Actual p-harmonic local temporal modes

Even actual p-solutions show why fixed-box information is insufficient. In two physical dimensions let e_i->0, tau_i->infinity, lambda_i=e_i/tau_i, p_i=2+1/e_i, and set

    a_i=(p_i-2)/(p_i-1)=1/(1+e_i),     D_i=tau_i,
    u_i(X,T)= {[(D_i+T)²+X²]^(a_i/2)-D_i^a_i}
              /(a_i D_i^(a_i-1)).                         (21)

This is a radial p-harmonic fundamental solution with pole (0,-D_i), after value and amplitude normalization. Direct radial differentiation gives the p-equation from (p_i-1)(a_i-1)+1=0. Its gradient at the origin is e_T. It can be extended to higher dimensions by adjoining inactive coordinates; the active radial dimension stays two.

On every fixed compact source-coordinate set,

    [u_i(sqrt(lambda_i)x,t)-t]/lambda_i -> -t²/2.            (22)

The quadratic terms after normalization are

    x²/(2D_i)+(a_i-1)t²/(2D_i lambda_i)
       =x²/(2tau_i)-t²/[2(1+e_i)].

The pure temporal cubic remainder divided by lambda_i is O(1/tau_i), since the third derivative contains a_i-1=O(e_i); mixed and higher transverse remainders are smaller. Taylor's formula on |T|<=D_i/2 gives uniformity on each fixed set.

This does not contradict B: the pole is at distance tau_i, whereas its required coarse scale is tau_i². No neighborhood of that coarse cylinder is available. Nor is (21) a counterexample to gradient convergence: on every fixed physical ball its actual gradients converge to e_T. Its limiting temporal quadratic lacks the global linear fit bound. It verifies that local actual-p equations alone cannot remove temporal modes; the selected domain and fit information are essential.

## 7. Verdict and contribution limits

The candidate is the larger selected cylinder with its growing parameter, an inscribed e-ellipsoid, and uniform small-jet regularity improving the original bad fit. It uses the finite-p equation and pays the previously missing enlarged-domain estimate under explicit selection hypotheses. It is not a reinterpretation of finite-tau affinity and does not assume the desired C¹ modulus.

Savin's small-solution theorem is established prior art. The same-center vector comparison and strengthened maximum are elementary or stipulated operations. An independent contribution gate must decide whether their combination meets this project's substantiality standard. No tenth finding is declared. The full p-gradient theorem remains unpaid for the reasons in Section 5; no actual counterexample to it is provided.
