# I220 — quantitative Coulomb/Riesz construction

**Analytic conclusion: complete proposed theorem, submitted to the parent gates.** This is new to this project; priority over the literature is not asserted. The fractional exponent and general oscillation mechanism already occur in a different two-marginal example (Carioni et al., Example 4.6). The additional bridge proved here concerns the pinned smooth five-component Coulomb/Riesz construction, including exact cyclic recovery. No numerical or code-based evidence is used.

## 1. Fixed source and regularity convention

Fix d>=2 an integer and s>0. Accept the pinned family-373 manuscript, particularly Lemma 3.1, Proposition 4.1, Lemma 4.2, Section 5 and Theorem 7.1. Write c_s(x,y,z)=|x-y|^{-s}+|x-z|^{-s}+|y-z|^{-s}. Constants may depend on d,s and the fixed construction; no uniformity in the bump or component separation is claimed.

Shrink the common ball if necessary and fix Q=(-a,a)^d with closure inside it. Choose

    b(r)=exp(-1/(a^2-r^2)) for |r|<a, and b(r)=0 otherwise;
    g(x)=C product_i b(x_i), normalized by integral g^2=1;
    nu=f dx=g^2 dx.

Then f is bounded by M, positive throughout Q and zero outside Qbar; nu is a product probability. Set H_1=Y_1,H_2=W_1,H_3=Y_2,H_4=W_2,H_0=Id, K_j=H_j(Qbar), D_j=H_j(Q), K=union K_j and D=union D_j. The five K_j are disjoint compact sets, separated by delta_K>0. All H_j extend smoothly as diffeomorphisms near Qbar and have bounded derivatives and bi-Lipschitz constants there. The marginal is exactly

    mu=nu/3+(1/6) sum_{j=1}^4 (H_j)#nu.

The source's smoothness proof applies to this g. Each outer square root is g(H_j^{-1}(y))|det DH_j^{-1}(y)|^{1/2}, smoothly zero-extended, since its support is compactly contained in H_j(B). Disjointness of the five supports gives smooth rho and sqrt(rho). Cube corners cause no issue because b is flat at its endpoints. There is no positive lower bound on f up to the boundary.

Let u be the supporting potential and put R(x,y,z)=c_s(x,y,z)-u(x)-u(y)-u(z)>=0 on K^3. For Borel T_2,T_3 preserving mu individually, set Delta=integral c_s(x,T_2x,T_3x)dmu-E_s(mu). The source gives E_s(mu)=3 integral u dmu, so Delta=integral R dmu, including +infinity. Preservation implies values in K for mu-a.e. input.

All complexities use **unweighted Lebesgue** measure:

    V_Q=|DT_2|(Q)+|DT_3|(Q),
    S_Q=[T_2]_{W^{t,p}(Q)}^p+[T_3]_{W^{t,p}(Q)}^p,
    [F]_{W^{t,p}(A)}^p=integral_{A x A}|F(x)-F(y)|^p/|x-y|^{d+tp} dx dy.

Here 0<t<1,1<=p<infinity,alpha=tp. Define V_D by summing variation on the five D_j, and S_D by summing their pth seminorms. Each D_j is a Lipschitz domain. Since f>0 on Q, changes on a mu-null subset of Q are also Lebesgue-null there.

## 2. The theorem

For every preserving Borel pair, with positive constants depending only on the fixed data (also t,p for the fractional assertion),

    Delta >= c(1+V_Q)^(-2),                                    (B)
    Delta >= c(1+S_Q)^(-2/alpha), if 0<alpha<1.                (F)

Only the central complexity of T_2 is actually needed. Consequently these inequalities hold with the larger componentwise or global complexities.

For each n>=1 there is a Borel T_n preserving mu, with T_n^3=Id mu-a.e., such that

    0<Delta(T_n,T_n^2)<=C n^(-2),
    |DT_n|(R^d)+|D(T_n^2)|(R^d)<=C n,
    [T_n]_{W^{t,p}(R^d)}^p+[T_n^2]_{W^{t,p}(R^d)}^p<=C_{t,p}n^alpha
       if 0<alpha<1.

These representatives are bounded and compactly supported; their L^1 and L^p norms are uniformly bounded. T_n^2 is actual composition. All upper estimates hold on D, both componentwise and for its full seminorm. Hence for sufficiently large budgets B the best gap is comparable to B^{-2} under a variation budget and to B^{-2/alpha} under a pth-fractional-energy budget. These are matching powers, not exact leading constants. For the seminorm rather than its pth power the exponent is -2/t.

If T_2 is continuous on Q, belongs to W^{1,1}_{loc}(Q), or has finite W^{t,p}(Q) seminorm with tp>=1, then the stronger conclusion is

    Delta>=kappa/3>0.                                        (T)

Thus globally smooth or integer-Sobolev near-optimal maps for this fixed marginal do not exist. The fractional jump threshold is tp<1, not tp<d.

## 3. Quantitative calibration

For a positive outer coordinate y, source Lemma 3.1 minimizes F_k(x,y,z)=c_s(x,y,z)-u_0(x)-v_k(z) in (x,z), with minimizer (X_k(y),Z_k(y)). Its Hessian is positive definite on a convex product of small balls. Take a common positive lower eigenvalue lambda on the compact subproducts needed here. Taylor along a segment gives

    R(x,y,z)>=(lambda/2)(|x-X_k(y)|^2+|z-Z_k(y)|^2)            (3.1)

on Q x Y_k(Qbar) x W_k(Qbar). Section 7 supplies the same argument for d,s. No constrained boundary minimizer is substituted.

For y=Y_k(v),z=W_k(t), let L_k=Lip(W_k^{-1}|W_k(Qbar)). Since |x-t|<=|x-v|+L_k|z-W_k(v)|, (3.1) controls |x-W_k^{-1}(z)|^2 with coefficient lambda/(4 max(1,L_k^2)). This separately verifies the two negative branches; the source Hessian is not simply assumed to hold with either outer variable fixed.

On each forbidden compact component product, R has a positive minimum: it is lower semicontinuous, tends to infinity at collisions, and its certified contact set misses that product. There are finitely many products. Let kappa>0 be the minimum of these minima when the first coordinate is central. In particular R>=kappa when the first two coordinates are central. With D_Q=diam(Q), put

    a_0=min{lambda/2, min_k lambda/(4 max(1,L_k^2)), kappa/D_Q^2}>0.

Allowed and forbidden cases together imply, for x in Q,y in K_j,j>=1,z in K,

    R(x,y,z)>=a_0|x-H_j^{-1}(y)|^2.                           (3.2)

A qualitative contact-set theorem alone would not imply this quadratic estimate; the source's uniform convexity is essential.

## 4. Route A: branch domination at a chosen scale

Let S_j={x in Q:T_2(x) in K_j}, m_j=nu(S_j). These partition Q modulo null sets. For j>=1 set F_j=H_j^{-1} composed with T_2 on S_j and E_j=integral_{S_j}|F_j(x)-x|^2 dnu. Exact preservation gives

    beta_j=(F_j)#(nu restricted to S_j)<=nu/2.                (4.1)

Indeed for every Borel A subset Qbar,

    (1/3)nu({x in S_j:F_j(x) in A})
       <=mu(T_2^{-1}(H_j(A)))=mu(H_j(A))=nu(A)/6.

Incoming mass from other source components only strengthens this inequality. Merely matching component totals would not give it. From (3.2),

    Delta>=(a_0/3)sum_{j>=1}E_j,
    Delta>=(kappa/3)m_0.                                    (4.2)

If m_0>=1/2, the gap is at least kappa/6. Otherwise at least one of the four outer sets has m_j>=1/8. Fix it and write S,m,E,beta. Extend chi_S by zero to R^d. Choose a fixed nonnegative smooth unit-ball mollifier eta with integral 1. Let phi=eta_r*chi_S and L_eta=||grad eta||_1, so 0<=phi<=1 and Lip(phi)<=L_eta/r. Set e=integral|phi-chi_S|dnu. Then (4.1) yields

    integral phi d(nu|S-beta)>=m/2-(3/2)e.                   (4.3)

The transport defining beta gives

    |integral phi d(nu|S-beta)|
        <=(L_eta/r)integral_S|x-F_j(x)|dnu
        <=(L_eta/r)sqrt(m E).                                (4.4)

If e<=m/6, these imply E>=m r^2/(16L_eta^2)>=r^2/(128L_eta^2).

The two regularity estimates, with all boundary terms retained, are as follows.

* For BV, take a globally Lipschitz target cutoff ell_j equal to 1 on K_j and 0 on every other K_i, with Lip<=L=2/delta_K. Then chi_S=ell_j(T_2) a.e. on Q. The chain rule gives |Dchi_S|(Q)<=L|DT_2|(Q); zero extension adds at most H^{d-1}(partial Q). Thus its full-space variation is at most P=L|DT_2|(Q)+H^{d-1}(partial Q). The BV translation estimate gives ||eta_r*chi_S-chi_S||_1<=C_eta r P.
* For fractional energy, |chi_S(x)-chi_S(y)|=|chi_S(x)-chi_S(y)|^p<=L^p|T_2(x)-T_2(y)|^p. Hence its W^{alpha,1}(Q) seminorm is at most L^p[T_2]_{W^{t,p}(Q)}^p. Zero extension adds at most

      B_{Q,alpha}=2 integral_Q integral_{R^d\Q}|x-y|^{-d-alpha}dy dx<infinity.

  The inner integral is bounded by C dist(x,partial Q)^{-alpha}, integrable exactly in this argument for alpha<1. Put P=L^p[T_2]^p+B_{Q,alpha}. Directly from the Gagliardo integral,

      ||eta_r*chi_S-chi_S||_1
        <=||eta||_infty r^{-d}integral_{|h|<r}||chi_S(.+h)-chi_S||_1 dh
        <=||eta||_infty r^alpha [chi_S]_{W^{alpha,1}(R^d)}.

Both cases give e<=M C_eta r^beta P, where beta=1 or alpha. Choose

    r=min{1,[48 M C_eta(1+P)]^{-1/beta}}.

Then e<=1/48<=m/6. Since 1+P<=C_0(1+complexity),

    r>=min{1,(48 M C_eta C_0)^(-1/beta)}(1+complexity)^(-1/beta).

Together with (4.2)--(4.4) this proves (B),(F); one possible lower constant is the minimum of kappa/6 and a_0 times the square of the last fixed coefficient divided by 384L_eta^2. This specifies all constants in terms of the fixed geometry, Hessian, f, cube and mollifier. Numerical values for the source's nonnumeric neighborhood choices are not claimed. No positive lower bound for f is required in this estimate.

## 5. Route B: exact conditional-CDF cycles

Write nu=nu_1 tensor nu_perp. Divide (-a,a) into n equal **geometric** intervals I_l of length h=2a/n. Define

    q_l(r)=nu_1((left(I_l),r))/nu_1(I_l),
    m_l=q_l^{-1}(1/2).

The CDF is continuous and strictly increasing, with endpoint values 0,1, and smooth in the interior. Split I_l into I_{l,1}=(left,m_l), I_{l,2}=(m_l,right). The two pieces have equal nu_1 mass, not necessarily equal length. On A_k=union_l I_{l,k} x (-a,a)^{d-1}, leave the transverse coordinates fixed and set

    (F_1(x))_1=q_l^{-1}(2q_l(x_1)),
    (F_2(x))_1=q_l^{-1}(2q_l(x_1)-1).

Their inverses from full cells to half-cells are

    (G_1(u))_1=q_l^{-1}(q_l(u_1)/2),
    (G_2(u))_1=q_l^{-1}((q_l(u_1)+1)/2).

All cell/half boundaries have nu-measure zero and can be assigned arbitrary values. On full-measure sets,

    F_k G_k=Id, G_k F_k=Id,
    (F_k)#(nu|A_k)=nu/2, (G_k)#nu=2nu|A_k,
    |F_k(x)-x|<=h, |G_k(u)-u|<=h.                             (5.1)

Proof: on each cell q_l sends its normalized law to uniform (0,1); doubling either half-uniform interval gives uniform, with half the original unnormalized mass. Product structure preserves nu_perp. Sum over cells. This verifies the pushforwards directly, without assuming a quantitative Borel isomorphism.

Define T=T_n by

    T(v)=Y_k(F_k(v))             for v in A_k;
    T(Y_k(u))=W_k(u)             for u in Q;
    T(W_k(u))=G_k(u)             for u in Q.                  (5.2)

Disjointness of the physical components makes this unambiguous. A cycle is v -> Y_k(u) -> W_k(u) -> v with u=F_k(v),v=G_k(u), so T^3=Id mu-a.e. For exact preservation: central mass nu|A_k/3 goes to (Y_k)#nu/6, which goes to (W_k)#nu/6, which goes back to nu|A_k/3. Sum over k. Thus T#mu=mu and (T^2)#mu=mu.

For global representatives, define T=0 outside K and on unresolved boundaries, and impose T(0)=0. Further exceptional values may be changed to 0 on null sets. Such changes affect T and T^2 only on mu-null sets, because the preimage of a mu-null set under a preserving map is null. They preserve the cycle and pushforwards a.e. and make the **actual composition T^2 zero outside K**. Omitting T(0)=0 could leave T^2 a nonzero constant outside K and invalidate its global L^p assertion.

### 5a. Cost and cancellation

For each u,k, R(u,Y_k(u),W_k(u))=0 and the derivative in the central variable vanishes, by the source stationarity (also by interior nonnegativity). Let H_* bound the central Hessian norm of R on the compact collision-free product Qbar x Y_k(Qbar) x W_k(Qbar). Since the segment between u,v stays in Qbar,

    0<=R(v,Y_k(u),W_k(u))<=(H_*/2)|v-u|^2<=(H_*/2)h^2.

Every graph triple from (5.2) is a cyclic permutation of one of these. Both c_s and the potential sum are symmetric. Thus Delta(T,T^2)<=(H_*/2)(2a/n)^2. Physical coordinates in each triple stay in distinct K_j, separated by delta_K; there is no approach to a collision. Strict positivity follows from source nonattainment or the lower bound.

### 5b. BV, jumps and flat endpoints

Each scalar F_k and G_k is increasing on each defining interval, with image inside I_l. Its variation on that interval is at most h, irrespective of the size of its derivative. It is smooth away from endpoints and has one-sided endpoint limits; its variation is precisely the difference of those limits. Thus flat bump endpoints do not cause unbounded variation.

For a coordinate map (r,x_perp)->(f_lk(r),x_perp), interior variation on its box is bounded by a fixed cross-sectional area times h plus a fixed constant times box volume. Composing with fixed H_j and H_j^{-1} multiplies variation by fixed constants (BV chain rule and change of variables). The actual powers are

    on A_k:     T=Y_k F_k,             T^2=W_k F_k;
    on Y_k(Q):  T=W_k Y_k^{-1},        T^2=G_k Y_k^{-1};
    on W_k(Q):  T=G_k W_k^{-1},        T^2=Y_k W_k^{-1}.

Summing the interior estimates over the 2n central boxes is O(1). Central cell/half interfaces number at most 2n-1, each of area (2a)^{d-1}, with uniformly bounded jumps, so their variation is O(n). Outer cell interfaces are fixed-diffeomorphic images of n-1 hyperplanes, have uniformly bounded areas per interface, and bounded jumps, again O(n). In fact the G_k jumps have height at most h, but this improvement is unnecessary. The five fixed support boundaries have finite perimeter and bounded traces, adding O(1) for zero extension. Pointwise null modifications change none of these variation estimates. This proves the global Cn bound for T and its actual square.

No bound on (q_l^{-1})' at 0 or 1 is used. The argument does not justify Lipschitz regularity. It also does not apply without extra work to an arbitrary nonproduct bump: conditional quantiles would depend on transverse coordinates, whose variation has not been bounded. The theorem uses the specific product bump of Section 1.

### 5c. Fractional and support-crossing terms

For U=T or T^2, ||U||_infty and ||U||_1 are uniformly bounded and |DU|(R^d)<=Cn. For any translation z,

    integral |U(x+z)-U(x)|^p dx
       <=(2||U||_infty)^{p-1}min{|z||DU|(R^d),2||U||_1}.

Use the translation formula for the full-space Gagliardo integral and split radial integration at 1/n. The integral of r^{-1-alpha}min{nr,1} is

    n^alpha[1/(1-alpha)+1/alpha], for 0<alpha<1.

This bounds all interactions, including across physical components and across support boundaries. Restricting to D or summing over its components only decreases it. The L^p terms remain bounded. Hence both maps really belong to global W^{t,p} for tp<1.

## 6. Topology and the critical fractional threshold

If T_2 is continuous on Q, it maps all of Q into K: a value outside the closed K would persist on an open set of positive nu-mass. Connectedness puts its image in one K_j. The entire central mass 1/3 cannot fit in an outer component of mass 1/6; hence j=0 and (4.2) gives Delta>=kappa/3.

For W^{1,1}_{loc}, compose T_2 with the five Lipschitz labels. Each is a W^{1,1}_{loc} characteristic function. Differentiating chi^2=chi gives grad chi=0 a.e.; connectedness makes its label constant. The same mass argument applies.

For finite W^{t,p} with alpha=tp>=1, each characteristic label has finite integral of |chi(x)-chi(y)|/|x-y|^{d+alpha}, since the numerator equals its pth power and is bounded by L^p|T_2(x)-T_2(y)|^p. Comparison on bounded Q reduces to exponent 1. Here is direct rigidity at that exponent. For Q' compactly contained in Q and epsilon small,

    ||grad(eta_epsilon*chi)||_{L^1(Q')}
      <=C epsilon^{-d-1} integral_{|z|<epsilon}integral_{Q'}
            |chi(x-z)-chi(x)| dx dz
      <=C integral_{|z|<epsilon}integral_{Q'}
            |chi(x-z)-chi(x)|/|z|^{d+1} dx dz ->0.

Absolute continuity of the finite integral gives the last limit. Therefore the distributional gradient of chi vanishes locally, so chi is constant on connected Q. Again only the central label is possible, proving (T), including tp=1.

The recovery maps also have genuine separated-target jumps on smooth patches of their central half-interfaces. Local normal-coordinate integration gives the divergent factor integral_0^epsilon r^{-alpha}dr when alpha>=1. Thus the threshold appears both in general rigidity and in the constructed sequence.

## 7. Sharpness and limits of the claim

For a sufficiently large variation budget B, choose n=floor(B/C); for a fractional-energy budget choose n=floor((B/C)^{1/alpha}), increasing the fixed C if necessary. This proves matching constrained powers. The lower bounds also imply V_Q(T_n,T_n^2)>=c n and S_Q(T_n,T_n^2)>=c n^alpha for large n. Thus an improved uniform lower exponent smaller than 2 or 2/alpha is impossible with these complexities. A larger exponent would be a weaker bound.

Elementary optimization also gives inf(Delta+epsilon V) comparable to epsilon^{2/3}, and inf(Delta+epsilon S) comparable to epsilon^{2/(2+alpha)} for small epsilon, for any of the stated complexity conventions. These concern infima, not existence of regularized minimizers, an exact leading coefficient, or a full Gamma-limit. The fractional penalty exponent is already known for another geometry. No weighted dmu dmu version is claimed: a flat bump precludes replacing Lebesgue and weighted energies by two-sided comparison.

Rejected overclaims: a contact set alone gives a quadratic residual; matching component totals gives exact pushforwards; smoothing preserving Borel maps preserves their marginals; inverse CDF derivatives of a flat bump are uniformly bounded; a componentwise estimate alone proves global fractional regularity; smooth near-optimal maps exist for the disconnected target; tp<d is the jump threshold; or this upper proof covers every arbitrary smooth bump. Each has been repaired or excluded above.

The two routes have different roles: route A controls every admissible pair by branch domination and displacement, while route B constructs exact cycles and controls both powers globally. Neither is a compactness-only positive gap. Under the displayed hypotheses the candidate does not fail analytically, so a speculative pivot is unnecessary. The parent still decides substantiality, priority and acceptance.
