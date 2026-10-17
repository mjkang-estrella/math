# Two temperature transitions for one radial pair potential on a common density interval

Myeongjin Kang; no affiliation. Original prose CC BY4.0. Third-party source statements retain their rights.

**Author status: full proof proposed for frozen R2T; independent proof and contribution review required. Counted=false.** Scope is exactly `original-scope.md`, SHA256 e595c73286a91733d95e3dc46800e1e51ed0af8d290490ffb93058815c5f79c2. No numerical evidence is used as a proof premise.

Write [B] for the pinned bounded radial-potential manuscript, identified in `inputs/radial-identities.json`. Its seven section files are all read. We use its thermodynamic/range/persistence operations, proving their transfer to the new core below. The divergent-core companion is not a proof premise. No assertion about the truth of the stipulated upstream theorems is being audited.

## 1. Core and two-level cluster geometry

Let p be the unit-separation packing constant of [B, foundations, f:packing]; its elementary proof establishes 0<p<infinity. Put A=3/(2p), Delta=10^-3, ell=exp(-t), s=exp(-6t), where t>1 will be fixed sufficiently large. Let I_s=[s,(1+Delta)s], I_ell=[ell,(1+Delta)ell]. Impose

2(1+Delta)s<ell, 2(1+Delta)ell<1.

Define psi_t:[0,infinity)→[0,t²] as follows: it is t² on [0,1] outside I_s union I_ell; it is zero on the middle closed third of each shell; on the two remaining shell thirds it interpolates linearly between these endpoint values. On [1,1+1/t] it decreases linearly from t² to0, and beyond1+1/t it is0. This is a single bounded continuous nonnegative radial core, supported in[0,2].

Call a pair good if its distance belongs to either shell. A set in which every distinct pair is good has at most16 particles. Indeed, the relation 'same particle or distance in I_s' is transitive on that set: two inner edges have endpoint distance less than ell, so a good endpoint pair must belong to I_s. Each equivalence class has at most4 particles. To see this, five points with all distances in [r,(1+Delta)r] would, after rescaling, give four difference vectors whose Gram matrix differs entrywise by at most 2Delta+Delta² from the matrix with diagonal1 and off-diagonal1/2. The latter has least eigenvalue1/2; the error operator norm is at most4(2Delta+Delta²)<1/2, forcing rank4 in R³, impossible. Representatives of distinct inner classes have all distances in I_ell; hence there are at most4 such classes. This proves16, including arbitrary configurations and possible coincident positions (coincident distinct labels are not good).

A configuration is called free if every pair at distance<1 is good. In a free configuration, joining pairs at distance<1 gives disjoint cliques: endpoints of a two-edge path have distance at most2(1+Delta)ell<1 and hence are joined. Thus each component has k inner classes and M particles with

1<=k<=4, k<=M<=4k.

One representative per whole component forms a1-separated packing, so there are at most M_L components in[0,L]³. This controls every mixed component, not only the extremal16-particle motif.

## 2. Stability and the transferred analytic framework

Fix the same nonnegative radial C¹ unit-integral kernel w as[B], supported in the unit ball; w_R(x)=R^-3 w(x/R). Consider the whole family

phi=psi_t-t sum_j alpha_j w_{R_j}, R_j>=1, alpha_j>=0, sum_j alpha_j<=A+1,

with finite or countable sums. Uniform convergence makes these bounded continuous radial potentials; they are nonpositive outside radius2.

Partition into half-open cubes of side b=1/4. The good-pair graph has clique number<=16. The weighted Motzkin-Straus argument gives at most15m²/32 good edges on any m vertices: a maximizing simplex weight can be moved from two nonadjacent positive vertices onto one, so a minimum-support maximizer is supported on a clique of size r<=16 and its value is at most(1-1/r)/2. Equal weights give the edge bound. A small cell has diameter<1, so at least m²/32-m/2 of its pairs have core value t². Consequently, with cell populations n_i,

U^{psi_t}>=D0 sum_i n_i²-B0 N, D0=t²/32, B0=t²/2.

The attraction cell-supremum matrix J has the same row bound as[B]: M0=c_b t(A+1), c_b=||w||_infinity(2/b+5)³. Thus even after arbitrary deletion of intercell core terms and permitted deletion/interpolation of attractions,

U>= (D0-M0/2) sum_i n_i²-B0 N.

Choose t so large that D0>=8M0 and c t>4(A+1), where c=1/13824. A cube of side L>=1 meets at most216L³ cells, and D0-M0/2>=t²/64. Therefore U>=c t² N²/L³-t²N/2. These are the exact margins needed below. All constants may depend on this one fixed t, but not on previous attraction ranges or the number of summands.

For clarity, the following consequences of the source proofs remain valid for this core, with the displayed changed constants:

(a) For every family member, the all-sequence canonical limit H_phi(beta,d)=-lim (t L³)^-1 log Z_{L,N}(beta), N/L³→d>=0, exists, is finite, convex continuous in d, and concave in beta>0. The joint convex pressure Q_phi satisfies

Q_phi(beta,h)=sup_{d>=0}(h d-H_phi(beta,d)),
H_phi(beta,d)=sup_h(h d-Q_phi(beta,h)) for d>0.

(b) For fixed t and parameter compacts, local cell second moments and exponential moments are uniform over the entire family, all finite regions and the stated deletions/interpolations. Tail attraction mass m changes pressure by at most C m.

(c) Define T_a Q(beta,h)=sup_u[Q(beta,h+beta a u)-beta a u²/2]. Active u are exactly maximizing densities in sup_d[h d-H(beta,d)+beta a d²/2], and lie in a common bounded interval on compacts, uniformly for 0<a<=2(A+1), also uniformly as t→infinity through admissible values. The transform is convex, 0<=T_aQ-Q<=C a, and at an active shifted point x=(beta,h+beta a u),

Q(x+(0,r))<=Q(x)+u r+r²/(2 beta a).

Every subgradient of Q at x has density coordinate u, and

partial(T_aQ)(beta,h)=conv union_{u active}{(e+a u²/2,u):(e,u) in partial Q(x)}.

(d) If phi_0 has reference range<=R0, R0>=2, and the total mass including a is<=A+1, then for R/R0 sufficiently large,

||Q_{phi_0-ta w_R}-T_a Q_{phi_0}||_D <= C_{D,t} sqrt(R0/R).

Here the threshold and constant are independent of all previous ranges and of positive a tending to0.

These are transfers of proofs, not applications of the old one-shell theorem to a new core without checking hypotheses. Detailed verification follows. For(a), the finite-volume lower canonical bound uses the new c and B0; the upper bound uses only 0<=psi_t<=t² and support<=2, so is unchanged. Superquadratic grand-count tails follow from c t>4(A+1). Separated reference boxes interact only attractively; the source integer-count adjustment proof of the canonical limit uses precisely this property and the two canonical bounds. Density convexity follows by mixing boxes, and pressure duality by the grand-count tail. No shell geometry occurs in those arguments.

For(b), condition on the outside of a small cell. Its energy contribution is >=(D0-J_ii/2)n²-B0 n-n G_i, G_i=sum_{j!=i}J_ij n_j. With u0=beta D0/4 and nG_i<=D0 n²/4+G_i²/D0, the conditional exponential moment is <=C2 exp(beta G_i²/D0). By weighted Cauchy-Schwarz and convexity, F_max=max_i E exp(u0 n_i²) satisfies

F_max<=C2 F_max^theta, theta=4M0²/D0²<=1/16.

Finite-volume finiteness precedes taking this maximum, using the global quadratic energy bound. Hence F_max<=C2^(1/(1-theta)) independent of volume. Differentiation along pair-interaction interpolation gives the bound (beta C1/2)sum_{ij}Jdiff_ij for log partition differences. This proves tail-mass continuity with the unchanged kernel row bound.

For(c), square completion in the density duality gives the transform formula. The objective is <=-beta(ct-a/2)d²+(|h|+beta t/2)d+1/t. This establishes attainment and the uniform maximizing-density bound, including uniformity in large t after division by beta t. Comparing u to u+r/(beta a) proves the parabola. The source exact compact-active-branch subgradient proof is purely convex and applies unchanged.

For(d), read[B, range] in full: delete reference interactions between boxes of side z≈sqrt(R0 R), aligned with the small-cell grid. The interpolation cost is O(R0/z); its proof uses only core support<=2, its supremum t², and the occupation estimate in(b). Kernel upper/lower row sums differ from their integral by O(z/R). The upper product grand sum is truncated using the quadratic canonical bound. For the lower bound, independent grand reference boxes at the active shifted field have mean density d_z bounded by(b), and

-u d_z+(1-epsilon)d_z²/2 >= -u²/2-epsilon d_z²/2,

epsilon=O(z/R).

No convergence of d_z to u is needed. Both bounds give O(R0/z+z/R), hence(d). All geometric facts about the microscopic shell have already been exhausted by the cell estimate. Thus the two-shell core satisfies the full framework, with no unstated phase or finite-volume mixing assumption.

## 3. Exact bare-core pressure from all cluster types

We prove locally uniformly in beta>0,h in R,

q^{(t)}(beta,h)=Q_{psi_t}(beta,h) → q_*(h)=p max{0,h,4h-9,16h-225}.   (3.1)

Fix beta>=beta_->0 and |h|<=H. For a free component with k inner classes and M particles, designate its root, a root for each inner class, and a partition into those classes. There are finitely many such types because M<=16. Integrating the whole root gives volume V=L³. Each of the k-1 other class roots is within O(ell) of it; each remaining particle is within O(s) of its class root. Thus a labeled type has volume at most

V C^{M-1} ell^{3(k-1)} s^{3(M-k)}.

One can sum all choices of roots and partitions rather than choose uniquely; this is a finite overcount. Splitting labels into unordered whole components cancels the global1/N! and leaves a factor1/K! for K components, along with finite type constants depending only on M,k. Therefore the free grand integral is bounded by

sum_{K=0}^{M_L} (V Theta_t(h))^K/K!,
Theta_t(h)=sum_{1<=k<=4, k<=M<=4k} C_{M,k} exp{t[M h-3(k-1)-18(M-k)]},

where all C_{M,k} are fixed positive finite constants; adding nonexistent types only enlarges the bound.

If h<=18, the exponent is maximized in M at M=k; maximizing k gives max(h,4h-9). If h>=18, take M=4k; maximizing k gives max(4h-54,16h-225). The maximum over all types is therefore max(h,4h-9,16h-225), since4h-54 is dominated. This equality also follows by retaining the valid extremal types, so no omitted intermediate component can change the leading pressure.

For a nonfree configuration let J be all labels incident to bad pairs (distance<1 outside the two closed shells). There are at least |J|/2 such pairs, each with energy t². Removing J leaves a free configuration; all other core terms are nonnegative. Summing over all possible removed label sets gives

Xi_{psi_t} <= exp[V exp(t h-beta t²/2)] Xi_free.

Exactly as in[B, initial], K!>= (K/e)^K and x(1-log x)<=1 imply the pressure upper limit <=p max(0,t^-1 log Theta_t)+1/t+t^-1 exp(tH-beta_-t²/2). This converges uniformly to(3.1).

For the lower bound use asymptotically optimal1-separated centers, slightly dilated to separation1+nu, repeated periodically with a boundary margin. At each center choose a root in a fixed ball of radius r<nu/16. The three component choices are:

- one root alone;
- four particles near a regular outer tetrahedron, all six edges in the middle third of I_ell;
- four inner tetrahedra, whose four distinguished roots form an outer tetrahedron.

For the third, first choose the three outer-root offsets in balls of radius delta ell about an outer tetrahedral pattern, and independently choose the three inner offsets in each of the four classes in balls of radius delta s about inner tetrahedral patterns. Fix delta sufficiently small relative to Delta. Since s/ell→0, all cross-class edges lie strictly inside the outer plateau for sufficiently large t; all within-class edges lie inside the inner plateau. The successive displacement coordinates have Jacobian1. Thus the relative configuration volume, bounded below by a fixed positive constant times its scale product, is respectively1, ell^9, ell^9 s^36. Their exponents are0,9,225. Every particle remains O(ell) from its component center. For large t, intercomponent distances exceed1+1/t, so these configurations have exactly zero core energy.

Assign unordered particle labels to the distinguishable centers, retaining one ordering inside each assigned set. The events are disjoint because center neighborhoods are disjoint; division by N! leaves the product1/(m!) per center. These finite factors vanish after division by t. First pass to infinite volume, then let center density tend to p and finally t→infinity. The three lower affine branches and the vacuum give(3.1), uniformly on the same parameter compact. This proves the bare pressure law.

## 4. Two separate triples in a single pressure diagram

Let D={0,p,4p,16p}, b_0=b_1=0,b_4=9,b_16=225. By square completion the ideal transform of(3.1) is

P_*(beta,h)=max_{m in{0,1,4,16}} L_m(beta,h),
L_m=p[m h-b_m+(3/4) beta m²].

The two parameters and active sets are

lambda_1=(1,-3/4), J_1={0,1,4};
lambda_2=(21/16,-27/16), J_2={0,4,16}.

At each parameter the three indicated planes equal0. The inactive values are respectively -45p and -45p/64. Thus there are disjoint small parameter balls on which the fourth plane has a uniform positive gap below P_* and all beta coordinates stay inside the respective frozen windows. Fix a common radius rho>0 small enough that the balls W_i(rho) have these properties, and larger compact neighborhoods for all forthcoming secants and shifted evaluations.

The slopes are v_m=((3/4)p m²,p m). Set

g_1=(21p/4,2p), g_2=(15p,2p).

In triangle(v_0,v_1,v_4), g_1 has weights(1/4,1/3,5/12). In triangle(v_0,v_4,v_16), g_2 has weights(11/16,1/4,1/16). Both are strictly interior. Let eta0>0 be the minimum over the two triangles and all unit z of max_{m in J_i}(v_m-g_i)·z. Let zeta0>0 be the minimum distance of g_i from each corresponding edge. Choose tau>0 with tau<min(p/16,eta0/4,zeta0/2). Then every choice w_m in closed B(v_m,tau), m in J_i, has a convex hull containing closed B(g_i,gamma), for gamma=eta0/2; and g_i is outside the hull of any two such balls. The support-function proof is immediate: max(w_m-g_i)·z>=eta0-tau>gamma; every point in a hull of two balls is within tau of the corresponding edge. Also

P_*(lambda)-P_*(lambda_i)-g_i·(lambda-lambda_i)>=eta0|lambda-lambda_i|,

because the maximum over all four planes dominates the maximum over the three planes equal at lambda_i.

Let P_1^{(t)}=T_A q^{(t)}. Framework2(c) and(3.1) give local uniform convergence to P_*, with maximizing shifts uniformly bounded for large t. If E_t bounds the bare-pressure approximation on the shifted compact, square completion gives

F_*(lambda,u)=max_m[L_m(lambda)-beta A(u-mp)²/2].

For lambda in W_i(rho), the unused plane has gap Delta_i>0. If u is active for P_1^{(t)}, F_*(lambda,u)>=P_*(lambda)-2E_t. For2E_t<Delta_i, one of the three active-set branches must realize this maximum; hence dist(u,{mp:m in J_i})<=2 sqrt(E_t/(beta_min A)).

At the shifted point x, every (e,u) in partial q^{(t)}(x) has |e|<=2E'_t/sigma by secants x±(sigma,0), since q_* is independent of beta. Here sigma>0 is fixed and E'_t→0 on an enlarged compact. The exact transform formula then places every active generator (e+A u²/2,u) within tau/2 of its corresponding v_m, uniformly for both neighborhoods. Fix one sufficiently large finite t such that, on each W_i(rho),

partial P_1=conv(partial P_1 intersect union_{m in J_i} closed B(v_m,tau/2)),
||P_1-P_*||<eta0 rho/16.   (4.1)

This is an exact statement about actual subgradients, not just convergence of ideal planes. All stability size requirements are imposed on this same t.

## 5. One physical attraction schedule preserves both triples

All following constants are chosen on one fixed compact containing both neighborhoods and the required shifted points. Let U_* bound active shifts for the entire family, and C_* bound pressure/transform Lipschitz constants on the necessary enlarged compact. Put beta_min>0 and beta_max<infinity for that compact. Choose k,l>0 with

k/(2 beta_min)+2C_* l/k<p/16,
S=beta_max U_*+k+l+1.

We record the source one-step argument in the form used here. Suppose on W_i(z) a convex P has its subdifferential generated by the three balls of radius r<tau around v_m, m in J_i; q is a physical family pressure; ||P-q||<=delta on the larger compact. If S a<z and2delta/(ka)<p/16, then T_aq has the same local generating statement on W_i(z-Sa), with radius

r^+=r+2delta/(la)+a U_*²/2.   (5.1)

Proof: at an active shifted point x for T_aq, every support (e,d) of P at y with |y-x|<=la obeys

|d-u|<=k/(2 beta_min)+2C_* l/k+2delta/(ka)<p/8

by the parabolic bound for q and comparison at x±(0,ka). Since the three density coordinates are at least p apart and r<tau<p/16, exactly one common group can appear throughout that neighborhood. Hence all subgradients of P there lie in that one ball. Secants from x to x+la z for arbitrary unit z transfer every subgradient of q(x) into its enlargement by2delta/(la). The transform adds (a u²/2,0), bounded by aU_*²/2. Taking the exact hull over active shifts proves(5.1). The argument applies to either triple using the SAME k,l,S,U_*.

Now choose R_1 sufficiently large, set R_n=R_1^(2^(n-1)), a_1=A, and a_n=R_n^-1/16 for n>=2. Define

phi_n=psi_t-t sum_{j<=n}a_j w_{R_j}, q_n=Q_{phi_n},
P_n=T_{a_n}q_{n-1}, q_0=Q_{psi_t}.

Framework2(d) gives ||q_n-P_n||<=delta_n=C3 R_n^-1/4 on the common compact, with one C3. For n=1 the stronger error O(R_1^-1/2) suffices; for n>=2 reference range R_{n-1}=sqrt(R_n). All ratio thresholds are met by enlarging R_1 once. Also a_{n+1}=R_n^-1/8 and delta_n/a_{n+1}=C3 R_n^-1/8. Thus sums of a_{n+1}, delta_n, and delta_n/a_{n+1} tend to0 as R_1→infinity.

Take R_1 large enough simultaneously that total later mass<1,

S sum_{n>=1}a_{n+1}<rho/2,
sum_{n>=1}[2delta_n/(l a_{n+1})+a_{n+1}U_*²/2]<tau/2,
sup_n 2delta_n/(k a_{n+1})<p/16,
sum_{n>=1}(delta_n+C0 a_{n+1})<eta0 rho/16,

where C0 bounds T_aQ-Q by C0a. Start r_1=tau/2 and iterate(5.1). For every n, on each W_i(rho-S sum_{j<n}a_{j+1}), the subdifferential of P_n is generated by the corresponding three radius-r_n balls, with r_n<tau. Both domains contain W_i(rho/2). Also telescoping q_n between successive transforms and(4.1) gives

||P_n-P_*||<eta0 rho/8

on both W_i(rho), for all n.

Minimize P_n(lambda)-g_i·lambda over W_i(rho/2). On the boundary its increase from lambda_i is at least eta0 rho/2 minus twice the approximation error, hence positive. The minimizer lambda_{i,n} is interior and g_i belongs to its subdifferential. Its local generating identity and the exclusion of every two-group hull force actual supports from all three groups there. Their convex hull contains closed B(g_i,gamma), so

closed B(g_i,gamma) subset partial P_n(lambda_{i,n}), i=1,2.   (5.2)

This simultaneously uses one core and one list of physical attractions. No potential is retuned after choosing one transition.

## 6. Limit, tail and common-density temperature jumps

Define the single final potential

Phi(x)=phi(|x|)=psi_t(|x|)-t sum_{n>=1}a_n w_{R_n}(x).

The series is uniformly convergent and the total mass<=A+1. Section2 gives stability with B=B0=t²/2, continuity and boundedness, and finite canonical limits for all beta>0,rho>0. For r>=1, a nonzero attraction term has R_n>=r. Thus

r^(3+1/32)|phi(r)|<=2^(3+1/32)t²+t||w||_infinity sum_n a_n R_n^(1/32)<infinity,

because the first term in the sum is A R_1^(1/32) and the later terms are R_n^-1/32. This proves the required tail.

Tail-mass continuity and the range errors give P_n→Q_Phi uniformly on the common compact. By compactness of the product W_1(rho/2)×W_2(rho/2), choose a single subsequence along which both lambda_{i,n} converge, to lambda_{i,c}=(beta_i,h_i). Every support inequality in(5.2) passes to the limit, so closed B(g_i,gamma) is contained in partial Q_Phi(lambda_{i,c}). An initially local support extends globally on the convex domain by restricting any hypothetical violation to a short segment near lambda_{i,c}. The two beta coordinates remain in the prescribed disjoint windows by the choice of rho.

Take eta=min(gamma/2,p)>0 and I=(2p-eta,2p+eta). If eta=p it still satisfies eta<2p. For every rho in I and both i, the points

(g_{i,1}-gamma/2,rho), (g_{i,1}+gamma/2,rho)

lie strictly in the radius-gamma support ball. (If eta=p<=gamma/2, the same inequality holds.) Write their energy coordinates as s_-<s_+. Partial convex duality yields

H_Phi(beta,rho)<=H_Phi(beta_i,rho)-s_±(beta-beta_i).

Indeed the full pressure support inequality holds for every field h; rearranging and taking sup_h gives this inequality, while density support at beta_i gives equality at the contact point. Since H_Phi(·,rho) is finite concave, its finite one-sided derivatives satisfy

H'_+(beta_i,rho)<=-s_+<-s_-<=H'_-(beta_i,rho).

Finally f(beta,rho)=t H_Phi(beta,rho)/beta. Continuity of H at beta_i cancels the derivative term from1/beta, leaving

f'_-(beta_i,rho)-f'_+(beta_i,rho)>=t gamma/beta_i>0.

The same phi, I and two beta_i work for every rho in I. This completes the proposed full proof of frozen R2T.

## 7. Contribution and limits

The new microscopic step is the exact two-level free-component classification, integration and maximization over every mixed cluster. It creates the extra density16p branch with entropy225p while retaining the4p branch with entropy9p. The resulting pressure has two separated active triples whose slope triangles have overlapping density interiors. This is not obtained by independently rescaling two already-constructed potentials: their sum would have uncontrolled interactions and would not preserve the source phase guarantees.

The macroscopic Kac/range framework, one-step separation and canonical support argument are antecedents in[B]. Their simultaneous use at two neighborhoods is credited as routine once the microscopic diagram is proved. The candidate does not claim that all phase transitions or all Gibbs states have been classified, that the transition locations equal the ideal values, or that no literature contains another proof. Independent contribution review must decide whether the new microscopic operation is substantial beyond these antecedents; the author does not award that verdict.
