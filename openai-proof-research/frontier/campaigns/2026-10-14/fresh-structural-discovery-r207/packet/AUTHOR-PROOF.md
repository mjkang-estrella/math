# Author proof of the frozen R207 statement

This is a discovery-stage proof for the exact statement in FROZEN.md, SHA256 7e9597aa5af080257a8a1f88e7a99a3bc41d3c0668fcf3e109076c4097d1d4e2. It is not an independent review or a manuscript. All scalars are real. Expectation is with respect to the indicated probability law. Write |.| for absolute value, ||.|| for the inherited L1 norm, and s_+=max(s,0).

The source construction is credited in full. In particular, the finite-head conditional expectations, first-exit factorization, real midpoint identity, and passage from an affine tail inequality to the asymptotic modulus are Source331 companion6, Section2, equations (prob:head-projection), (prob:first-exit), (prob:midpoint-identity), and Lemma (lem:affine). Its first-moment bounds use a finite second moment. The proof below replaces that bound and the special-law scalar estimates by a uniform first-moment argument for different laws in a compact family. The final bounded-tree induction is the source operation, with its weak-null input established here without a second moment.

## 1. Law topology and a scalar normalization

Every law in K is supported on [0,infinity), has finite first moment, and has mean one. Indeed, these properties pass to d_1 limits: for almost optimal couplings U,V, |EU-EV|<=E|U-V|, and nonnegativity passes to weak limits. For mu in K define

    rho(mu)=E|W-1|,       alpha(mu)=E|W-W'|,

where W,W' are independent of law mu. The first function is 1-Lipschitz in d_1. The second is 2-Lipschitz: couple U,V almost optimally and take an independent copy U',V'; then

    ||U-U'|-|V-V'|| <= |U-V|+|U'-V'|.

Thus rho(mu)>=rho_0 throughout K, and alpha(mu)>=rho(mu)>=rho_0 by conditional Jensen. Compactness gives the minimum alpha_K, with rho_0<=alpha_K<=2. In particular all laws in K are nonconstant.

For a finite list mu_i in K let D_i=W_i-W_i', with all W_i,W_i' independent, and put

    kappa(a)=E|sum_i a_i D_i|.

It is a norm on the finite coefficient space. In fact

    alpha_K ||a||_2/sqrt(3) <= kappa(a) <= 2 sum_i |a_i|.       (1)

Here and below ||a||_2 is Euclidean. To prove the lower bound, first take deterministic real c_i and independent fair signs epsilon_i. For R=sum epsilon_i c_i,

    ER^2=sum c_i^2,       ER^4<=3(sum c_i^2)^2.

Hölder gives ER^2 <= (E|R|)^(2/3)(ER^4)^(1/3), hence E|R|>=||c||_2/sqrt(3). A symmetric independent list D_i has the same law as epsilon_i |D_i|, with fresh independent signs. Apply this inequality conditionally on the magnitudes, then Jensen for the Euclidean norm:

    kappa(a) >= E||(a_i |D_i|)_i||_2/sqrt(3)
             >= ||(|a_i| E|D_i|)_i||_2/sqrt(3)
             >= alpha_K ||a||_2/sqrt(3).

Only finite deterministic sign sums have been assigned second and fourth moments. No moment of D_i beyond its first has been assumed. All integrations are legitimate because the list is finite and its sum of absolute first moments is finite. The upper bound and

    |kappa(a)-kappa(b)| <= 2 sum_i |a_i-b_i|                 (2)

follow directly by the triangle inequality.

## 2. A uniform excess lemma for compact families of laws

Assume throughout this section that every law in K is essentially unbounded. For every r>0 the quantity Theta_K(r) defined in FROZEN.md is strictly positive. Its defining set is nonempty: take a single law mu and coefficient 1/alpha(mu). Also 0<=Theta_K(r)<=1.

Here is a proof, including the classical infinitesimal-array argument rather than using a limit-law theorem as a black box. Suppose, for a fixed finite r>0, that Theta_K(r)=0. There are finite independent sums

    S_n=sum_{i=1}^{l_n} a_{n,i} D_{n,i},
    E|S_n|=1,       E(|S_n|-r)_+ -> 0.                    (3)

Their laws are tight by Markov's inequality. They are uniformly integrable: for M>2r,

    E[|S_n| 1_{|S_n|>M}] <= 2 E(|S_n|-r)_+.

For all sufficiently large n this is arbitrarily small uniformly; for the remaining finitely many integrable variables it tends to zero with M. Select a weakly convergent subsequence S_n -> Z. Weak compactness of tight probability measures on the real line follows, for example, by diagonal selection of distribution functions at rational points. Truncating the continuous function |s| and using uniform integrability gives E|Z|=1. Similarly the bounded continuous truncations of (|s|-r)_+ have limiting expectation zero. Therefore

    Z is symmetric,       |Z|<=r almost surely,       E|Z|=1.   (4)

We claim max_i |a_{n,i}| -> 0. For every i, conditional Jensen over the other independent, mean-zero summands gives

    |a_{n,i}| alpha(mu_{n,i}) <= E|S_n|=1.

The coefficients are therefore bounded by 1/alpha_K. If the claim fails, select a coefficient bounded away from zero on a subsequence. Absorb its sign into its symmetric D variable, and pass to a further subsequence so that this coefficient tends to a>0 and its law mu_{n,i} tends in d_1 to mu in K. The difference variables converge in d_1 to D=W-W', since an independent pair of almost optimal couplings has expected difference error at most twice the coupling error. The remaining sum R_n is independent of that D variable and satisfies E|R_n|<=1 by Jensen. Its laws are tight, so a further subsequence converges weakly to R. Characteristic functions, or convergence of product laws, show

    Z has the law of aD+R, with D and R independent.        (5)

This law cannot have bounded support. Since mu is unbounded and has mean one, D has an unbounded positive tail: choose a finite A with P(W'<=A)>0, then P(D>B)>=P(W>B+A)P(W'<=A)>0 for every B. For some finite H, P(R>=-H)>0. Independence now gives P(aD+R>r)>0, contradicting (4). This proves the claim.

Fix an arbitrary integer m>=1. Independently retain each summand of S_n with probability 1/m, writing

    Y_{n,m}=sum_i B_{n,i} a_{n,i} D_{n,i},
    P(B_{n,i}=1)=1/m.

For each fixed selected subset, conditional Jensen over its mean-zero complement bounds its expected absolute sum by E|S_n|=1. Averaging the selectors gives E|Y_{n,m}|<=1. Hence, for this fixed m, a subsequence has a weak limit Y_m; it is symmetric. These subsequences need not be common for different m.

For a fixed real t write phi_{n,i}(t)=E exp(it a_{n,i}D_{n,i}), which is real by symmetry, and z_{n,i}=1-phi_{n,i}(t). The bound E|D_{n,i}|<=2 gives

    0<=z_{n,i} <= 2|t| max_i |a_{n,i}| =: eta_n -> 0.

For sufficiently large n, eta_n<1. The characteristic functions of S_n and Y_{n,m} are respectively

    A_n=product_i(1-z_{n,i}),
    B_n=product_i(1-z_{n,i}/m).

Put H_n=sum_i z_{n,i}. Bernoulli's inequality and -z/(1-eta_n)<=log(1-z)<=-z give

    0 <= B_n^m-A_n
       <= exp(-H_n)-exp(-H_n/(1-eta_n))
       <= [eta_n/(1-eta_n)] H_n exp(-H_n)
       <= eta_n/[e(1-eta_n)].                             (6)

Indeed B_n^m>=A_n follows factorwise from (1-z/m)^m>=1-z, while B_n^m<=exp(-H_n) and A_n>=exp(-H_n/(1-eta_n)). This estimate also covers H_n tending to infinity; no division by a limiting characteristic function is used. Taking limits along the subsequence for Y_m yields

    phi_Z(t)=phi_{Y_m}(t)^m     for every real t.

Uniqueness of characteristic functions means Z has the distribution of a sum of m independent copies of Y_m. If P(Y_m>r/m)>0, the event that all these copies exceed r/m has positive probability and their sum exceeds r, contradicting (4). By symmetry also P(Y_m<-r/m)=0. Thus |Y_m|<=r/m almost surely. It has mean zero and finite variance, and

    Var(Z)=m Var(Y_m) <= r^2/m.

This holds for every integer m. Consequently Var(Z)=0, and symmetry implies Z=0 almost surely, contradicting E|Z|=1. The contradiction proves Theta_K(r)>0 for every r>0.

The classical principles here are compactness of tight real laws, symmetrization, and the divisibility of infinitesimal independent-sum limits. Equation (6) supplies the needed special case directly. The proposed new application is its uniform, first-moment-normalized interface for arbitrary mixed lists of the parent laws, not an assertion that infinite divisibility is new.

## 3. The actual product space and its finite heads

There are countably many edge coordinates. The countable product of their Borel probability laws supplies the required probability space. Each path uses finitely many independent nonnegative variables of mean one. Therefore P_v is integrable, nonnegative and ||P_v||=EP_v=1, even if some multipliers vanish or have infinite second moment.

The closed real span X is a Banach space. Rational finite combinations of its countable generating set are dense, so it is separable. It is infinite dimensional: the independent first-generation variables W_{emptyset,j}-1 are linearly independent. In a finite linear relation, condition on one of them and integrate all the others; their means are zero, leaving c_j(W_{emptyset,j}-1)=0 almost surely. Nonconstancy forces c_j=0 for each j. This argument needs no orthogonality in L2.

Let T be a finite predecessor-closed set of vertices containing the root. Let G_T be the sigma-field of its nonroot edge coordinates, and let v_T be the last ancestor of v in T. Independence and mean one give

    Q_T P_v := E(P_v | G_T)=P_{v_T}.                       (7)

Thus conditional expectation restricts to a contractive projection on X with range

    E_T=span{P_v:v in T}.

Continuity and closedness of this finite-dimensional space establish the same assertion on the closed span, not just its algebraic part. The subspace F_T=ker(Q_T|_X) is closed and of finite codimension. If y in F_T is approximated by finite-product combinations z_n, then (I-Q_T)z_n are finite-product combinations in F_T and converge to y, since ||I-Q_T||<=2. This proves the density needed below. No infinite first-exit expansion of a completed tail will be used.

For a finite-product tail y in F_T, let I be its finite set of first exits from T. Factoring at each exit i gives exactly

    y=d+sum_{i in I} W_i B_i,
    d=-sum_i m_i,       m_i=E(B_i | G_T).                  (8)

Here W_i has law mu_{i^-}; B_i is a finite linear combination of products using the old coordinates and strict descendants of i, multiplied by P_{i^-}. The old part d is G_T-measurable. Conditional on G_T, the B_i are independent because the exit subtrees are disjoint. The whole vector (B_i) is independent of the first-exit variables W_i conditionally on G_T. Consequently conditioning further on every B_i still leaves those W_i mutually independent with their assigned, deterministic laws. All B_i are integrable; finite products use independent integrable factors on distinct coordinates. Also E(sum B_i^2)^(1/2)<=sum E|B_i|<infinity.

For the list of laws mu_{i^-}, let kappa(B) mean the coefficient norm of Section1 evaluated at the random list B_i. It is measurable by (2) and integrable by its upper bound there.

## 4. Replacing the second-moment estimate

For every finite-product y in F_T,

    ||y|| <= C_K E kappa(B),       C_K=1+2sqrt(3)/alpha_K.  (9)

The same inequality holds conditionally on G_T. To prove it, fix the old coordinates and write, from (8),

    y=sum_i B_i(W_i-1)+sum_i(B_i-m_i).

After fixing B, Jensen using independent fresh copies W_i' gives

    E_W |sum_i B_i(W_i-1)|
       <= E_{W,W'} |sum_i B_i(W_i-W_i')|=kappa(B).

For the second sum, take conditionally independent copies B_i' of the independent B_i. Jensen, the symmetry of B_i-B_i', and independent signs give

    E|sum_i(B_i-m_i)|
       <= E|sum_i(B_i-B_i')|
        = E E_epsilon |sum_i epsilon_i(B_i-B_i')|
       <= E||(B_i-B_i')_i||_2
       <= 2 E||B||_2
       <= (2sqrt(3)/alpha_K) E kappa(B).

The sign upper bound is Cauchy--Schwarz on a finite sign space for a fixed realized coefficient list. It imposes no second moment on B. Integrating over the old coordinates proves (9).

## 5. A uniform affine midpoint inequality

For x,y in X put

    M_t(x,y)=(||x+t y||+||x-t y||)/2-||x||.

The real identity (|a+b|+|a-b|)/2=max(|a|,|b|) gives

    M_t(x,y)=E(t|y|-|x|)_+.                               (10)

Fix t>0 and r>0 and abbreviate theta=Theta_K(r). For u in E_T and a finite-product y in F_T we prove

    M_t(u,y) >= theta [ t||y||/(2C_K) - ||u||/r ].         (11)

Condition on G_T and the entire list B. Put A=|u|, b_i=B_i and k=kappa(b). Resample only W_i to independent W_i', leaving d and b fixed. For the even convex function f(s)=(t|s|-A)_+, identical distribution and convexity imply

    E_W f(d+sum b_i W_i)
       >= E_{W,W'} f( sum b_i(W_i-W_i')/2 ).              (12)

Indeed f((z-z')/2)<= [f(z)+f(-z')]/2 and f is even. If k>0, the sum divided by k is admissible in the definition of Theta_K. If 2A/(tk)<=r, monotonicity of the threshold gives a lower bound tk theta/2 for the right side of (12), which is at least theta(tk/2-A/r). If 2A/(tk)>r, the latter expression is negative and the nonnegative left side again dominates it. When k=0 the same conclusion follows from nonnegativity (and (1) forces b=0). In all cases

    E_W(t|y|-|u|)_+ >= theta(t kappa(B)/2-|u|/r).

Integrate and apply (9) to obtain (11). The estimate is uniform over all finite heads, all old centers, and all finite random coefficient lists with their possibly different laws. Independence is invoked only after the relevant conditioning; a Gaussian or identical-law assumption is not substituted.

## 6. Completion, order of choices, and AMUC

The elementary estimate

    |M_t(x,y)-M_t(x',y')| <= 2||x-x'||+t||y-y'||          (13)

shows that (11) passes to every y in the closed tail F_T. This passage uses finite-product approximations in F_T, and does not assign any unproved representation to a general tail.

Choose r=4C_K/t. Section2 gives theta>0. Equation (11) has constants

    A_t=t theta/(2C_K),       B_t=theta/r=t theta/(4C_K),
    A_t-B_t=t theta/(4C_K)>0.

Fix a unit x and epsilon>0. Choose a finite-product u with ||x-u||<epsilon, then a finite predecessor-closed T containing all product paths in u. This T is chosen before y. For every y in F_T with ||y||>=1, equations (11)-(13) give

    M_t(x,y) >= A_t-B_t-(B_t+2)epsilon.

Take the infimum over those y, then the supremum over closed finite-codimensional subspaces, then let epsilon decrease to zero. The resulting bound is independent of x, so the infimum over unit x yields

    Delta_X(t) >= t Theta_K(4C_K/t)/(4C_K)>0.              (14)

For clarity, the maximum and averaged conventions give the same positivity. At a unit x choose a norming functional ell. On ker ell, both ||x+t y|| and ||x-t y|| are at least one. Intersect any finite-codimensional F with ker ell; this keeps finite codimension and cannot reduce an infimum for the maximum expression. On the intersection, average excess is at least half the maximum excess. Taking suprema and then infima gives

    (1/2) Delta_X^max(t) <= Delta_X(t) <= Delta_X^max(t).  (15)

For either symmetric expression, the function of the displacement radius is even and convex, hence nondecreasing on [0,infinity). Directions of norm exactly one and norm at least one therefore give the same infimum. All these direction sets are nonempty because X is infinite dimensional. This proves the positive direction of the frozen equivalence in both conventions.

## 7. Weakly null children with only first moments

For a fixed parent v put

    Z_{v,j}=P_v(W_{v,j}-1)=P_{v^j}-P_v,
    rho_v=rho(mu_v).

Then ||Z_{v,j}||=rho_v>=rho_0, and Z_{v,j} tends weakly to zero in X. Here is the complete weak-null argument. Define a probability measure nu by dnu=P_v dP, using P_v>=0 and EP_v=1. The child coordinates W_{v,j} retain their law mu_v and are independent of every finite cylinder avoiding them under nu, because the density P_v uses only ancestors.

Let g be any bounded measurable function on the product space. Bounded cylinder functions g_l depending on finitely many coordinates can approximate g in L1(nu), with |g_l|<=||g||_infinity. This follows from the increasing finite-coordinate sigma-fields generating the countable product sigma-field, or from density of simple cylinder functions followed by truncation. For j outside the finitely many coordinates in g_l,

    E_nu[g_l(W_{v,j}-1)]=0.

For any H>0 the remaining error is bounded by

    |E_nu[(g-g_l)(W_{v,j}-1)]|
      <= H ||g-g_l||_{L1(nu)}
         +2||g||_infinity E_{mu_v}[|W-1|1_{|W-1|>H}].   (16)

First choose H large by integrability, then l large, and finally j outside that finite cylinder. The bound tends to zero. Thus E[g Z_{v,j}]->0 for every g in L-infinity. Duality of probability L1 and L-infinity gives weak nullity in L1. Hahn--Banach extends every functional on its closed subspace X to L1, so the sequence is weakly null in X itself. The argument is for each fixed parent; no exchange of v and j limits is used. Vanishing values of P_v cause no difficulty in the absolutely continuous probability measure nu.

## 8. A bounded law in the closure forces zero midpoint modulus

Suppose mu_* in K is essentially bounded. Set rho_*=rho(mu_*)>=rho_0 and L_*=ess sup_{mu_*}|W-1|. Then 0<L_*<infinity. Choose assigned parent laws mu_{v_n} -> mu_* in d_1, and put rho_n=rho(mu_{v_n})->rho_*.

For a fixed parent v, the positive unit center x=P_v and the weakly null unit vectors y_j=Z_{v,j}/rho_v satisfy the exact identity

    M_t(P_v,y_j)=h_v(t),
    h_v(t)=E_{mu_v}(t|W-1|/rho_v-1)_+.                   (17)

This uses positivity and independence of P_v and its children, not any boundedness of P_v.

For every closed finite-codimensional F, the quotient images of y_j tend to zero in norm: their images are weakly null in a finite-dimensional normed space. Choose z_j in F with ||z_j-y_j||->0, and normalize z_j by its norm, which tends to one. The resulting unit vectors in F still differ from y_j by a norm-null sequence. Equation (13) then shows

    inf_{y in F, ||y||>=1} M_t(P_v,y) <= h_v(t).

Since F was arbitrary, the centerwise supremum is at most h_v(t), and consequently

    0<=Delta_X(t)<=h_{v_n}(t)     for every n.             (18)

Let t_*=rho_*/(2L_*). For fixed 0<t<=t_*, the integrand for mu_* is identically zero. The functions in (17) converge in expectation under d_1 convergence and rho_n->rho_*>0. Explicitly an almost optimal coupling U_n,U of mu_{v_n},mu_* gives

    |E(t|U_n-1|/rho_n-1)_+ - E(t|U-1|/rho_*-1)_+|
      <= (t/rho_n)E|U_n-U|
         +t|1/rho_n-1/rho_*| E|U-1| -> 0.

Thus h_{v_n}(t)->0. Equation (18) proves Delta_X(t)=0 for every 0<t<=t_*. Equation (15) gives the same zero values for the maximum modulus. This proves necessity, including the case where the bounded law occurs only in K and at no vertex.

## 9. Every equivalent norm has the stated one-sided zero range

Let a||z||<=N(z)<=b||z|| and fix 0<t<=a rho_0/b. The one-sided modulus is nonnegative: at each N-unit center, the kernel of a norming functional makes N(x+t y)>=1. Suppose for contradiction delta_N(t)=d>0.

For each unit center u choose a closed finite-codimensional F such that

    N(u+t q)>=1+3d/4     (q in F, N(q)=1).

This is possible since the centerwise supremum is at least d, even if it is not attained. Convexity along a ray extends the same lower bound to u+w for w in F with N(w)>=t.

At any parent v use u=P_v/N(P_v). The sequence z_j=Z_{v,j}/N(P_v) is weakly null by Section7 and satisfies

    N(z_j)>=a rho_v/b>=a rho_0/b>=t.

Its quotient images modulo F tend to zero. Choose w_j in F with N(w_j-z_j)->0. If N(w_j)<t, replace w_j by t w_j/N(w_j), for large j. This changes it by at most N(w_j-z_j), because N(z_j)>=t. The repaired w_j still tends to z_j in N norm and has norm at least t. For large j we obtain

    N(u+z_j)>1+d/2,
    N(P_{v^j})>(1+d/2)N(P_v).                            (19)

Choose such a child repeatedly to any prescribed finite depth m. The tree has countably infinite branching at every parent, so each choice is available; it is not a finite-branching approximation. Since every P_v has inherited norm one, (19) yields

    a(1+d/2)^m <= N(P_{chosen depth m}) <= b,

a contradiction for sufficiently large m. Hence delta_N(t)=0 throughout the frozen interval. This is a given-space renorming obstruction with a uniform lower increment bound rho_0. No preservation of the original midpoint modulus under renorming has been assumed.

Sections1-9 prove every conclusion of FROZEN.md under exactly its hypotheses.

## 10. Concrete consequences illustrating the scope

These are applications of the frozen statement, not replacement targets.

(a) A fixed nonnegative, nonconstant mean-one integrable W gives K={law(W)}. Its product span is AMUC exactly when W is essentially unbounded. The finite second moment in the source's general construction is unnecessary for this criterion and for the no-AUC conclusion. For example, let T have density (3/2)s^(-5/2) on [1,infinity) and let W=T/3. Then ET=3, EW=1, EW^2=infinity, W>=1/3, and W is unbounded. The theorem applies, giving an AMUC inherited norm and no equivalent AUC norm.

(b) Individual unboundedness at every parent does not suffice. Let mu_*= (delta_{1/2}+delta_{3/2})/2, and let nu be the preceding Pareto law for W. Put mu_n=(1-epsilon_n)mu_*+epsilon_n nu with epsilon_n=1/(n+2), n>=1, and assign mu_v=mu_{|v|+1}. Every assigned law is strictly positive, unbounded, mean one, and has infinite second moment. Nevertheless mu_n -> mu_* in d_1 (couple the mixture to mu_*), so K={mu_*,mu_1,mu_2,...} is compact. Also rho(mu_n)>=(1-epsilon_n)/2>=1/3. The bounded-limit clause gives zero midpoint modulus for all 0<t<=1/2, since rho_*=L_*=1/2. This is one inhomogeneous product tree, not a sum of component spaces.

(c) Genuinely varying laws can also retain AMUC. Take the Pareto law nu above and the mean-one exponential law eta, and assign to each parent any mixture (1-s_v)nu+s_v eta, 0<=s_v<=1. Their closure is contained in a compact d_1-continuous mixture curve. Every mixture is unbounded and rho is at least min(rho(nu),rho(eta))>0, by linearity of the integral of |w-1|. Thus every such assignment has AMUC inherited norm and no equivalent AUC norm. The common lower modulus is supplied by the compact curve's Theta and C, independent of the assignment and center.

## 11. Limits and strongest-reduction comparison

The result does not improve the source's numeric exponential/Gaussian constants, its exact Daugavet moduli, or its D^2>=1+k/4 forest diamond bound. It proves no new graph embedding estimate, basis theorem, reflexivity claim, or complex-scalar version. Its compact-law hypothesis and positive rho_0 are essential to the scope; no assertion outside that class is made. In particular, laws approaching delta_1 are not covered.

The source already pays for the independent-product span, conditional heads and first-exit decomposition, affine completion interface, special-law estimates, and bounded-tree renorming induction. DKRRZ supplies the geometric/finite-codimension AMUC framework; its unconditional-basis renorming result cannot be applied without an unconditional basis. Baudier and Kadets-Werner use measure-precompactness/Daugavet mechanisms, whose hypotheses are not silently assigned to X. The original I88 MAP observation is a routine consequence of the same heads and is not a claimed contribution. Classical independent-sum symmetrization and divisibility remain credited as classical operations.

The distinct proved work is the uniform normalized-excess lemma across all mixed finite lists in a compact law family, the first-moment conditional comparison in (9), and their two-way conversion to a single row-dependent product-tree criterion, including bounded limit laws absent from the tree itself. The proof of this operation is explicit in Sections1-8. Whether this full theorem is a substantial contribution requires the parent's separate primary-literature review; no contribution grade, correctness grade, acceptance or count is assigned here. The limited primary/history navigation is not a priority or exhaustion claim.
