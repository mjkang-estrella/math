# T373E135 author proof

Author-level submission at the exact frozen scope `FROZEN-SCOPE.md`. The source and its operative proofs are stipulated true. This document supplies no independent correctness, contribution, acceptance or count decision. All logarithms are natural. Differential entropy here means H(p)=integral p log p, with this sign. KL is relative entropy, without subtraction of masses.

## 1. Source interfaces and latent coordinates

Fix the data of the frozen scope. Write H_0=Id, H_1=Y_1, H_2=W_1, H_3=Y_2, H_4=W_2. Their images of Qbar are pairwise disjoint compact sets. The prescribed marginal has a smooth compactly supported density and smooth square root by the source's change-of-variables argument.

The exact source inputs are `local.tex`, Lemma `lem:local`; `certificate.tex`, Proposition `prop:certificate` and Lemma `lem:common-ball`; `proof.tex`; and `riesz.tex`, Theorem `thm:riesz`, from the sole family373 manuscript. They give a bounded smooth-on-components potential u, R=c_alpha-sum u>=0 on the five-component product, and the complete contact set consisting of the two graphs and their six coordinate permutations. They also give uniform positive definiteness of the (x,z)-Hessian of c_alpha-u_0(x)-v_k(z), on the small convex product neighborhoods at issue. All these operations, including the construction and exclusion of other component patterns, are paid inputs.

For k=1,2 use latent coordinates

 r_k(t0,t1,t2)=R(t0,Y_k(t1),W_k(t2)).

This is smooth on a neighborhood of Qbar^3. Its value and gradient vanish at every (t,t,t). The source convexity gives, with a fixed lambda>0,

 r_k(t0,t1,t2)>=lambda (|t0-t1|^2+|W_k(t2)-W_k(t1)|^2).

A smaller lambda works on the compact products for both branches. A smooth diffeomorphism on a neighborhood of Qbar is bi-Lipschitz on Qbar: use its local inverse derivative near the diagonal and compactness of the pairs away from the diagonal. Consequently there are c,C>0 such that

 c (|t1-t0|^2+|t2-t0|^2)<=r_k(t0,t1,t2)
 <=C (|t1-t0|^2+|t2-t0|^2).                         (1)

For the upper bound use bounded second derivatives and Taylor expansion from (t0,t0,t0), on the convex latent cube. The first bound follows from the displayed source estimate and the triangle inequality. Thus

 K_k(t)=D^2_(t1,t2)r_k(t,t,t)

is smooth and uniformly positive definite on Qbar. In coordinates (t0,h1=t1-t0,h2=t2-t0), the entire Hessian of r_k at h=0 has zero tangent and mixed blocks and normal block K_k(t). Indeed r_k(t,0)=0 and D_h r_k(t,0)=0 identically in t. Determinants of K_k are bounded above and away from zero.

The product bump f is smooth after zero extension, bounded, and positive exactly on Q. It satisfies

 integral f |log f|<infinity,   integral f |grad log f|^m<infinity

for every finite m. These follow by integrating a polynomial in inverse boundary distance against exp(-2/(a^2-r^2)) in each coordinate. In particular H(f) and C_* are finite.

## 2. An elliptic covariance lift with constant marginal blocks

Here is the elementary matrix construction used in the recovery, stated explicitly because merely adding independent marginal noise would not prescribe the transverse covariance.

Let A(t) be any smooth, uniformly positive definite 2d-by-2d matrix field on a neighborhood of Qbar, with d-by-d blocks A_ij. Extend it smoothly to all R^d, uniformly elliptic and with bounded derivatives, by a smooth cutoff and a fixed positive definite matrix outside a compact neighborhood. This uses convexity of the positive definite cone; choose the cutoff supported within the original neighborhood. Define

 R_A(t)=(-A_11(t)/2, -A_22(t)/2),
 S(t)=[[beta I, R_A(t)],[R_A(t)^T,A(t)]],

where beta>1+sup_t ||R_A(t) A(t)^(-1) R_A(t)^T||. S is uniformly positive definite by its Schur complement and compactness, and bounded. Let L send (z,h1,h2) to (z,z+h1,z+h2), and set C=L S L^T. Its diagonal d-by-d blocks are all beta I. In fact

 C_00=beta I,
 C_11=beta I+2(-A_11/2)+A_11=beta I,
 C_22=beta I+2(-A_22/2)+A_22=beta I.

If D sends (z0,z1,z2) to (z1-z0,z2-z0), then

                  D C(t) D^T=A(t).                         (2)

No commutativity of A's blocks is assumed. C is smooth, globally bounded and uniformly elliptic, with bounded derivatives. Its positive square root sigma has the same regularity needed for a globally Lipschitz diffusion coefficient. A constant beta works for the entire compact family, separately or jointly for the two branches.

For branch k take A=K_k^(-1). From now on all three diagonal marginal blocks of C are beta I, while C as a full matrix is evaluated at its first latent coordinate.

## 3. A diffusion that preserves all three marginals exactly

On Q^3 consider

 dZ_i(s)=sigma_i(Z_0(s)) dB(s)+b(Z_i(s)) ds,
 b(x)=(beta/2)grad log f(x),                 i=0,1,2,        (3)

where B is a standard Brownian motion in R^(3d), sigma_i is the corresponding d-row block, and Z_0(0)=Z_1(0)=Z_2(0)=T with T distributed as f. The notation Z_0(s) denotes the first particle, not the initial state.

The drift is smooth locally in Q, although it is unbounded near its boundary. We justify existence, confinement and stationarity rather than applying a theorem for a globally bounded drift.

For one scalar factor write V(r)=2/(a^2-r^2), up to an irrelevant constant. Its diffusion generator is

 L_1 h=(beta/2)(h''-V'h').

V tends to infinity at both endpoints, and

 L_1 V=(beta/2)(V''-(V')^2)

is bounded above: near either endpoint the negative term has order distance^-4 and the positive term order distance^-3. The sum of these V's over all coordinates of all three particles has the same bounded-above generator under (3). Cross-covariance terms do not occur in its Hessian. Local strong existence holds because the coefficients are locally Lipschitz. Stopping when this sum reaches n, Ito's formula and Markov's inequality give a bound (initial expected V+constant times s)/n for boundary exit before time s. The initial expectation is finite. Thus the local solution extends uniquely for all finite times and never reaches the boundary.

Each particle's martingale has quadratic covariation beta I ds, by the constant diagonal blocks of C. Levy's characterization therefore makes that martingale divided by sqrt(beta) a d-dimensional Brownian motion in the full filtration. Its individual equation is the autonomous product Langevin equation with drift b. Its law is unique by the same local uniqueness and nonexit argument.

The invariant probability of each scalar equation is proportional to exp(-V). One direct justification, including the boundary issue, is to reflect the equation on [-a+1/n,a-1/n]. Integration by parts gives invariance of the normalized restriction of exp(-V), since its probability current is zero and the reflecting test functions have zero derivative at the endpoints. Couple to the unrestricted equation up to the first hit of these endpoints. The preceding V bound makes the hit probability tend to zero on each finite time interval, with the initial normalized restrictions having uniformly bounded V expectation. Local strong stability and convergence of these initial restrictions then give invariance of exp(-V) on the open interval. Taking the product gives invariance of f on Q. Thus uniqueness in law of each individual equation implies, for every s>=0,

                        (Z_i(s))#P=nu.                    (4)

This is exact. Correlations between the particles do not alter their individual generators. The joint distribution need not be stationary.

In particular, at each time the expected squared drift summed over particles is the fixed finite number 3 beta^2 I(f)/4, where I(f)=integral f|grad log f|^2. Higher moments are finite as well.

## 4. Driftless comparison and entropy of the thin coupling

Let P_s be the joint law from (3), and let Q_s be the joint law from the same diagonal initial distribution with the drift deleted. The latter diffusion has globally smooth bounded uniformly elliptic coefficients.

### 4.1 Finite-energy change of drift

For every s in a bounded interval,

                        KL(P_s|Q_s)<=C s.                 (5)

For completeness, stop the drift on compact subsets of Q^3, additionally stopping its accumulated squared norm. The drift perturbation is then bounded on the relevant stopped portion, so the exponential change-of-measure formula is a true martingale and gives path relative entropy equal to one half the expected integral of |sigma^(-1)b_joint|^2. Until the stopping time the stopped and original drifted laws coincide. Uniform ellipticity and (4) bound that expectation by C s. After the stopping time use zero drift. The stopping probability under the original law tends to zero, by nonexit and finite expected drift energy, so the stopped path laws converge to the original path law. Lower semicontinuity of relative entropy gives the same upper bound against the unchanged driftless path law. Applying the measurable terminal-time map cannot increase relative entropy, which proves (5). The initial law is the same for both processes; its singularity on the diagonal is immaterial to this argument.

Credit and chronology: stationary Langevin approximation and its Girsanov entropy comparison are primary operations in Agarwal–Harchaoui–Mulcahy–Pal, arXiv:2505.07647v1, Theorem1 and its proof; Djellout–Guillin–Wu, arXiv:math/0410172v1, equations(5.1),(5.7), supplies a transitive stopped-martingale antecedent. The complete Theorem1 proof and the latter passages were read after this proof's first draft, as recorded in the notebook. We claim neither the invariance principle nor the change-of-drift identity as a new operation. Section3 and the stopping argument above explicitly handle our compact flat density and common-noise three-particle coefficient, rather than importing a theorem whose hypotheses do not cover them.

### 4.2 The bounded-coefficient heat-kernel input

We use only the classical deterministic parametrix, not a boundary heat-kernel assertion for (3). A smooth bounded uniformly elliptic coefficient C on R^m has a transition density p_s(z,z') with a Gaussian upper bound and the frozen-Gaussian remainder

 |p_s(z,z')-G_{s C(z')}(z'-z)|
       <= C s^(theta/2) s^(-m/2) exp(-c|z-z'|^2/s),         (6)

for any fixed 0<theta<1, 0<s<=1, after enlarging constants. Freezing at the starting point instead is also possible; we use the displayed final-point convention.

The actual construction and bound used were read in Pascucci-Pesce, *The parametrix method for parabolic SPDEs*, deterministic Section4: Assumptions4.1-4.2, Theorems4.6-4.7, equations(4.4)-(4.6),(4.13),(4.17),(4.20). In their backward-kernel notation, p_s(z,z')=Gamma(s,z;0,z'). Thus (6) has the correct orientation. Their proof estimates the residual of the frozen Gaussian by C s^(-1+theta/2) times a wider Gaussian. Iterated time-space convolution gives Gamma-function denominators; its summed series is bounded by the same residual order. One final convolution gives C s^(theta/2) times a Gaussian, exactly(6). The coefficients here satisfy their hypotheses globally with zero drift and zero killing. No unbounded-drift extension from their Remark4.4 is used. Their Gaussian lower bound, or its elementary near-diagonal bound followed by chaining, also ensures positivity and a Gaussian lower estimate. Only the upper bound and (6) drive the asymptotics below; the lower bound ensures finite cross-entropies at fixed s.

Define the invertible rescaling

 F_s(z0,z1,z2)=(x=z0,w1=(z1-z0)/sqrt(s),w2=(z2-z0)/sqrt(s)).

Its inverse has determinant s^d. Let q_s be the Lebesgue density of F_s#Q_s. Integrating (6) over the diagonal initial variable gives

 q_s(x,w)=s^d integral_Q f(t) p_s((t,t,t),(x,x+sqrt(s)w1,x+sqrt(s)w2)) dt.

Gaussian completion of squares and boundedness of f yield

                  0<q_s(x,w)<=C exp(-c|w|^2).              (7)

The constants are independent of x and 0<s<=1. The estimate follows because integration over the d-dimensional common shift removes exactly a factor s^(d/2) from the 3d-dimensional Gaussian. Its remaining quadratic form is comparable to |w|^2.

Set t=x+sqrt(s)v in the frozen Gaussian. At its final point the coefficient is C(x), since the full coefficient field depends only on the first particle. Integrating in v marginalizes the Gaussian in (z,h1,h2) to its difference coordinates, whose covariance is A(x) by(2). Hence, locally uniformly for x in Q and w in R^(2d),

             q_s(x,w) -> q_0(x,w):=f(x) G_{A(x)}(w).        (8)

The remainder contributes at most C s^(theta/2) exp(-c|w|^2). For the main term, bounded uniformly continuous f and Gaussian tails justify the change of variables and local uniform convergence. This also proves weak convergence to q_0; alternatively tightness follows directly from the bounded diffusion coefficient and the compact initial support. q_0 has total mass one.

Let p_s be the density of F_s#P_s. Such a density exists by(5), and data processing gives KL(p_s|q_s)<=C s. Consequently p_s and q_s have total variation distance tending to zero, and p_s converges weakly to q_0.

The second moments also converge. The x marginal of p_s is exactly f. For the difference martingale M=(Z_1-Z_0,Z_2-Z_0) minus its drift,

 E|M_s|^2/s=(1/s)integral_0^s E tr A(Z_0(v))dv
            =integral f tr A.

The squared norm of the divided-by-sqrt(s) drift integral is O(s), by Cauchy-Schwarz and (4). Its cross term with the martingale is o(1). Therefore E_{p_s}|w|^2 -> integral f tr A, the second moment of q_0.

### 4.3 Entropy transfer without dividing by the flat density

We claim

                           H(p_s)->H(q_0).                 (9)

For the lower limit compare to a fixed nondegenerate Gaussian reference on (x,w). Relative entropy is lower semicontinuous under weak convergence. Subtracting the Gaussian log density is legitimate with the just-proved second-moment convergence. It gives liminf H(p_s)>=H(q_0).

For the upper limit use

 H(p_s)=KL(p_s|q_s)+integral p_s log q_s.

At each fixed s the identity is legitimate: a Gaussian lower estimate for q_s, obtained by integrating over a fixed inner ball where f has positive mass, bounds -log q_s on x in Q by C_s+C|w|^2; (7) bounds it above. The second moments of p_s are finite. The KL term is O(s). Globally log q_s<=log C by(7), and on every compact subset of Q times R^(2d), log q_s converges uniformly to log q_0 by(8). Exhaust this set by compact rectangles whose boundaries have q_0 measure zero. Weak convergence on each rectangle and the global upper bound on its complement give

 limsup integral p_s log q_s <= integral q_0 log q_0.

To see the exhaustion step explicitly, for a rectangle K the upper bound is integral_K q_0 log q_0+(log C)(1-q_0(K)); send K to Q times R^(2d). The limit integral is absolutely finite because integral f|log f| is finite and A and A^(-1) are bounded. This proves(9), with no positive lower bound on f near the boundary.

The entropy of q_0 is computed from the 2d-dimensional Gaussian:

 H(q_0)=H(f)-d log(2pi)-d-(1/2)integral f log det A
        =H(f)-d log(2pi)-d+(1/2)integral f log det K_k.

Undoing F_s changes entropy by -d log s. Thus the exact three-marginal latent coupling P_s has

 H(P_s)=d log(1/s)+H(f)-d log(2pi)-d
                   +(1/2)integral f log det K_k+o(1).      (10)

This is an entropy statement for the constructed recovery, not a Gaussian limit theorem for the unknown entropic optimizer.

## 5. Cost of the recovery

Ito's formula applies to the smooth bounded function r_k on the compact cube; local stopping followed by integrability of the drift justifies expectations. Its value at the diagonal is zero. Its generator expectation at time s tends as s decreases to zero to

 (1/2) integral_Q f(t) tr(C(t) D^2 r_k(t,t,t))dt=d.          (11)

Indeed the diffusion term converges by boundedness and continuity. The gradient of r_k vanishes on the diagonal, while its gradient is Lipschitz on Qbar^3. Since the process tends in L2 to its diagonal initial state, Cauchy-Schwarz and the fixed finite second drift moment make the expected drift term tend to zero. In the coordinates (t0,h1,h2), the Hessian has normal block K_k and no other blocks, so its contraction with C is tr(K_k A)=2d by(2). This proves(11). Integration in time gives

                         integral r_k dP_s=d s+o(s).       (12)

Every physical recovery triple (Z_0,Y_k(Z_1),W_k(Z_2)) remains in three distinct compact components. Hence it is uniformly separated from collisions, for every alpha>0. No integrability restriction alpha<d is introduced by Gaussian tails: the actual recovery is the confined drifted process, not the auxiliary driftless Gaussian comparison.

## 6. Assemble twelve cells and compute the coefficient

For each branch form P_s^k by the preceding construction. Push it forward by (Id,Y_k,W_k), and then average over k with weight1/2 and over its six coordinate permutations with weight1/6. Call the resulting physical coupling pi_s^rec. Equation(4) gives exactly the prescribed identical marginal mu in every coordinate. The twelve component patterns are disjoint. Each has mass1/12; the product reference mu^3 on the corresponding ordered component cell has mass (1/3)(1/6)(1/6)=1/108 and normalized pullback reference nu^3.

Relative entropy is invariant under these product diffeomorphisms. Therefore, exactly,

 KL(pi_s^rec|mu^3)=log9+(1/2)sum_{k=1}^2 KL(P_s^k|nu^3)
                 =log9+(1/2)sum_k H(P_s^k)-3H(f).          (13)

All quantities are finite. Combining(10),(12),(13), with s=epsilon, yields

 integral c_alpha dpi_epsilon^rec=E+d epsilon+o(epsilon),
 KL(pi_epsilon^rec|mu^3)=d log(1/epsilon)+C_*-d+o(1),

and hence

 E_epsilon<=E+d epsilon log(1/epsilon)+C_*epsilon+o(epsilon). (14)

This construction supplies finite competitors for every positive epsilon (any fixed positive diffusion time suffices outside the asymptotic range).

On the compact product of the supports, c_alpha is nonnegative lower semicontinuous, and relative entropy is lower semicontinuous. Compactness of the marginal constraint set and a finite competitor give existence of a minimizer for every epsilon>0. Strict convexity of relative entropy on finite densities gives uniqueness: two distinct minimizers would have a midpoint with strictly lower objective. The minimizer is permutation invariant because the objective and constraints are invariant. No assertion of strict positivity of its density is needed.

## 7. Symmetric zero-temperature optimizer

The source contact certificate implies that every unregularized optimizer is supported on the twelve contact graphs. Any permutation-invariant such coupling can be described by measures eta_k on the central parameter, with mass eta_1(Q)+eta_2(Q)=1, followed by uniform permutation. Its outer Y_k marginal is (Y_k#eta_k)/3. Comparing with the prescribed (Y_k#nu)/6 gives eta_k=nu/2, by injectivity. Thus its law is exactly pi_0. This proves uniqueness only within the permutation-invariant class.

Equation(14), KL>=0, and lower semicontinuity show that every weak cluster point of pi_epsilon is an unregularized optimizer. Its symmetry passes to the limit, so it is pi_0. Compactness then gives pi_epsilon -> pi_0 weakly. These conclusions use elementary symmetry and source geometry; they are not separate nominated operations.

## 8. Matching lower coefficient

On the compact physical support K^3 define the finite measure

              tau_epsilon=epsilon^(-d) exp(-R/epsilon)mu^3,

with exp(-infinity)=0. We compute its weak limit without assuming that the singular Coulomb cost is smooth across forbidden products.

Every forbidden component pattern has a positive minimum of R. To prove this, R is lower semicontinuous there, tends to infinity at collisions, and has no zero on that compact pattern by the source's exact contact characterization. There are finitely many patterns. Their tau_epsilon masses therefore tend to zero exponentially.

On the ordered k-th allowed pattern use (t0,t1,t2) in Qbar^3. The reference has density f(t0)f(t1)f(t2)/108. Set tj=t0+sqrt(epsilon)wj for j=1,2. By(1), the integrands after multiplying by epsilon^(-d) are dominated by a constant times f(t0)exp(-c|w|^2). Taylor expansion gives

 r_k(t0,t0+sqrt(epsilon)w1,t0+sqrt(epsilon)w2)/epsilon
                      ->(1/2)w^T K_k(t0)w.

Extend f by zero; boundary points have zero f mass. Dominated convergence, also with a continuous test function on K^3, gives a limiting measure tau on each graph whose density in central parameter t is

                (2pi)^d f(t)^3/(108 sqrt(det K_k(t))).      (15)

The other eleven graph pieces are given by the appropriate permutations and k. Thus tau_epsilon -> tau as finite measures, including convergence of total masses.

For any probability pi with the exact marginals and finite objective, direct substitution gives

 KL(pi|tau_epsilon)
    = [integral c_alpha dpi+epsilon KL(pi|mu^3)-E]/epsilon
                                                    -d log(1/epsilon). (16)

Here KL relative to a finite nonprobability reference has the same integral definition. Its variational formula on a compact space is

 KL(P|M)=sup_{phi continuous} [integral phi dP-log integral exp(phi)dM].

It follows by the Gibbs inequality and approximation of the log density; equivalently normalize M and use the probability-reference formula. This also proves joint lower semicontinuity under P_n -> P and finite M_n -> M with positive limiting mass, by taking the supremum after the limit for each fixed continuous phi.

Apply this to pi_epsilon -> pi_0 and tau_epsilon -> tau. On each graph pi_0 has density f/12, while tau has density(15). Hence

 d pi_0/d tau=9 sqrt(det K_k)/[(2pi)^d f^2]

at f-positive points, and direct integration gives KL(pi_0|tau)=C_*. From(16),

 liminf [E_epsilon-E-d epsilon log(1/epsilon)]/epsilon>=C_*.

Together with(14), this proves the frozen expansion of E_epsilon.

## 9. Separate transport and entropy expansions

Let h_epsilon=KL(pi_epsilon|mu^3). For any eta>0, optimality at eta and use of pi_epsilon as a competitor give

 E_eta<=E_epsilon+(eta-epsilon)h_epsilon.

Fix lambda>1 and use eta=lambda epsilon and eta=epsilon/lambda. The just-proved value expansion bounds h_epsilon between

 d log(1/epsilon)+C_*-d lambda log(lambda)/(lambda-1)+o(1)

and

 d log(1/epsilon)+C_*-d log(lambda)/(lambda-1)+o(1).

First let epsilon decrease to zero at fixed lambda, then lambda decrease to1. Both constants tend to C_*-d. Thus

 h_epsilon=d log(1/epsilon)+C_*-d+o(1).

Subtract epsilon h_epsilon from E_epsilon to get integral c_alpha dpi_epsilon=E+d epsilon+o(epsilon). No unjustified differentiation of an o(epsilon) remainder is used.

This completes the author argument at every clause of the unchanged frozen scope. Independent review must assess the stochastic confinement, finite-energy change of drift, parametrix orientation, entropy transfer, all source interfaces and the contribution comparison. Artifact validation cannot settle them.
