# Canonical initial gas and the regular-lifespan reduction — prefreeze derivations

This is a research derivation, not a frozen nominee, review, or grade. Only the Source364 family is under consideration. Write p=f0, a probability density on R^3_x x R^3_v satisfying the source's spatially summable Gaussian assumptions. Put mu=epsilon^{-2}, n an integer with |n-mu|<=C sqrt(mu), and b=(4pi/3)||rho0||_infinity epsilon^3. Then d=nb=O(epsilon). The canonical law is

  P_n(dZ_n)=Q_n[p]^{-1} product_i p(z_i) product_{i<j}(1-chi_ij) dZ_n,
  chi_ij=1_{|x_i-x_j|<=epsilon}.

There is no additional thermodynamic limit. Q_n is a probability of exclusion under n independent p-particles, not the grand partition function. Deterministic hard-sphere flow is the same flow as in the source on its full-measure domain. All conclusions below about time zero refer to this exact excluded law, not to the unexcluded binomial process.

## 1. Nonemptiness, partition ratios, and finite-root positive bounds

For every configuration of k points, the p-mass excluded for the next point is at most kb, by the union bound and the definition of b. Consequently, for kb<1,

  (1-kb)Q_k[p] <= Q_{k+1}[p] <= Q_k[p].                         (1.1)

Thus Q_n>0 when nb<1. The assumptions are compatible for every sufficiently small epsilon and n=floor(mu), without any extra spatial support or density restriction. Integrating all but h fixed points and discarding their exclusions with the integrated points gives the normalized factorial marginal bound

  F_h^can(Z_h) <= (n)_h mu^{-h} p^h(Z_h) Q_{n-h}/Q_n
              <= (n/mu)^h (1-nb)^{-h} p^h(Z_h).              (1.2)

For h=polylog(1/epsilon), the prefactor is exp(O(h epsilon))=1+o(1). This is a positive marginal estimate, not a connected estimate. It does not by itself restart a long-time fluctuation expansion.

There is also an exact insertion coupling useful for testing conditioning arguments. The marginal of the first n coordinates under P_{n+1} is P_n reweighted by

  A_n(Z_n)/E_{P_n} A_n,
  A_n(Z_n)=integral p(z) product_i(1-chi(z,z_i)) dz,
  1-nb <= A_n <=1.

Its total variation distance from P_n is at most nb/(1-nb) (the bound is deliberately nonoptimal). A maximal coupling then appends one extra particle with failure probability O(d). After w insertions near n~mu the accumulated initial failure is O(w epsilon). This rigorously couples nearby initial particle counts; it does not bound the number of particles whose trajectories later differ.

## 2. Exact canonical polymer formula, with a quantitative convergence budget

For a normalized complex one-particle measure q and V subset [n], |V|>=2, let

  w_V(q)=integral product_{i in V}q(dz_i) U_V(Z_V),
  U_V=sum_{connected graphs on V} product_{edges}(-chi_ij).

Decomposing each graph into its connected components gives the exact finite identity

  Q_n[q]=sum_{pairwise disjoint polymer collections} product_V w_V(q). (2.1)

The repulsive tree-graph identity yields |U_V|<=sum_{trees on V} product chi. A concise justification is the rooted breadth-first partition of connected graphs: each class contains a minimal tree and arbitrary edges in its allowed closure; summing those edges produces product(1-chi), of magnitude at most one. Integrating a tree from its leaves under p gives b^{|V|-1}, hence

  |w_V(p)| <= |V|^{|V|-2} b^{|V|-1}.                          (2.2)

For a complex external field u with ||u||_infinity<=1/4, set m(u)=integral p(1+u), p_u=p(1+u)/m(u). Then |p_u|<= (5/3)p, so the right side of (2.2) is multiplied by (5/3)^{|V|}. For any fixed A>0, using binom(n-1,k-1)<=n^{k-1}/(k-1)! and k^{k-2}/(k-1)!<=e^k,

  sum_{V contains i}|w_V(p_u)| exp(A|V|)
  <= sum_{k>=2} e^{(A+1)k}(5/3)^k d^{k-1} <= C_A d.         (2.3)

Choose d small enough that C_{A+1}d<=1. For any V, the sum of the exponentially weighted activities incompatible with V is then at most |V|. This gives an absolute connected polymer expansion with an exponential budget in the total number S of particle occurrences in its polymers.

For completeness, the needed abstract estimate can be obtained without a thermodynamic-limit theorem. Apply the same repulsive tree-graph inequality to the incompatibility graph of an ordered polymer list. The sum of rooted trees is bounded by the monotone iteration

  R_0(V)=a_V,
  R_{k+1}(V)=a_V exp(sum_{W incompatible V} R_k(W)),
  a_V=|w_V| exp(A|V|).

Condition (2.3), with one spare exponential, inductively gives R_k(V)<=a_V exp(|V|). Summing the rooted majorant bounds the absolute connected series. The formal logarithm identity follows first in a neighborhood of zero activities by finite polynomial expansion, and the absolutely convergent series continues it to the above polydisc. In particular Q_n[p_u] has no zero there. Summing the rooted bound over V, and using sum_V <=sum_i sum_{V contains i}, gives

  sum_{connected polymer clusters}|coefficient| product |w_V| exp(A S)
       <= C_A n d.                                          (2.4)

The leading cluster is one two-label polymer. The absolute sum of all remaining clusters is at most C_A n d^2: one polymer of size >=3 costs two powers of d; a cluster with >=2 polymers contains at least two physical edges. The same rooted recursion, with a parameter multiplying each physical edge, bounds the terms of degree >=2 by C_A n d^2. This budget is uniform for all n and small d. It is sufficient for all fixed-order integrated derivatives below; it is not yet a spatially resolved root-tree bound.

This is the finite-label canonical construction of Pulvirenti--Tsagkarogiannis, adapted here to an inhomogeneous probability density by the direct leaf integral b. Their uniform-box thermodynamic limit is not being applied to p. No infinite-volume equivalence of ensembles is assumed.

## 3. Derivatives as measures: total variation, not only diagonal test bounds

The factorial generating functional is exactly

  log E_{P_n} product_i(1+u(z_i))
   =n log m(u)+H_n(u)-H_n(0),
  H_n(u)=log Q_n[p_u].                                       (3.1)

In a cluster term of H_n let S=sum_V |V|, counting repeated polymer occurrences. Before normalization its product of activities is multilinear in S copies of p(1+u); the denominator is m(u)^S. For the hth derivative at zero, select a<=h distinct occurrence slots and assign a of the h external labels to them; differentiate the denominator h-a times. The latter derivative is

  (-1)^{h-a} (S)^{overline{h-a}} p^{tensor(h-a)}.

Every derivative is therefore an explicitly defined finite signed measure on h external phase points. Its total variation is bounded by

  sum_{a=0}^h binom(h,a)(S)_a(S)^{overline{h-a}}
     times the original absolute tree majorant
   <= (C_h)(1+S)^h times that majorant.                       (3.2)

One spare exponential in (2.4) absorbs this polynomial. This proves, for every fixed h,

  ||D^h H_n(0)||_TV <= C_h n d.                              (3.3)

It also proves the O(C_h n d^2) version after removing the two-label cluster. This is a total-variation assertion because the derivative is represented term by term as a measure and its absolute variation is summed; it is not inferred from bounds on products of bounded tests. Constants can, for example, be taken of order (C h)^{C h}; only fixed-order uses are made here.

If c_h^can denotes the factorial cumulant density normalized by mu^{-h}, differentiating (3.1) yields the explicit decomposition

  c_h^can = (-1)^{h-1}(h-1)! n mu^{-h} p^{tensor h}+r_h,
  ||r_h||_TV <= C_h n d mu^{-h}.                             (3.4)

In particular mu c_2^can -> -p tensor p in total variation, and F_1^can ->p. The ideal fixed-count term is order mu^{1-h}; it does not disappear with exclusion. For h>=2 it is larger, in integrated scale, than the grand-canonical purely geometric initial cumulant epsilon^{3(h-1)}.

## 4. Exact first-order canonical bias

Let a_epsilon(z)=integral chi(z,z')p(z') dz' and A_epsilon=integral p a_epsilon. The two-label polymer contribution to H_n is

  -binom(n,2) integral chi(z,z')p_u(z)p_u(z') dz dz'.

Differentiating at u=0 in a bounded direction phi, and using the remainder budget in Section 3, proves

  E_can pi_0(phi)
   =(n/mu)p(phi)
    - n(n-1)/mu [p(phi a_epsilon)-p(phi) A_epsilon]
    + O(||phi||_infinity n d^2/mu).                         (4.1)

The source gradient assumption implies rho0 is bounded Lipschitz and integrable. Thus a_epsilon(z)=v_3 epsilon^3 rho0(x)+O(epsilon^4), uniformly, v_3=4pi/3, and A_epsilon=v_3 epsilon^3 integral rho0^2+O(epsilon^4). Along any sequence with (n-mu)/sqrt(mu)->kappa,

  epsilon^{-1}[E_can pi_0(phi)-p(phi)]
    -> kappa p(phi)
       -v_3[p(phi rho0)-p(phi) integral rho0^2].              (4.2)

For phi=1 this gives exactly kappa; the exclusion correction has zero total mass. The grand-canonical correction instead equals -v_3 p(phi rho0), with a particle-number deficit. Equating the two ensembles at the fluctuation scale without this mass compensation is incorrect. Formula (4.2) is a time-zero calculation only. It does not license Boltzmann-density centering at later times.

## 5. Initial canonical Gaussian law, derived independently

For a fixed bounded real phi set u_theta=e^{theta phi}-1. Then

  log E_can exp(theta sum_i phi(z_i))
   =n log p(e^{theta phi})+H_n(u_theta)-H_n(0).

On a theta-disc with radius c/||phi||_infinity the cluster series has the same absolute budget. Each k-th ordinary cumulant therefore equals

  kappa_k(sum_i phi)=n kappa_{k,p}(phi)+O_k(n d ||phi||_infinity^k). (5.1)

The same holds for mixed cumulants of any fixed finite list. After exact centering and division by sqrt(mu), the second cumulant tends to

  p(phi psi)-p(phi)p(psi),                                   (5.2)

and all fixed k>=3 cumulants are O_k(mu^{1-k/2}). A direct characteristic-function argument avoids any moment-determinacy shortcut: Taylor the analytic logarithm at theta=i t/sqrt(mu) through order two; its third derivative is bounded by C n ||phi||^3 uniformly on a fixed disc, so the remainder is O_t(n mu^{-3/2})=O_t(mu^{-1/2}). Equations (5.1)--(5.2) give the finite-dimensional initial Gaussian law by applying this argument to each fixed linear combination. This static conclusion is a classical canonical-cluster consequence and is not being submitted as a substantial new result.

## 6. A uniform local limit for the particle count itself

The grand-canonical normalization admits the usual absolutely convergent Mayer series

  log Xi(lambda)=lambda+sum_{k>=2} lambda^k B_k/k!,
  |B_k|<=k^{k-2}b^{k-1},                                   (6.1)

by the same repulsive tree majorant and leaf integrations. This identity is also the source's initial connected expansion with no displayed roots. It holds for complex lambda with e|lambda|b small. Its coefficients B_k are real. For real lambda>0 and |t|<=pi,

  log E_lambda exp(itN)=log Xi(lambda e^{it})-log Xi(lambda).

Since 1-cos(kt)<=k^2(1-cos t), (6.1) implies

  Re log E_lambda exp(itN)
   <=-lambda(1-cos t)+C lambda^2 b(1-cos t)
   <=-c lambda t^2                                          (6.2)

when lambda b is small. There is no assertion that a marked dynamical characteristic function enjoys (6.2).

Differentiating (6.1) with lambda d/dlambda gives

  m_lambda=E N=lambda-lambda^2 A_epsilon+O(lambda(lambda b)^2),
  Var N=lambda+O(lambda^2 b),
  |kappa_j(N)|<=C_j lambda                                  (6.3)

for fixed j. At t=u/sqrt(lambda), the centered logarithm tends to -u^2/2 uniformly on compact u-sets. Fourier inversion and (6.2), after the change of variable u=t sqrt(lambda), give an L1-dominated-convergence proof of the local limit:

  sup_{k in Z} | sqrt(lambda) P_lambda(N=k)
       -(2pi)^{-1/2}exp(-(k-m_lambda)^2/(2lambda)) | ->0.     (6.4)

Uniformity in k follows by taking the L1 norm of the difference of the Fourier integrands; the oscillatory factor has modulus one. On |u|<=pi sqrt(lambda), (6.2) is bounded by exp(-c u^2); extend the integrand by zero outside this interval. This also proves (6.4) uniformly for lambda/mu in any fixed neighborhood of 1 with lambda b->0.

With lambda=mu and (n-mu)/sqrt(mu)->kappa, write R2=integral rho0^2. Then

  P_mu(N=n)=epsilon (2pi)^{-1/2}
             exp(-(kappa+v_3 R2)^2/2)+o(epsilon).            (6.5)

This is an actual local limit calculation for the count. It controls the denominator in conditioning. It does not control the joint numerator containing a dynamical observable.

## 7. The propagated rank-one correction and its compatibility checks

The source collision-invariant identities give A_t 1=0, U(r,t)1=1 and C_t(1,h)=0. The global particle-count mode can equivalently be treated directly in the bounded record expansion, since N is conserved; no topology on noncompact test functions is being silently substituted. At the Gaussian level let M be the initial total-mass mode, Var(M)=p(1)=1. Put

  m_t(phi)=integral p(z) U(0,t)phi(z) dz.

The source covariance then gives Cov(zeta_t(phi),M)=m_t(phi). Therefore a centered Gaussian field with the fixed-count initial law, the same propagator and the same collision noise has covariance

  K_can((t,phi),(s,psi))=K_gc((t,phi),(s,psi))-m_t(phi)m_s(psi). (7.1)

This is positive semidefinite: it is the covariance of zeta_t(phi)-m_t(phi)M. At time zero it equals (5.2); its total mass mode vanishes, and its noise still annihilates all collision invariants. The mass constraint alone removes only the mass direction. No fixed momentum or energy constraint is imposed.

The correction is not generally -f_t(phi)f_s(psi). If g_t is the first density-amplitude variation of the Boltzmann solution, g_0=p and

  (partial_t+v dot grad_x)g=Q(g,f)+Q(f,g),

then duality gives m_t(phi)=g_t(phi). At t=0,

  partial_t(g-f)|_0=Q(p,p),                                 (7.2)

which need not vanish. Compatible examples exist: take p(x,v)=rho(x)M_A(v), rho a normalized smooth spatial Gaussian and M_A a normalized anisotropic Gaussian with positive definite nonscalar quadratic form A. Choose the source beta smaller than one quarter of the least eigenvalue of A, so all required Gaussian and spatial-gradient bounds hold. A nonempty regular interval exists for this example by the following local construction. Set beta(t)=beta_0-t with beta_0 below the initial Gaussian exponent and choose T_0<beta_0/2. In the norm sup_{t<=T_0,x,v} exp(beta(t)|v|^2)|f(t,x,v)|, energy conservation in a collision gives the bilinear Duhamel bound C(sqrt(T_0)+T_0)||f||||g||: the single hard-sphere velocity factor is bounded by C(1+(t-s)^{-1/2}) after the Gaussian loss beta(s)-beta(t). Transport does not increase the spatial supremum. The Duhamel map is therefore a contraction on the ball of twice the initial norm for sufficiently small T_0. Nonnegativity follows by approximating the collision rate by min(B,M), using the positive gain/loss integrating-factor formula, and passing to the same contraction limit as M tends to infinity. The differentiated equation gives the same contraction estimate for the spatial gradient. The spatially summable bounds then follow from the Volterra argument of DHM v3, Appendix A, Proposition A.1, whose proof was read here: dyadic free-transport spatial displacements are absorbed by the spare Gaussian factor, leaving an integrable (t-s)^{-1/2} kernel. Taking T<=T_0 yields the required nonempty regular interval. This local existence calculation is only a compatibility check; it is not an extension of the source lifespan. Q(M_A,M_A) is nonzero: for an open set of incoming pairs and collision normals the quadratic form in the relative velocity changes under collision, so M_A(v)M_A(v_*) differs from its postcollisional product. The symmetrized entropy-production integral has strictly positive integrand on such a set; if Q vanished that integral would be zero. Thus (7.2) is a real distinction. Every fixed real kappa is also compatible with n=floor(mu+kappa sqrt(mu)); no purported free count parameter is forced by exclusion.

At time zero the difference of canonical and grand-canonical deterministic biases is

  sqrt(mu)(E_can pi_0(phi)-E_gc pi_0(phi))
       ->(kappa+v_3 R2)p(phi),                              (7.3)

consistent with conditioning the Gaussian mass mode at value kappa+v_3 R2. This consistency does not prove the analogous identity at positive times.

## 8. Why the now-proved count local limit is still insufficient

For a fixed dynamical fluctuation vector Y_epsilon, conditioning exactly on N=n requires

  E[e^{it dot Y};N=n]
     =(2pi)^{-1} integral_{-pi}^pi e^{-iun}
          E[e^{it dot Y+iuN}] du.                           (8.1)

The unmarked estimate (6.2) cannot be applied to the expectation inside (8.1). Its factor e^{it dot Y} is a function of the whole initial state through the dynamics. A sufficient missing estimate, in addition to the correct joint central-window limit, is

  lim_{A->infinity} limsup_{epsilon->0} sqrt(mu)
    integral_{A/sqrt(mu)<=|u|<=pi}
       |E[e^{it dot Y+iu(N-m_mu)}]| du =0                    (8.2)

for every fixed t. At t=0 this follows from (6.2); at t!=0 no such bound has been established here or extracted from the source. To replace grand-canonical by exact canonical centering one also needs the corresponding first-moment conditional convergence/uniform integrability, or a separate canonical mean estimate; a bounded characteristic function statement alone does not provide it.

The logical distinction is substantive. Let N_mu be Poisson(mu), n_mu=floor(mu), and G an independent standard Gaussian. Set Y_mu=G+1_{N_mu=n_mu}. The pair ((N_mu-mu)/sqrt(mu),Y_mu) has the usual independent Gaussian weak limit, and N_mu has a uniform local limit; however Y_mu conditioned on N_mu=n_mu has law G+1. Thus joint weak convergence plus the count local limit cannot justify the desired conditional limit.

Similarly, applying the source coupling bound through conditioning gives only

  P_can(bad) <= P_gc(bad)/P_gc(N=n)=O(epsilon^{1/20}),        (8.3)

whereas a bounded empirical sum can differ by O(n) on bad histories. Its normalized expectation error is at most O(sqrt(mu)epsilon^{1/20})=O(epsilon^{-19/20}), which does not tend to zero. The direct canonical version of the source's O(epsilon^{21/20}) bound would suffice, since N is then fixed and the centering error is O(epsilon^{1/20}). Neither version is being conflated with the other.

## 9. Spatially resolved canonical diagrams: an exact construction before the unresolved estimate

The direct route is stronger than simply conditioning the source theorem. It retains the exact canonical initial cumulants in the source's factorial hierarchy. The coefficients mu^j/j! in creation kernels come from the normalization of factorial marginals; they do not require Poisson particle counts. All finite-label expansion identities can therefore be written before using a grand-canonical initial bound. Spectator cancellation and the stopped remainder still have to be estimated with the new initial kernels.

Here is a concrete initial diagram construction. In an ordered connected polymer cluster choose an incompatibility tree on its k polymers. A polymer V_i of size v_i is represented by v_i distinct occurrence slots; its physical Ursell weight is bounded by a physical tree on those slots. For each edge of the incompatibility tree, bound the overlap indicator by the sum over choices of one slot at either end whose particle labels agree. The k-1 chosen overlap edges join distinct polymer blocks in a tree, so their equality constraints have rank k-1. Dropping the remaining within-block distinctness restrictions gives exactly at most

  n^{S-k+1},  S=v_1+...+v_k,

label assignments, with denominators product_i v_i! for the occurrence parametrizations and k! for the ordered polymer list. The physical positions of equal-label occurrences in distinct polymer integrals remain independent integration variables. Identifying these positions would be an error: an incompatibility edge is combinatorial, not a physical contact.

Thus one obtains a positive, explicit two-level majorant with:

* a physical tree of chi_epsilon edges inside each polymer block;
* a tree of combinatorial overlap edges between blocks;
* coefficient n^{S-k+1}/(k! product_i v_i!);
* the h external marks distributed over occurrence slots and normalization tags exactly as in Section 3.

All physical coordinates carry p. This is not a heuristic graph count: it is obtained by applying the two repulsive tree inequalities to the exact logarithm and then summing the specified label equalities. Its fully integrated absolute sum is bounded by Section 3. It also explains the correct scale of a spatially unrestricted edge: after factoring n per particle occurrence, each independent label identification carries n^{-1}. Normalization tags add further global factors and signs. The exact ideal term in (3.4) is kept separately, rather than recovered from a bound.

A useful finite physical-tree estimate can be proved without any diagram limit. Suppose one block has v occurrence vertices, of which r>=1 have prescribed positions. Remove r-1 edges from its tree to leave a forest with exactly one prescribed root in each component. Integrate all v-r remaining vertices along that forest. This costs at most b^{v-r}. The original connected tree also forces all prescribed roots to lie within distance (v-1)epsilon of the first one. Hence its integral is bounded by

  b^{v-r} product_{j=2}^r 1_{|x_j-x_1|<v epsilon}.            (9.1)

For v-r large, the activity factor turns the surplus b-powers into d-powers. For fixed root order, truncating long physical connecting paths can therefore replace a path by a bounded-radius local link plus an arbitrarily high fixed epsilon power, provided the remainder is summed with the correct marked combinatorial budget. The source's packing argument (27 separated root components per auxiliary point) is relevant to a coarse bound uniform in root order. A global overlap edge can connect separated components without a physical auxiliary point and must instead be charged its n^{-1}; it cannot be fed into the source's physical packing count unchanged.

The finite skeleton and (9.1) are established here. What is not established is a uniform resummation of all marked two-level skeletons that gives both of the following interfaces simultaneously:

  |c_h^can(Z_h)| <= (C h)^{C h} p^h(Z_h)
      sum_{T on [h]} product_{ij in T}(chi_epsilon(x_i-x_j)+epsilon^{1/81})   (9.2)

on the polylogarithmic root range demanded by the restarted source proof, with one epsilon threshold independent of h; and, for fixed h,D, an exact signed representation dominated by

  C_{h,D} p^h(Z_h) sum_T product_{ij in T}
      [chi_{C_{h,D}epsilon}(x_i-x_j)+epsilon^D+mu^{-1}],     (9.3)

with controlled remainders under the actual incoming collision charts. A proof of only (9.3) as an abstract measure inequality would still have to retain the representation needed to identify its surviving global edge and show that the other connected terms vanish on those charts. Bounds (9.2)--(9.3) are displayed obligations, not asserted lemmas. The unproved step is a marked resummation with spatial constraints and signs; the finite diagrams and their integrated estimates are not being relabeled as its proof.

One further input does close directly. By (1.2), under P_{n-1} the probability that a particle lies within epsilon of a fixed root is at most (n-1)b/(1-nb). Inserting the fixed root and using (1.1) gives, wherever p>0,

  F_1^can/p=(n/mu)(1+O(d)),                                 (9.4)

uniformly in the root; if p=0 both sides are zero in the underlying density formula. Thus the initial one-root envelope and O(epsilon) closeness are available. This does not supply the connected interfaces (9.2)--(9.3).

## 10. Carrying the two-edge construction through the entire proposed lifespan

The following calculation records exactly how a successful spatial resummation would fit the source, including the part that is already paid. It is not a conditional theorem submitted for acceptance.

Fix the source regular interval [0,T]. The source fixes a large slab number L, tau=T/L, so C tau sqrt(L)<1; L is independent of the fixed cumulant order. A low-complexity diagram has m distinct particle lines, h displayed roots, d independent dynamic merger contacts, p physical initial forest links, and q spatially unrestricted canonical initial links. In an acyclic combined graph with c components,

  d+p+q=m-c.

The existing dynamic charts contribute epsilon^{2d}; physical initial translations contribute epsilon^{3p}; canonical count links contribute mu^{-q}; and the original fresh-label activity is mu^{m-h}. Therefore

  mu^{m-h} epsilon^{2d+3p} mu^{-q}=mu^{c-h}epsilon^p.        (10.1)

This gives the desired mu^{1-h} connected scale, with an extra epsilon for each physical initial forest edge. A global link is never assigned an epsilon^3 volume, and its two endpoint positions are not identified. For diagrams with further combinatorial cycles, the number of independent geometric mergers and the number of global numerical factors must be counted separately; one may not use a redundant-contact normal/time as a free parameter.

For fixed root order and fixed complexity, the number of global links would be bounded. The source's fresh-label factorial accounting then changes only a polynomial degree in the ordinary size, not its exponential base. Its once-counted Gaussian energy and prefix pair-flux summation give

  C_K(1+M)^{d_K}(C tau sqrt L)^M,

where M is the total ordinary size. Because global links carry no velocity derivative or collision flux, they introduce no new Gaussian energy loss in this finite skeleton. These are compatible operations, not reasons to declare the whole extension inaccessible.

The leading connected two-root classes have p=0. The class q=0 is exactly the paid grand-canonical covariance, including the collision noise. A single surviving initial canonical edge has signed weight -p tensor p / mu from (3.4), with two independently propagated linear responses. Its candidate contribution is precisely -m_t(phi)m_s(psi). Initial connected cumulants of order >=3 have the scale mu^{1-h}; after converting factorial to ordinary cumulants, every fixed normalized cumulant of order k>=3 is O(mu^{1-k/2}) if the direct sharp history estimates hold. Thus there is no missing Gaussian algebra after the spatial history estimates: the candidate covariance, noise, invariant constraints and higher-cumulant scaling are fully specified.

The actual unresolved estimate is required twice. First it must allow the source's coarse complexity tail to be removed at every restart, with the root orders, entropy charges and epsilon powers used there, not just for a fixed initial finite skeleton. Second it must allow the bounded-complexity sharp charts and last-contact spatial disintegrations to be applied to the canonical initial remainder. Total variation (3.4) cannot replace this: a kernel of mass a_epsilon concentrated in an epsilon-thick spatial diagonal can have trace of size a_epsilon epsilon^{-3}. Collision traces are not bounded operators on unweighted total variation. The source resolves this issue for its own geometric initial links by retaining their actual position variables; the canonical two-level expansion must receive the corresponding proof.

If these estimates were proved, the source's same Gamma hierarchy and positive bad-history construction would have to be rerun with the canonical initial representation. Its O(epsilon^{21/20}) discrepancy bound would then transfer both laws and exact canonical centering: N=n deterministically, so the normalized mean discrepancy is at most 2||phi||_infinity n/sqrt(mu) times that probability, namely O(epsilon^{1/20}). This explains why a direct canonical estimate would finish the entire regular interval whereas the conditioned estimate (8.3) does not. No growing test list, process topology, mesoscopic scale or attractive-potential fluctuation claim is appended.

## 11. Stopping point and strongest comparison

The derivation closes the initial canonical law, its fixed-order factorial cumulants in total variation, its initial Gaussian law, the first-order bias including the compensating total-mass term, a uniform local limit for the particle count, and the finite two-level initial diagram construction. It also carries the proposed canonical fluctuation extension through the correct dynamic power counting, covariance identification, energy/factorial budget and final coupling/centering requirements.

It does not close either (8.2) with conditional mean control or the simultaneous spatial/resummed interfaces (9.2)--(9.3) and their restart/bad-history use. Consequently no full regular-lifespan canonical fluctuation statement is frozen, and there is no author-proof nominee. These are outstanding proof requirements, not a claim that the extension is false or new to the literature.

The classical canonical polymer method already pays for much of Sections 1--6. The source already pays for the long regular interval, its grand-canonical fluctuations and the chronological-merger machinery. The overlapping original history already develops the finite-test process strengthening. The unproved spatial resummation cannot serve as contribution evidence. This round remains PREFREEZE/no nominee, without any correctness, contribution, acceptance or count assigned here.
