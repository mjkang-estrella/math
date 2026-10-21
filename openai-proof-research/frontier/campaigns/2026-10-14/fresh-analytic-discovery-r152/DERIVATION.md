# Canonical hard-sphere fluctuations: integrated reduction, PREFREEZE

No theorem is frozen or nominated. These are research calculations and a precise compatibility obligation, not a full author proof. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs are stipulated. No correctness/contribution grade or campaign count is assigned.

## Exploratory full scope

The question tested is the fixed-particle-number analogue of Source364, including the functional topology already paid for its original ensemble by R025. This is an ensemble change, not a retry of the accepted path-space theorem. Space is R^3_x times R^3_v. Let f0 be a smooth nonnegative probability density with, for some beta>0,

 ||f0||Bol,2beta + ||grad_x f0||Bol,2beta < infinity,
 ||g||Bol,beta = sum_{a in Z^3} sup_{|x-a|<=1,v} exp(beta|v|²)|g(x,v)|.

Assume the hard-sphere Boltzmann equation has a nonnegative classical solution f with initial value f0 on the entire prescribed finite interval [0,T], and sup_{t,x,v} exp(2beta|v|²) f(t,x,v)<infinity. The collision convention is [(v-v*) dot omega]_+ with ordinary surface measure and the elastic scattering map of H01. No equilibrium or spatial homogeneity is added.

For every sufficiently small epsilon>0 put mu=epsilon^-2 and n=floor(mu). The canonical initial probability on n labelled particles is Z_n^-1 1_{D_n} product f0(z_i) dz_i, where D_n imposes |x_i-x_j|>epsilon. Evolve the actual deterministic elastic hard-sphere flow. Define X_epsilon(t,phi)=mu^-1/2 [sum_{i=1}^n phi(z_i(t))-E_can sum_{i=1}^n phi(z_i(t))]. The explored conclusion is joint convergence for every finite list of real compact smooth tests in D([0,T],R^d), with the J1 topology and C-tightness, to the continuous Gaussian field described below. This entire question remains unproved here. It is not a frozen exact theorem or a weakened substitute for any old scope.

## Gaussian candidate is already paid at the abstract level

Let U(s,t) be H02's backward dual of the homogeneous linearized Boltzmann evolution about f. With H's initial isonormal field I0 on L²(f0 dz) and independent collision martingale noise W, H's Gaussian field is

 zeta_t(phi)=I0(U(0,t)phi)+integral_0^t W(ds,U(s,t)phi).

Set G=I0(1), a_t(phi)=integral f0 U(0,t)phi, and zeta_can,t(phi)=zeta_t(phi)-a_t(phi)G. Then Var(G)=1 and Cov(zeta_t(phi),G)=a_t(phi), so its covariance is exactly K(t,phi;s,psi)-a_t(phi)a_s(psi). Its initial covariance is integral f0 phi psi - integral f0 phi integral f0 psi. Its driving collision noise is unchanged. This construction directly proves positivity of the proposed covariance; H's regularity of U and Gaussian process construction gives the same continuous finite-test realization. It does not prove microscopic convergence.

The number response is h_t=S(t,0)f0. It is generally not f_t. The tentative amplitude/time-scaling expression in the earliest FEASIBILITY note is discarded; the transport term prevents that shortcut. If one obtained a joint conditional limit at (n-E_GC N)/sqrt(mu)->a0, its uncentered Gaussian shift would be a0 a_t. Exact canonical centering removes that shift only after a valid conditional mean argument, which is not supplied by weak convergence alone.

## Strongest initial reduction

The detailed calculations are in notes/INITIAL-CALCULATIONS.md and notes/CANONICAL-BLOCKS.md. They use H02's proved Mayer tree bound and the actual finite-label polymer convergence criterion and leaf-integration proof of Pulvirenti–Tsagkarogiannis (PT), rather than invoking equivalence of ensembles as a slogan.

Write rho0=int f0 dv and b=(4pi/3)||rho0||infinity epsilon³. The number partition coefficients obey |a_k|<=k^(k-2)b^(k-1)/k!. For lambda comparable to mu, all fixed logarithmic derivatives beyond the ideal gas have size O(mu epsilon). The inequality 1-cos(k theta)<=k²(1-cos theta) gives the whole-circle number bound |E_lambda exp(i theta N)|<=exp[-c lambda(1-cos theta)]. Thus the lattice local limit is available, not just a central limit theorem. At n=floor(mu),

 P_GC(N=n) ~ epsilon (2pi)^(-1/2) exp(-a0²/2),
 a0=(4pi/3) integral rho0².

The excluded-volume mean shift is of fluctuation size and has been retained.

For bounded complex u with small sup norm set m(u)=1+integral f0u and p_u=f0(1+u)/m(u). The exact canonical factorial generating identity is

 log E_can product_i(1+u(z_i)) = n log m(u)+R_n(u)-R_n(0).

R_n is the convergent logarithm of the finite exclusion-polymer partition. The label-rooted smallness parameter is nb=O(epsilon). Weighted cluster convergence gives |R_n|<=C n²b with an exponential reserve in the total number q of integration copies. Differentiating h times gives an explicit signed-measure kernel; allocation of numerator and denominator derivatives costs at most C_h(1+q)^h, absorbed by that reserve. Importantly, repeated appearances of a label in different polymer occurrences are separate integration copies, not geometrically equal positions. Consequently for every fixed h,

 c_h^ideal=(-1)^(h-1)(h-1)! n mu^-h f0^tensor h,
 ||c_h-c_h^ideal||TV <= C_h epsilon mu^(1-h).                  (IB)

The variation assertion uses termwise absolute marked measures, not merely bounds on product test functions. Scalar exponential tilts give cumulants n kappa_h(phi(Z))+O_h(n epsilon), hence the canonical initial finite-test Gaussian bridge. These are source/classical compositions. No substantial new operation is claimed for (IB).

## Global canonical links do fit finite-complexity geometry

The exact finite connected algebra in H04 does not require global Poisson independence; it expands the actual initial connected blocks. Ideal canonical blocks can be represented by abstract trees with an edge factor mu^-1. These edges enforce algebraic dependence, not spatial closeness. They must be erased before making physical merger-coordinate changes.

For a combined connected diagram let g be its abstract edges, p its independent physical initial links, m its birth lines, h its top roots, and c_geom the number of components after deleting the abstract edges. The physical dynamic merger count is m-c_geom-p. Use one integrable spatial anchor in EACH geometric component. The normalization then is

 mu^(m-h) epsilon^[2(m-c_geom-p)] epsilon^(3p) mu^-g
 = mu^(c_geom-h-g) epsilon^p <= mu^(1-h) epsilon^p,           (S)

because c_geom<=g+1. Abstract cycles have extra mu^-1. Physical dynamic cycles use H's existing redundant-contact smallness within their physical component. Thus a global link is not an unpaid spatial pin. For fixed complexity, fresh-label denominators, shell-energy flux integration, and time entropy retain H's C_K(1+n)^d_K(CT/sqrt(L))^n majorant without a new ordinary-atom factorial. This settles the finite-complexity ideal-link scaling issue.

The new leading two-root connection propagates the initial -f0 tensor f0 through two linear-response branches and yields -a_t a_s, with no new collision-noise term. Fixed-complexity insertion, however, does not remove growing-order initial roots or high-complexity tails. It is not a proof of the proposed kinetic theorem.

## The actual uniform interface remains unpaid

H02 provides a pointwise tree envelope for its grand-canonical initial c_h with constants uniform in h, using the coarse kernel 1_{|x_i-x_j|<=epsilon}+epsilon^(1/81), and a sharper arbitrary-accuracy envelope for fixed h. H04–H06 insert these bounds in layered remainders, connected summation, and witness estimates. DHM's actual initial-cumulant proof (2408.07818v3, lines2071–2165) and its full immediate layered recurrence (2168–2291) show why such an input is needed before the contact integrals and cutoff estimates. Its canonical LLN remark is credited; it is not a fluctuation-scale estimate.

A canonical rooted expansion must simultaneously retain the leading nonlocal mu^-1 coefficients, give appropriate pointwise/Gaussian domination through the growing cutoff A0(epsilon), and control the residual terms to arbitrary accuracy where H needs that accuracy. The integrated fixed-h bound (IB) does not permit taking contact traces. A larger epsilon^(1/81) coarse factor may dominate a mu^-1 global edge once the requisite pointwise expansion is proved, but cannot substitute for that proof. PT's corrected v3 two-point theorem includes the finite-volume nonlocal term; the finite-box two-point theorem is not the needed all-order inhomogeneous whole-space interface. Its rooted-polymer proof is a plausible classical route, and no nonroutine obstruction or impossibility is inferred from this unfinished extension.

After that input, one must still carry the canonical estimates through ONE pasted dynamics and one cutoff hierarchy, chosen before the fixed moment order, including stopped variations, high-complexity tails, actual terminal witnesses and R025's collective time shifts and microscopic windows. At bounded complexity the extra spatial anchors in (S) can be shifted along with the original chronology domain; there is no independent reassignment of cut times. Uniform reassembly for the full canonical law has not been proved here.

The stable-radial companion P has a potentially stronger exponential witness schedule, read in its entire closure section together with its initial insertion proof. That schedule still uses its own initial grand-canonical occupancy identity and centered inputs. Its initial insertion expectation is over the original random-number cloud. It is not a free canonical fluctuation bridge; a uniform replacement of its initial input would again require proof. No smooth-potential full theorem is proposed.

## Conditioning route tested rather than dismissed

H's grand-canonical bad-event bound O(epsilon^(1+eta)), eta=1/20, and the proved number local limit give only P_can(bad)=O(epsilon^eta). This suffices to couple uncentered true and pasted observables in probability, but the elementary exact-mean comparison is at most C epsilon^(eta-1), which does not tend to zero. This is a limitation of this bound, not a divergence claim. A direct canonical witness bound o(epsilon), or a genuinely justified conditional uniform-integrability argument, would repair that step.

Alternatively the Fourier coefficient formula involves E_GC[exp(iS/sqrt(mu))exp(i theta N)] over the whole circle. The number-only Fourier bound does not majorize this mixed transform. BGSS's actual short-time factorial-in-order estimate and its generating-functional summation were read; those estimates cannot be restarted by falsely declaring independently refreshed slabs. H's fixed-order bounds on a regular lifespan do not by themselves give the needed uniform complex-activity estimate. No proof here shows that the mixed bound is impossible or that its establishment would necessarily be substantial.

## Decision

PREFREEZE/no nominee. Initial canonical CLT, conditioning probability and ideal-link finite-complexity accounting are useful paid reductions. Neither full-scope closure nor an identifiable nonroutine operation after strongest integrated source/classical composition has been established. No independent review, formal support, manuscript or release was attempted. All old scopes and dispositions, in particular R025, I23 and the user-listed analytic/arithmetic/algebraic targets, remain unchanged.
