# I346 analysis and validation

2026-10-13. Analytic research only; no numerical scan, external full-body retention, git operation or subordinate agent. The complete proof is in [the proposal](../../iterations/i346-ball-slab-crossover-research.md). Status: complete research proof under the stated dependencies, **TECHNICAL / not substantial**, not an independent review or acceptance.

## The estimate that actually needed to be paid

Fixed-R R018 cannot be applied by replacing R with R_epsilon: its compactness argument selected balls using strict scalar uniqueness below R=1/3. At the moving endpoint, a radius-2/9 tube is an additional inner scalar equality case. The necessary lower alternatives are

    ball localized minimum / S -> 2pi,
    cylinder localized minimum >= g(R),

with no error of size o(delta) mistakenly used as o(S). The proof obtains the second inequality exactly and establishes the first by repeating the existing contact argument on a uniformly regular reference interval. There is no unproved parameter-uniform global scalar uniqueness estimate.

## Checks of the extra replacement step

Let a_*=4pi/81. Every radius-1/3 ball projects onto each coordinate circle in an interval of length 2/3. A coordinate tube has volume density a_* along its own axis. Thus the tube portion outside a ball has volume at least a_*/3. Equal volumes give a paired symmetric-difference separation at least 2a_*/3 between the inner orbits. Choosing eta_0=a_*/10 gives disjoint closed neighborhoods without an unspecified separation constant.

The local constraint is only dist(E,inner orbit)<=eta_0; F keeps its complete original class. The direct method applies because the inner orbits are compact and this distance is L1 continuous. A localized minimizer has a zero-deficit endpoint limit and hence has distance tending to zero from its selected orbit. It cannot remain on the artificial neighborhood boundary. Volume-corrected lattice competitors, for sufficiently small fixed comparison balls, stay interior: their total L1 displacement is bounded by C times the scalar symmetric difference. For flow parameter s this last fact follows from the BV transport bound |Phi_s(A) triangle A|<=C|s|P(A), by approximation and integration along the smooth flow.

At every cylinder/slab equality limit, including one-face tangency, an inner boundary patch stays strictly inside the occupied slab. The other face or an exterior transverse strip gives an outer patch outside the tube. These provide an invertible diagonal two-volume derivative. There is no requirement that arbitrary competitors themselves have clean free patches; smooth Jacobian integrals remain invertible for nearby measurable sets. Large comparison balls and larger-perimeter comparisons are handled separately, ensuring every scalar quasiminimality quantifier is covered.

The graph conclusion is invoked only for these exact minimizing replacements. A near-minimizer approaching a selected class is bounded below by its local minimum; no transfer of graph regularity to that original near-minimizer is needed.

## Cylinder calculation, including mean and translation modes

Use X(s,theta)=(s,(rho+u)cos theta,(rho+u)sin theta). Its cross product gives the exact density

    sqrt((rho+u)^2(1+u_s^2)+u_theta^2),

and its volume is (1/2)integral(rho+u)^2 ds dtheta. At exact volume pi rho^2, integral u=-(1/(2rho))integral u^2. In particular the mean is quadratic, not zero. Area expansion after this substitution is

    (1/2)integral [u_s^2+rho^-2(u_theta^2-u^2)]rho ds dtheta
      +o(1)||u||_H1^2.

The eigenvalues are 4pi^2 k^2+(m^2-1)/rho^2. Transverse translations are the two modes (k,m)=(0,+/-1); reference centering removes their moments exactly. Axial translations have zero normal component. The constant mode is negative, but the exact volume identity bounds its coefficient by the square of the nonconstant L2 norm. The other modes have the uniform positive lower bound min{4pi^2-rho^-2,3rho^-2}; at rho=2/9 the first term is 4pi^2-81/4>0, already from pi>3. Ratios to the H1 weights give uniform full-norm coercivity.

The quadratic mean and area remainder can therefore be absorbed, giving P(E)>=2pi rho+c||u||_H1^2. In particular, for local minimizing replacements with energy <=g(R), equality is forced: u=0 and P(F)=2. This works even when delta/S tends to infinity. No error term is normalized by S on this branch, and no assumption that a cylinder globally minimizes below volume 4pi/81 is made.

For the elementary penalty,

    rho(1/3)=2/9,
    R_*-rho_*=1/9,
    g(R)=4pi R^(3/2)(1/sqrt(3)-sqrt(R)),
    g(R)/delta=4pi R^(3/2)/(1/sqrt(3)+sqrt(R)).

The last expression tends to 2pi/3. Direct differentiation gives g'(1/3)=-2pi/3. These exact calculations validate both the scaling and the sign.

## Ball lower passage audit

The reference radius, local chart denominators, sphere spectrum, free patch distances and two-volume derivatives remain uniformly controlled for R in a sufficiently small compact interval ending at 1/3. None involves the spectral or topological distance to the globally competing cylinder. The compactness selection of a ball is supplied instead by the separated local constraint.

The small quantities used at the contact circle are the fixed finite spherical modes, with C1 norm O_N(epsilon/sqrt(ell)), and the quadratic spherical mean O(S). General C1 graph errors are not declared o(epsilon). The ACTUAL inverse horizontal map and ACTUAL multiplicative coefficient remain in the high-mode transformation. Its gradient losses are absorbed through the fixed high-frequency spectral estimate before epsilon tends to zero.

The two annuli are disjoint on the sphere. Localizing each surface energy and then sharing it gives coefficient 1/4. Circle averages yield capacity 2pi/log(b/a); a=c sqrt(epsilon) gives log(b/a)=ell/2+O(1), hence 4pi/ell per relative height. The two positive-part constraints yield a sum at least 2epsilon^2 in the final c->0 limit. Thus the final coefficient is (1/4)*(4pi)*2=2pi. This independently checks the factor, lower-face sign and arbitrary normal drift.

Parameter order is zeta, then fixed chart radius, Young parameter and finite spectral cutoff, then fixed c, then the moving (R_n,epsilon_n) sequence; c,zeta go to zero last. Uniformity near R_* permits this order without substituting into a fixed-R theorem or requiring a moving spectral cutoff.

The same positive-part inequality, combined with the saturated ball local minimum, gives h=o(epsilon) for exact replacements after reference centering. The proof first derives |h|=O(epsilon); subsequential H=h/epsilon must satisfy (1+H)_+^2+(1-H)_+^2<=2, forcing H=0. This is a consequence of the existing sharp contact estimate, not a new rigidity mechanism.

## Near-minimizers and what morphology means

The exact identity L=min{M_B,g} and the positive gap between the two normalized costs select a single endpoint class for arbitrary near-minimizers away from lambda=3. This is paired L1 selection, including axis orientation and normal placement. At lambda=3 there are asymptotically minimizing representatives of both separated classes. No exact finite-parameter coexistence or transition uniqueness follows.

Topology would be an inappropriate conclusion for arbitrary near-minimizers. For either a smooth ball recovery or a centered cylinder competitor, choose a fixed point strictly inside F and outside E, with positive gaps. Add an inner spherical satellite of radius t=epsilon^2 at that point, and remove its volume from E by a contracting smooth bump on a free inner patch. The exact bump parameter is O(t^3), by a nonzero volume derivative; its contraction preserves inclusion. F is unchanged, both target volumes remain exact, and the added perimeter is O(t^2)+O(t^3)=o(S). This gives a disconnected inner near-minimizer whenever the starting recovery is selected or at the tie. The original admissible class thus genuinely retains rough/topologically different competitors.

## Contribution check

The endpoint is an energy crossing, not a Jacobi degeneracy. The first sphere mode after translations has eigenvalue 4/R_*^2=36. The cylinder mode after translations has eigenvalue 4pi^2-81/4>0. Ordinary local stability applies on both wells; only the existing logarithmic contact estimate is singular. The extra localization and exact cylinder classification are useful technical deductions. They do not establish a new substantial lower passage, new sharp quantitative stability law for original near-minimizers, or new contact law.

No proof assistant or independent reviewer was used. An optional inline SymPy simplification could not start because SymPy is absent; it wrote no file and provided no evidence. All displayed algebra and spectral signs were checked analytically. The complete chain has no remaining leading-order estimate as written, but this is a research proof, not an independent PASS gate.
