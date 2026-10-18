# Exact lifetime expansion for geometric dynamics

Author mechanism work toward the frozen full target, not a completed proof. Unlike color resampling, this construction retains the absence of a nucleus in some time slices.

Fix a finite observation window [0,T] in rescaled time and put a=r_e/2. The physical interval is [0,aT]. A stationary birth–death process has a Poisson realization by independent particles carrying spatial location, fair color, birth time, and exponential lifetime. Split the particles meeting this interval into:

1. Persistent particles, present throughout: a fair-colored Poisson process of intensity lambda exp(-aT), lambda=e^-2.
2. Initial particles that die before aT: locations of intensity lambda(1-exp(-aT)), with conditional death time and fair independent color.
3. Particles born during (0,aT]: a Poisson process in space-time with rate lambda dz ds, each with independent Exp(1) lifetime and fair color.

These three processes are independent. The third includes particles dying before the interval ends. Its spatial projection has intensity lambda aT; conditional birth time is uniform. Thus the union of nonpersistent particles has spatial intensity lambda h_a where

 h_a=1-exp(-aT)+aT<=2aT.

At a finite list of times each rare particle has a history in {absent,black,white}^n: its presence times form an interval and its color is constant while present. The base particles have constant fair histories. This is an exact representation, not a first-order approximation. Its base is a critical Poisson tessellation at mesh e'=e exp(aT/2). The source amplitude r_e~c_V^-1 e^(3/4) gives r_(e')/r_e->1, since a->0. Therefore this small change in base intensity does not create an unpaid normalization limit.

## Exact finite-volume perturbation series

For finitely many tested quads, first restrict to a bounded box B and a geometry event ensuring all relevant cells are determined inside B. For a bounded test F of finitely many crossing histories, let D_(z,h)F be F with an extra particle of history h at z minus F without that extra particle. The add operators commute, even though the resulting Voronoi cells do not vary linearly. The Poisson perturbation identity gives

 E F(base+rare)=sum_(k>=0) (lambda h_a)^k/k!
   integral_(B^k) E integral D_(z1,h1)...D_(zk,hk)F(base)
                         dnu_a(h1)...dnu_a(hk) dz1...dzk,       (1)

where nu_a is the normalized rare-history distribution. For fixed mesh and finite B this is absolutely convergent by the crude bound 2^k||F||∞ and finite Poisson mass. It follows by differentiating the Poisson intensity parameter or expanding the exponential of the add-minus-identity operator. No uniform-in-mesh convergence follows from that crude bound, since lambda h_a diverges like e^(-5/4).

A uniform proof needs a geometric mixed-difference estimate. Source fixed-tessellation history kernels have the bound C^k k^(-theta k) after multiplying each spatial integral by lambda r_e and dividing by k!. Here the corresponding necessary estimate is the SAME summable bound for the differences in (1), where absence changes the tessellation. There is a plausible route through screened annuli: if a selected addition is irrelevant under every setting of the other particles, its difference cancels; if relevant, its affected region must transmit alternating arms through annuli free of selected locations. But the support radius of an added/deleted cell and the exact necessary arm event must be proved uniformly for all selected subsets. The fixed-tessellation theorem cannot simply be cited for this claim.

## Short-lived particles and why total counting is insufficient

Particles born and dying within the interval have spatial intensity

 lambda integral_0^(aT) [1-exp(-(aT-s))] ds <=lambda(aT)^2/2.

Their expected NUMBER in a fixed box still diverges as e tends to0, so they cannot be discarded by saying their probability is O(a²). If each such particle receives a four-arm pivotal factor of order E N_e/lambda, its normalized total influence would instead be O(a² E N_e)=O(r_e), which vanishes. This is the correct prospective estimate and requires the geometric insertion arm bound. It is not established by the raw Poisson count.

After removing such particles legitimately, a rare lifetime history has at most one presence change. The remaining source comparison must identify a birth or death across a four-interface screen with a critical connection-bit refresh, INCLUDING its conditional distribution and joint effect on all tested quads. Scalar flip calibration fixes the time factor but not these signed multi-test kernels; the intermediate-state defect in geometric-dynamics-interface.md records that distinction.

## Conditional geometry and two replicas

For quenched convergence, two birth–death processes share only the initial uncolored Poisson geometry. Initial colors and all subsequent deaths/births are independent conditional on that geometry. Thus their persistent initial particles are overlapping thinnings of one original process, while their new births are independent. Treating the two bases as independent Poisson tessellations would erase the very conditional covariance that must be controlled. The source's second-replica protection under annular swaps is relevant, but its exact constant-geometry history formulation does not already identify this overlapping-thinning construction. A full proof must retain these shared locations and show concentration of path laws, not merely compare annealed one-replica series.

No path tightness, geometric mixed-difference bound, or two-replica comparison is claimed proved in this note. The exact Poisson lifetime representation and its normalization expose concrete estimates that would close the new operation rather than replacing it by frozen-color dynamics.

## A proved finite-time-list removal estimate

The short-lived-particle issue CAN be resolved for each fixed finite list of observation times, although not yet uniformly over paths. At physical time s in [0,aT], particles born after0, still alive at s, and dead by aT form a marked Poisson process independent of the remaining snapshot, of intensity

 rho_s=lambda(1-exp(-s))(1-exp(-(aT-s)))<=lambda(aT)^2/4.

The remaining snapshot is fair critical Poisson of intensity lambda-rho_s. Couple these two critical snapshots by adding the removed points one at a time in the Poisson intensity parameter. The expected number of changes of a fixed crossing Q along this coupling is exactly

 integral_(lambda-rho_s)^lambda [E N_u(Q)/(2u)] du.       (2)

This is the local identity and Mecke from the interface note, applied at each intermediate intensity u, with color-pivotal expectation N_u. A difference of the endpoint indicators is bounded by the number of changes, regardless of their signs. The source square amplitude and its common first-coefficient calibration for each fixed polygon Q give E N_u(Q)<=C_Q E N_lambda(Q_*) uniformly when u/lambda->1. To see the uniformity without a convergence rate, u tending to infinity and u/lambda tending to1 imply the same asymptotic statements along every such sequence; the unit-square power amplitude controls its ratio. Thus (2) is at most

 C_Q (rho_s/lambda) E N_lambda(Q_*)
       <=C_(Q,T) a²/r_e = C_(Q,T) r_e.                 (3)

A union bound proves that deleting all particles born and dead inside the observation interval changes any specified finite list of crossing observations with probability O(r_e), tending to0. In particular the short-lived particles may be omitted in the finite-dimensional comparison. This estimate uses source pivotal calibration, not an unproved geometric many-insertion bound.

It does not establish pathwise equality with high probability: many distinct observation times can expose different temporary effects, and the finite-list union constant grows with list length. Passing from (3) to a uniform path estimate requires additional time control. The frozen full J1 target therefore remains open.
