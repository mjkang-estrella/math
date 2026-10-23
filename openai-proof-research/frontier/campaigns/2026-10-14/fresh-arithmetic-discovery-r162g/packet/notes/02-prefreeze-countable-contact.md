# Prefreeze calculation: removable dust and countable-contact curve perturbations

This is a feasibility record, not a frozen theorem or an author-proof nominee. All canonical source operations are accepted as true. No old statement is weakened or regraded. The developed operation is distinct from the prior complete Beltrami deformation comparison.

## 1. Exact full target tested

Let B be any compact totally disconnected conformally removable subset of the plane. Let F_sigma(B) consist of rectifiable curves whose *image* meets B at at most countably many points; visits with parameter multiplicity are not the definition here. For every open Omega and every pair of disjoint nonempty continua E,F compactly contained in Omega, the proposed operation would prove

    Mod_2 Gamma(E,F;Omega)
      = Mod_2 [Gamma(E,F;Omega) intersect F_sigma(B)].                 (T)

No separation, dimension, finite-connectivity, local-connectivity, or cofatness hypothesis on B is added. Continua may meet B. A nondegenerate continuum cannot be contained in B, but its intersection with B may be uncountable and may carry positive one-dimensional measure.

The strong constructive form would say: for each nonnegative Borel rho in L2_loc(R²), there is an exceptional curve family Gamma_0(rho) of 2-modulus zero such that every rectifiable gamma outside it with distinct endpoints, every neighborhood U of its image, and every epsilon>0 admit a simple curve gamma_tilde with

    endpoints(gamma_tilde) = endpoints(gamma),
    image(gamma_tilde) subset U,
    image(gamma_tilde) intersect B countable,
    length(gamma_tilde) <= length(gamma)+epsilon,
    integral_gamma_tilde rho ds <= integral_gamma rho ds+epsilon.     (P)

The primary main criterion, read in its actual proof, pays equivalence of these formulations for closed B, including a stronger finite-connector statement away from B at the endpoints. Thus proving that equivalence again would not be a contribution. The unpaid input is deriving one of them from the source's scalar removability theorem, without adding CNED as a hypothesis.

The choice of this full operation is prospective feasibility, not a freeze of a supposedly viable statement. No closed full proof emerged below, so no frozen-theorem file was created.

## 2. Strongest primary reduction: a positive bound is enough

One need not obtain the sharp constant one directly. The primary criterion reduces (T) to the following uniform local assertion. There are t,phi>0 such that for every x there exists r_x>0 with

    Mod_2[Gamma(E,F;R²) intersect F_sigma(B)] >= phi                    (L)

for all disjoint nondegenerate continua E,F in B(x,r_x) with

    dist(E,F)/min(diam E,diam F) <= t.

The constants t and phi must be common to all these condensers; r_x may depend on x. All endpoint and contact conditions remain present. A weak modulus comparison with any finite common factor would suffice. Consequently the source barrier's factor 8, or a derived energy factor 32, is not by itself an obstruction.

Here is the exact quantitative use of (L). A family of curves meeting D=B(x,r), having length>M r, has modulus at most

    pi/M + 2 pi/log(sqrt(M))

up to harmless fixed rescaling of the disk in the first term. For the contained subfamily use density 1/(M r) in B(x,sqrt(M)r); for the escaping subfamily use the radial annulus density. The bound tends to zero. Choose M so that it is less than phi/3. On the remaining curves, all images lie in a fixed dilation lambda D. If every such connector had rho-length greater than A||rho||_(L2(lambda D)), then the normalized density rho/(A||rho||_2) would bound that bad family's modulus by A^(-2). Choose A with A^(-2)<phi/3. Removing a prescribed modulus-zero family costs nothing. A connector remains, with

    length <= M r,
    rho-length <= A||rho||_(L2(lambda D)).                             (2.1)

For n=2 the latter equals a constant times r sqrt(average_(lambda D) rho²). The primary constructs covers of B for which, outside one modulus-zero family,

    sum_(D_i met by gamma) r_i -> 0,
    sum_(D_i met by gamma) r_i sqrt(average_(lambda D_i) rho²) -> 0.    (2.2)

It uses disjoint small subballs, bounded-overlap dilations, an L2 synthesis estimate and Fuglede summability. It then performs *finitely many* replacements for a curve whose endpoints avoid B. Every new connector already belongs to F_sigma(B), so the final contact set is contained in a finite union of countable sets. When endpoints meet B, the separate endpoint concatenation has only countably many junctions accumulating at the two endpoints. These are actual operations in the primary proof, not additional author steps.

If one only obtains a positive number phi_i for each local pair, (2.1) has constants depending on phi_i, including A_i at least of order phi_i^(-1/2). Neither compactness alone nor the unweighted limits (2.2) control the weighted sums with A_i. For example, abstract errors a_m=2^(-m) and constants A_m=2^(2m) have a_m->0 but A_m a_m->infinity. This is a diagnosis of missing uniformity, not a construction of a removable domain violating (L).

## 3. What probability-law duality would actually need

A useful sufficient construction for (L) would be a probability P supported on the specified countable-contact connectors with mean full arclength occupation g dA and ||g||_2<=C, uniformly over the local condensers. If rho is admissible for those connectors, Tonelli and Cauchy--Schwarz give

    1 <= E_P integral_gamma rho ds
      = integral rho g dA <= C||rho||_2,

hence their modulus is at least C^(-2). It is enough to prove this law for an appropriate subfamily; a sharp minimizing law is unnecessary.

The canonical positive-law theorem gives an L2 *domain-part* occupation density, square-summable hit probabilities on all dust points, and mean visit control on specified countable sets. Its tagged paths can run through generic previous level sets and can have uncountably many residual dust contacts. Its endpoint problem is an interior anchor to one specified quotient end. These distinctions prevent simply inserting its law into the preceding calculation for (L).

A tempting inference is that counting-l2 hit probabilities force almost every sample to have only countably many dust contacts. They do not. The following exact model keeps the mean occupation and the contact-cardinality issue visible.

Choose a nonempty perfect null Cantor set C subset [0,1], and a compact nowhere-dense Cantor set D subset [0,1] of positive length d. Set

    B_0=C times D.

This is compact, totally disconnected and planar-area zero. No conformal removability of B_0 is asserted. For y uniformly distributed with respect to normalized Lebesgue measure on D, take the horizontal segment

    gamma_y(t)=(-1+3t,y),  0<=t<=1.

Its mean arclength occupation density is

    g(x,y)=d^(-1) 1_[-1,2](x) 1_D(y),
    ||g||_2²=3/d.                                                    (3.1)

For every fixed point z, P(z lies on gamma_y)=0. Thus the entire pointwise hit function on B_0 is zero, and its counting-l2 norm is zero. For every finite Borel measure lambda on B_0, even one chosen arbitrarily after the law, Tonelli gives

    E lambda(image gamma_y intersect B_0)
      = integral_(B_0) P(z lies on gamma_y) dlambda(z)=0.              (3.2)

Nevertheless image(gamma_y) intersect B_0=C times {y}, an uncountable set, for every sample. Independent samples are on distinct horizontal lines almost surely, so their dust intersections with each other are empty. Thus even pairwise absence of diffuse intersections between independent samples does not imply countable contacts of an individual sample.

This is not a negligible exceptional-family phenomenon. The family H={gamma_y:y in D} has exact modulus d/3. If rho is admissible, then

    1 <= (integral_[-1,2] rho(x,y) dx)²
      <= 3 integral_[-1,2] rho(x,y)² dx

for every y in D with finite line integral, and integration yields ||rho||_2²>=d/3. Density (1/3)1_([-1,2] times D) attains that value. Therefore uncountably many dust contacts can occupy a positive-modulus family while all point-hit probabilities vanish and (3.1)--(3.2) hold.

This example refutes the proposed probability inference, not the full target (T) for removable dust. Nor does it impersonate all the source's endpoint/tag hypotheses. To repair the route one must actually construct a law supported on countable-contact paths, using removability in an additional way. Countable flag support, more atomless test measures, and independent-sample intersection control do not alone provide that support condition.

## 4. Scalar extension does pay a strong analytic statement

Let B satisfy the target hypotheses. For any globally continuous u with finite Dirichlet energy on G=S²\B, the complete companion proof gives u in W1,2(S²). Since B has area zero, its global weak gradient agrees almost everywhere with its off-B gradient and

    integral_(S²) |grad u|² = integral_G |grad u|².                    (4.1)

Thus there is no energy inflation in this scalar conclusion. For each such u, the usual Sobolev/Fuglede statement gives an upper-gradient inequality outside a modulus-zero family depending on u. Countably many fixed u's may share the union of their exceptional families.

Neither fact constructs a new curve with countable contacts. It gives inequalities along existing typical curves. The desired Gamma_0 may depend on rho, so density-dependent choices are allowed; the difficulty is constructing the appropriate *continuous* scalar object from that rho, retaining the required condenser values and the correct path class.

For a nonnegative rho, an attempted potential is

    d_rho(E,z)=inf integral_eta rho ds,

where eta joins E to z and belongs to F_sigma(B), and u=min(1,d_rho). In G, ordinary small line segments are permitted, hence actual pointwise values obey

    |u(x)-u(y)| <= integral_[x,y] rho ds                              (4.2)

whenever the segment is in G. This gives local ACL and |grad u|<=sqrt(2)rho using two coordinate directions, provided measurable representatives are handled. The constant sqrt(2) is harmless for weak comparison. What (4.2) does not prove is continuity across B.

Here is an explicit calculation showing that the missing continuity cannot be supplied merely by an L2 bound, even for a removable singleton.

Work inside D_3, let B={0}, let E be the closed disk of radius 1/8 centered at (-1,0), and set

    x_j=(2^(-j),0),  R_j=2^(-j-3),
    L_j=2^(j+4),    r_j=R_j exp(-L_j),     j>=1.

The closed disks of radii R_j about x_j are pairwise disjoint and lie strictly in the right half-plane. Put

    rho_j(z)=1/(L_j |z-x_j|) on r_j<|z-x_j|<R_j,
             0 elsewhere,
    rho(z)=delta+sum_j rho_j(z),       delta=1/10 on D_3.             (4.3)

For each annulus,

    integral rho_j² dA = 2pi/L_j,
    integral_(r_j)^(R_j) [1/(L_j s)] ds = 1.                          (4.4)

Disjointness and sum 1/L_j<infinity imply rho in L2(D_3). Every rectifiable curve from E to x_j must cross the jth annulus, and the radial variation inequality gives rho-length at least one. Such curves may touch 0; that does not reduce the annular cost. Thus u(x_j)=1 for the clipped distance with curves restricted to D_3.

Let q_j=(0,2^(-j)). The segment from (-1,0) to q_j lies in the closed left half-plane and meets none of the annuli. It avoids 0. Consequently

    u(q_j) <= delta sqrt(1+2^(-2j)) <= delta sqrt(2)<1/5.              (4.5)

Both x_j and q_j tend to the one removable point 0. The potential has no continuous extension there. This is a failure of this potential construction, not a failure of continuous Sobolev removability or of CNED for a point.

The same annulus calculation shows why small L2 changes to a density do not uniformly control all path integrals: the L2 energy 2pi/L can be arbitrarily small while every crossing still costs one. Density approximation must use a modulus-exceptional argument or a suitable pointwise majorant, with all endpoint requirements retained. Simply mollifying rho in L2 is insufficient.

## 5. Trying the stronger source repair: shrinking jumps

Stopping at the raw-distance discontinuity would be premature. The canonical barrier proof already constructs chain distances with progressively smaller jumps and then smooths with shrinking sampling neighborhoods. Its explicit purpose is to produce controlled topological bands even when ordinary weighted distances have no trace. The following tests that stronger repair, keeping its domain of validity separate from (T).

First consider *buffered anchors* E_1,E_2 compactly contained in G, and smaller compact sets E'_i in their interiors. Suppose a density g>=c>0 is admissible for countable-contact paths from E_1 to E_2. A version of the source jump-removal argument is feasible here:

1. For each finite collection of old jump levels all jump tolls have a positive minimum. A chain with bounded cost therefore has boundedly many jumps. When one new level has mesh tending to zero, its new jump endpoints have subsequential common limits in B.
2. Between distinct limiting dust junctions, the source collar-splicing argument uses actual original pieces and smooth joining arcs in G. If the original paths have countable dust image, each replacement still does: countably many original pieces, arcs in G, and countably many endpoint/junction images suffice. It is essential that the extra times accumulate only at the specified endpoints, as the source itself stresses.
3. The exterior anchors avoid B, so a limiting dust junction cannot belong to an anchor. The one-ended collar construction retains an actual prefix starting in that anchor. Old jump disks are open and have boundary in G, so a limiting dust junction in their closure lies in their interior and permits truncation there; junctions outside their closure are handled by the one-ended collar construction.
4. A newly added jump level with fixed positive toll rho_j cannot lower the old positive chain bound by a fixed amount at arbitrarily small mesh: the preceding replacements would give an old chain below its bound. This is the source's finite-level contradiction with zero boundary weights m and the restricted contact property preserved.
5. Choose summable permitted bound losses and rho_j down to zero. The truncated chain distance then has oscillation at most a constant times rho_j within each disk of level j. Consequently its domain trace at *every* b in B is unique, with no almost-everywhere qualification. The trace is continuous as a function on B and under approach from G: any sufficiently small neighborhood sits inside a level-j disk, whose full value oscillation is small.

The measurability step also needs attention. One cannot literally reuse the source's standard-Borel coding proof after silently adding the predicate “the compact dust contact set is countable.” There is, however, a scalar workaround for the buffered-potential calculation. The axis-segment inequality holds for actual bounded potential values. On a compact rectangle in G, almost every vertical and horizontal line has finite g-integral, so the restriction is absolutely continuous on each such whole line. Choose countably many good vertical lines dense in the horizontal coordinate. Nearest-line evaluations are measurable functions of the two variables and converge to the original potential on every good horizontal line. This proves Lebesgue measurability up to a planar-null set; a Borel representative follows. Fubini then supplies the distributional derivatives. This avoids asserting a Borel path-family coding that has not been established.

Positive local convolution and a locally finite partition of unity smooth the potential in G with arbitrarily small L2 gradient error. Sampling neighborhoods shrink toward B, so pointwise band bounds are preserved. On E'_1 and E'_2 the sampling can stay inside the corresponding constant regions. The result is globally continuous, smooth off B, zero and one on those smaller anchors, and has a gradient bound of the form

    ||grad u||_(2,G) <= 4sqrt(2)||g||_2+epsilon.                       (5.1)

The companion's scalar theorem then gives global Sobolev membership with exactly the same gradient energy. For an arbitrary admissible L2 density g, replace it by g+c on the sphere and then let c decrease to zero; this preserves admissibility and changes its L2 norm by at most c times the square root of spherical area. Thus the positive lower bound is not an essential issue for this buffered calculation. A global Sobolev upper gradient proves

    Mod_2 Gamma(E'_1,E'_2;S²)
       <= (4sqrt(2)||g||_2+epsilon)².                                (5.2)

This is the strongest integrated scalar calculation reached here. It is recorded to show that the source's actual repair has been tried; it is not offered as a restricted substitute theorem or as a nominee. The distinct full target is still (T), with arbitrary continua, arbitrary rho, and the actual countable-contact curve construction.

For (4.3), the jump repair can indeed erase the oscillating wells near 0 at small energy cost. It cannot converge uniformly to the original potential: every sufficiently small neighborhood of 0 contains a center with value one and a q_j with value below 1/5, so any continuous replacement has uniform discrepancy at least 2/5 on one of those subsequences in the limit. This is compatible with a vanishing tail Dirichlet error because sum_{j>=N}2pi/L_j tends to zero. Thus the raw counterexample does not disprove the repair; it identifies exactly which topology of approximation is unavailable.

## 6. Where this repair still does not pay the full criterion

The anchors in (5.2) have a buffer inside G. The local criterion (L) quantifies over *every* nearby continuum, including those meeting B, and requires one uniform modulus bound in their relative-distance scale. Choosing arbitrarily tiny subcontinua of E\B and F\B is not enough. Their diameters may be arbitrarily small relative to dist(E,F), so the ordinary Loewner lower bound for those smaller condensers can tend to zero. No common phi follows from (5.2) by that selection.

There are two concrete ways one might try to remove this limitation, and neither was completed.

(A) Allow jump endpoints on the anchors' dust points. This would force the desired potential trace to be zero/one there. The source jump-removal proof no longer applies without an extra step: a new jump can converge to b in E intersect B, and the one-ended construction assumes its dust target is outside the anchor closure. To remove the jump while retaining an actual endpoint in E, one needs a cheap admissible connector from E to the retained collar. Small ordinary circles may meet B uncountably; they are not automatically permitted connectors. Merely declaring the endpoint b accessible is also wrong for arbitrary L2 densities. For example

    rho(z)=1/(|z-b| log(1/|z-b|)),  0<|z-b|<e^(-1)

has finite local L2 energy, but every ordinary rectifiable path reaching b with full radial variation pays infinite rho-length. The exceptional-modulus treatment of such points must be integrated into the continuum/endpoint construction, rather than excluded from the theorem. This example concerns accessibility under a density, not topological accessibility or a counterexample to (T).

(B) First construct positive-modulus connectors for exterior approximating continua and then pass to a limit. Compactness preserves endpoints, length bounds in favorable parametrizations, and sometimes lower semicontinuity of a suitable weighted length. It does not preserve countable dust contact. An explicit fixed-endpoint example is B=C times {0}, with C a compact Cantor subset of (-1,1). Let gamma_n go from (-2,0) vertically to (-2,1/n), horizontally to (2,1/n), then vertically to (2,0). It misses B and has length 4+2/n. Under the natural three-piece reparametrization these paths converge uniformly to the horizontal segment, whose contact set is C times {0}, uncountable. The limiting target statement requires existence of some countable-contact replacement; this sequence shows only that it cannot be justified by closedness of the path property. Even here B is a subset of a line, so this is not a negative example to the target.

The primary finite-surgery proof avoids precisely this limit problem: it retains finitely many connectors already satisfying the contact restriction. To invoke it for removable dust, the uniformly positive local modulus input (L), or an equivalent direct finite-connector construction, remains to be supplied. The criterion itself and its endpoint iteration are already paid.

## 7. Compatibility with the full circle-domain proof

There is a related temptation to take the source mask argument and replace its coordinate of f by an arbitrary density potential. The actual mask proof starts with a bounded scalar that is continuous at every common point component; its possible discontinuities are indexed by countably many disk-containing pairs. It then masks those intervals and applies scalar extension on residual compact dust. In the arbitrary rho problem, (4.3) shows that a potential can already be discontinuous at a point component, with no target disk interval available to absorb the discontinuity. Additional scalar traces would need to be constructed first.

Likewise the source's null projected trace conclusion is an assertion for almost every axial line and particular conformal-map coordinates. It is sufficient for its exact flux calculation. It is not the geometric assertion that those lines meet the dust only countably often, and it does not quantify over all L2 densities. The primary transboundary proof uses a CNED perturbation with rho=|Df| plus a packing density specifically to ensure that *new* connectors pay any newly met disk tails. This compatibility step is already supplied when CNED is known, but cannot be inverted to establish CNED from the final rigidity conclusion.

A conditional quantitative flux computation would read

    E_derivative + pi sum radius_errors² <= flux_defect + area_defects,

with all terms normalized consistently. It follows directly by the source's subtraction. It does not estimate the right side from the hypotheses of (T), and was not promoted into another target. No stability claim with a uniform constant over arbitrary circle domains is asserted.

## 8. Prefreeze outcome

The full countable-contact modulus operation has not closed. The strongest integrated progress is the exact scalar-energy input, the quantitative law-to-modulus calculation, and the buffered shrinking-jump potential calculation (5.1)--(5.2), followed by the primary's precise reduction to a uniform local connector bound. The calculations explicitly defeat several insufficient shortcuts and show why neither arbitrary point-hit control nor raw weighted-distance regularity supplies the missing step.

The unresolved operation is: construct countable-contact connectors with a uniform positive local modulus for every pair of nearby continua, including their intersections with B, while retaining arbitrary L2 weighted costs; equivalently close the full finite-surgery input required by the primary criterion from conformal removability alone. No counterexample to that statement is proved here. No worldwide impossibility, exhaustive search, or new-to-literature theorem is claimed. No theorem was frozen, no independent grade is assigned, and no weaker substitute is submitted. Parent alone integrates or requests reviews of any future full author proof.
