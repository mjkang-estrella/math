# I14 — The sharp spectral coefficient for graph width in dimension three

Date: 2026-10-08. **Completed parent candidate, not accepted.** All applicable results in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The candidate requires independent proof and final significance reviews. It is not a new finding until those gates pass. No worldwide-priority claim is made.

## 1. Exact proposed theorem

Use the sign convention Delta = div grad. For a complete connected smooth boundaryless Riemannian three-manifold, write

    -a Delta_g + Scal_g >= lambda

when its quadratic form on every real compactly supported smooth function is at least lambda times the squared L2 norm. Fix **4 <= a < 6**, lambda > 0, and put

\[
 s_a=\sqrt{\frac{8-a}{2(6-a)}}.
\]

**Theorem W.** Under this spectral inequality there is a continuous map from M to a locally finite simplicial graph, with its usual polyhedral topology, for which every entire fiber has g-diameter at most

\[
 500 s_a/\sqrt\lambda. \tag{W}
\]

No orientability, spin, compactness, bounded geometry, bound on the auxiliary weight, or bound on its derivatives is imposed. For 0 <= a <= 4, the coefficient-4 source theorem directly gives the bound 500/sqrt(lambda). Thus the positive-coefficient range for a universal graph-width implication is precisely **0 < a < 6**.

The endpoint is excluded: the same explicit smooth complete metric on R3 satisfies `-6 Delta + Scal >= 4` and has infinite Urysohn 1-width. Monotonicity of quadratic forms gives the same failure for all a >= 6. The numerical constant 500 is not optimized; sharpness refers to the range of a, not the width constant.

## 2. Pinned input and new obligations

Let **S** denote [Spectral scalar curvature and Urysohn width in dimension three](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Spectral-scalar-curvature-and-Urysohn-width-in-dimension-three-October-5-2026/build). Its actual `thm:main` assumes coefficient **4** and proves the width bound 500/sqrt(lambda). Its proof uses

    D(h,T) = Scal_h + 2 Delta_h T - |dT|_h^2.

The parent read all six section files, not just the theorem. The complete pinned inventory was parsed and all 15 TeX files of the two spectral-width manuscripts were retrieved and checked by Git blob identity. [Source manifest](../sources/i14_spectral_width/source-manifest.json).

The following S interfaces are used, with their hypotheses checked below:

- `lem:positive-weight`: positive ground-state exhaustion from the quadratic form. Its elementary argument also works for any fixed a>0.
- `eq:weighted-mean-curvature`, `eq:weighted-jacobi`, `eq:stability-form`, `eq:log-jacobi`, and the Gauss identities in `02-weighted-surfaces.tex`: geometric identities and local stability for an arbitrary smooth weight T and pressure mu. These identities do not assume coefficient 4.
- `03-cutting.tex`: the maximal nonseparating stable-surface family and localized integral-current construction. Its curvature-dependent inputs are the closed-surface diameter/topology estimate and the local exit estimate. We supply their replacements explicitly.
- `04-doubling-bubbles.tex`: reflection-compatible smoothing and compact weighted perimeter-minus-volume minimization. The smoothing needs a new quadratic-form check for the modified curvature quantity; the pressure scale also changes. Neither is imported with widened hypotheses.
- `05-slabs.tex` and `06-graph-gluing.tex`: the separating-interface tree, multiplicity-two slab cover, locally finite partition, and whole-fiber anchor argument. These are metric/topological constructions. We give every changed constant and preserve local finiteness, compact supports and paired collars.

S's higher-dimensional companion still assumes coefficient 4. The complete inventory's two spectral-width titles do not state Theorem W. The proof here is a modification of lower-level S arguments, not an application of S's global theorem to a stronger hypothesis. In particular a>4 makes the spectral assumption weaker, so operator monotonicity gives no reduction to coefficient 4.

## 3. Positive density and the generalized curvature quantity

Scale g by lambda, so the spectral lower bound is one. Put

\[
 \beta=4/a\in(2/3,1],\qquad
 \gamma=2-1/\beta=2-a/4\in(1/2,1],\qquad
 c_\beta=\frac{3\beta-2}{2\beta-1}
 =\frac{2(6-a)}{8-a},\qquad s=c_\beta^{-1/2}=s_a.
 \tag{3.1}
\]

For any dimension define `D_beta(h,T)=Scal_h+2 Delta_h T-beta |dT|_h^2`. The ground-state argument supplies positive smooth u with

\[
 (-a\Delta_g+\mathrm{Scal}_g)u\ge u.
\]

On a compact manifold use the positive first eigenfunction. Otherwise exhaust by connected relatively compact smooth domains, normalize first Dirichlet eigenfunctions at one base point, and pass to a smooth local limit by Harnack and interior estimates. Their decreasing eigenvalues are at least one and bounded above by a fixed compactly supported Rayleigh quotient. All coefficients are smooth and locally bounded; no global Harnack constant is required. Set

\[
 T=-(a/2)\log u.
\]

Direct differentiation, using beta=4/a, gives

\[
 D_\beta(g,T)=\mathrm{Scal}_g-a\Delta_g u/u\ge1. \tag{3.2}
\]

The weighted area density is e^{-T}; it is positive and smooth and is used only on compact minimization regions. No completeness of the conformal area metric is claimed.

## 4. Exact stable-surface transfer retaining the quadratic terms

Let Sigma be a smooth two-sided stable weighted surface in a smooth three-manifold (X,h), with induced metric k and equation

    H - nu T = mu.

The unconstrained weighted Jacobi operator is the one in S:

\[
 \Delta_{\Sigma,T}=\Delta_k-\langle d_\Sigma T,d\cdot\rangle,
 \qquad Q=\mathrm{Ric}_h(\nu,\nu)+\mathrm{Hess}_hT(\nu,\nu)+|B|^2+\nu\mu.
\]

On a closed connected Sigma, or any relatively compact connected smooth interior domain, take a positive first eigenfunction w of `-Delta_(Sigma,T)-Q`, with Dirichlet boundary condition in the domain case. Stability gives

\[
 -\Delta_{\Sigma,T}p\ge Q+|dp|^2,\qquad p=\log w.
\]

Put U=T|_Sigma-p and B0=B-(H/2)k. The Gauss and Laplacian decompositions give

\[
\begin{aligned}
 D_\gamma(k,U)\ge D_\beta(h,T)
 &+(\beta-\gamma)|d_\Sigma T|^2
   +2(\gamma-1)\langle d_\Sigma T,dp\rangle+(2-\gamma)|dp|^2\\
 &+\mu^2+(\beta-1)(\nu T)^2+|B|^2+2\nu\mu.
\end{aligned} \tag{4.1}
\]

For clarity, the first line uses tangential covectors; the normal component is in the second. This follows by first writing

    D_gamma(k,T) = D_gamma(h,T) - 2(Ric_nunu+Hess T_nunu)
                    + (H-nu T)^2 + (gamma-1)(nu T)^2 - |B|^2,

then replacing T by T-p, applying the Jacobi inequality, and using `D_gamma(h,T)=D_beta(h,T)+(beta-gamma)|dT|^2`. The normal Ricci and Hessian cancel. There is no discarded indefinite cross term.

With gamma=2-1/beta, the tangential quadratic form is exactly

\[
 \frac1\beta|dp+(\beta-1)d_\Sigma T|^2.
\]

Since H=mu+nu T and `|B|^2=|B0|^2+H^2/2`, the remaining quadratic expression is exactly

\[
 |B_0|^2+(\beta-\tfrac12)
       \left(\nu T+\frac{\mu}{2\beta-1}\right)^2+c_\beta\mu^2.
\]

Consequently

\[
 \boxed{D_\gamma(k,U)\ge D_\beta(h,T)+c_\beta\mu^2+2\nu\mu.} \tag{4.2}
\]

All omitted terms are squares with nonnegative coefficients. The identities remain valid for nonorientable ambient manifolds: calculations use local normals and densities, and two-sidedness gives the required normal along the surface. No ambient orientation was used.

## 5. Intrinsic length, local exit and topology

Suppose a smooth surface (S,k) with a smooth U satisfies

\[
 2K_k+2\Delta_k U-\gamma|dU|^2\ge c>0,
 \qquad \gamma>1/2.
\]

Let a finite segment be an index-stable geodesic for `exp(-2U)k`, parametrized by k-arclength t in [0,L]. The conformal curvature and index form give

\[
 0\le\int_0^L e^U\{(\phi')^2-\tfrac12(c+\gamma|dU|^2)\phi^2\}\,dt.
\]

Set phi=exp(-U/2)psi. The part containing U' is

    (psi')^2 - U' psi psi' - (2 gamma-1)(U')^2 psi^2/4.

Completing the square bounds this above by
`[2 gamma/(2 gamma-1)](psi')^2`; the remaining normal-to-the-curve part of |dU|^2 is nonpositive. A sine test in H0^1 gives

\[
 L\le2\pi\sqrt{\frac{\gamma}{(2\gamma-1)c}}
       =\frac{2\pi s}{\sqrt c}. \tag{5.1}
\]

The last equality follows from (3.1). On a closed surface the conformal metric is complete, so a minimizing conformal geodesic between any two points proves the same bound for intrinsic k-diameter. Integrating the curvature inequality gives

\[
 4\pi\chi(S)\ge c\,\mathrm{Area}_k(S)+\gamma\int_S|dU|^2>0,
\]

so a connected closed surface is a sphere or real projective plane. The density version of Gauss–Bonnet, or its orientation double cover, gives the statement in the nonorientable case.

The **local exit estimate** requires no completeness of an open stable sheet. Choose nested relatively compact smooth domains Omega0 compactly contained in Omega1, apply the positive Jacobi eigenfunction on Omega1, and minimize conformal distance from a point of Omega0 to its nonempty boundary within the compact closure of Omega0. The segment stays within a region where U is smooth and satisfies (5.1). It supplies a k-path to that boundary of length at most 2 pi s/sqrt(c).

By (4.2), all these conclusions apply to a stable weighted mu-surface whenever

\[
 D_\beta(h,T)+c_\beta\mu^2-2|d\mu|_h\ge c>0. \tag{5.2}
\]

For the original data and mu=0 the diameter and exit constant is 2 pi s. This is the exact input replacing S's 2 pi estimate.

## 6. Cutting and smoothing: the additional seam check

The proof of S `prop:separating-cut` now applies with every occurrence of its curvature-dependent length 2 pi replaced by 2 pi s and its detection neighborhood radius 10 replaced by 10s. Here is the dependency verification.

Choose a maximal family of disjoint closed two-sided stable weighted minimal surfaces such that no finite subfamily disconnects M. The diameter bound confines all members meeting a compact set to its compact 2 pi s-neighborhood. Finite subfamilies have independent mod-two homology classes detected by crossing loops. A compact smooth neighborhood has finite-dimensional second homology, so only finitely many members meet the compact set. Cutting is therefore locally finite, its gluing map proper, and each piece is proper in its intrinsic metric.

If an interior closed hypersurface fails to separate, use S's orientation double cover, antisymmetric integral currents and compactly supported Thom form detecting a crossing loop. Minimize in a compact region containing the full 10s-neighborhood of that form. The area metric exp(-T)g is smooth on the compact region. At a cut boundary the same local foliation by minimal disks gives an area-nonincreasing retraction, so full-neighborhood interior regularity applies. The minimizing sheets that meet the form are two-sided and stable. The exit estimate 2 pi s < 10s forces those sheets to be closed. Some detected component is nonseparating, contradicting maximality. This uses precisely S's compact support, coorientation and boundary comparison arguments, which are independent of beta. Finally each boundary component is a sphere or projective plane; its finite fundamental group allows the same circle-valued-map argument to turn a nonseparating neat hypersurface into a nonseparating closed one. Thus every compact connected two-sided neat hypersurface separates each cut piece P.

The double smoothing is not quoted without change. On a normal collar write

    g = dr^2 + k(r),   A=k'/2,   H=tr_k A,
    m(r)=log(dvol_k(r)/dvol_k(0))-T(r).

Weighted minimality gives m'(0)=0. The exact curvature identity is

\[
 D_\beta(g,T)=D_\beta(k,T)-|A|^2-(m')^2-2m''
                       +(1-\beta)(H-m')^2. \tag{6.1}
\]

Reflect k and m evenly and smooth them with the source's even mollifier and cutoff; recover T from k and m. As in S, all tangential derivatives needed and m'' converge uniformly; m' tends to zero at a sequence approaching the seam. The only noncontinuous first-normal-derivative contribution there is

\[
 Q_\beta(A)=-|A|^2+(1-\beta)(\mathrm{tr}A)^2
            =-|A_0|^2-(\beta-1/2)(\mathrm{tr}A)^2. \tag{6.2}
\]

It is concave for beta>=1/2. A mollified k'/2 at a seam sequence averages tensors tending to A and -A. Jensen for this concave quadratic form yields a lower bound by the one-sided Q_beta(A), with a vanishing error from the converging metrics. The m' cross terms vanish and m'' converges. Thus the lower limit of D_beta at the seam is at least one. Away from it the convergence is smooth. Compactness of each collar's changed region gives

\[
 D_\beta(h,\widetilde T)\ge1/2,\qquad g/4\le h\le4g. \tag{6.3}
\]

Choose the smoothing size separately on disjoint locally finite compact collars, leaving all data unchanged outside them. This gives globally smooth reflection-invariant data. There is no global bound on T or derivative size: all choices are local on compact collars. The condition beta>2/3 needed earlier is stronger than the seam condition beta>=1/2.

## 7. Pressure, slabs and whole fibers with every scale recorded

Use the intrinsic proper length metric d of h on P, base point o, and r=d(o,·), extended evenly to the double. Folding across the seam does not increase length; projection into M has g-length at most twice h-length. Smooth r evenly to rho with

    |rho-r|<s,   |d rho|_h<=2.

The source's locally finite partition smoothing allows any positive value error, so s replaces its error 1. For any level ell>=100s choose regular values

    A in (ell-90s, ell-89s),  B in (ell-20s, ell-19s),

and on their band put

\[
 \mu=s\cot\!\left(\frac{\pi(\rho-A)}{B-A}\right).
\]

Since B-A>69s and c_beta=s^{-2},

\[
 2|d\mu|_h\le\frac{4\pi s}{B-A}(1+\mu^2/s^2)
              \le\tfrac14(1+c_\beta\mu^2). \tag{7.1}
\]

The compact constrained minimization, union with its reflected minimizer, barrier clearance, and full-neighborhood regularity in S `prop:separating-interfaces` depend only on smooth positive weight, compact support, and the signs of the unbounded cotangent pressure at the two ends. They therefore apply verbatim with these A,B,mu. With (6.3) and (7.1), inequality (5.2) holds with c=1/4. Each closed interface has intrinsic h-diameter at most 4 pi s. Folding yields finitely many disjoint compact neat interfaces F_i in P, with

    ell-91s < r < ell-18s,   diam_d F_i <= 4 pi s.

They separate P by Section 6 and separate o from every point with r>ell. Reflection fixes the outward normal at a seam point, so the interfaces meet the seam transversely; this step is unchanged by beta.

Consider a connected distance slab ell<r<u with u<=ell+2s. When ell<100s, its diameter is at most 204s. Otherwise the finite complementary-region graph of the F_i is a tree, because each F_i individually separates. Some one F_i separates o from the entire connected slab. A minimizing d-geodesic from o to x in the slab meets it at a point z_x with d(x,z_x)<93s. Consequently

    diam_d(slab component) < 186s + 4 pi s < 220s.

The slab-component cover from intervals `(js-3s/4,js+3s/4)`, j>=0, has multiplicity at most two, compact closures, and projected g-diameters at most 440s. The source's compactly supported locally finite refinement can be grouped by these sets: each grouped support remains compact and only finitely many summands are assigned to a set, because its closure is compact. The graph of overlapping positive partition coordinates is locally finite. The partition map has each whole fiber anchored in any one cover set corresponding to a vertex of its containing simplex.

To glue the cut boundary copies, take disjoint locally finite paired collars of normal g-length <=s. Their projected union has diameter at most

    L_s=2 pi s+2s.

Each boundary component has finite fundamental group, so its map into its finite image subgraph lifts to a tree and is nullhomotopic there. Retain the source's anchored subgraph: each of its vertices has a positive original partition coordinate somewhere on the collar's inner boundary. Contract on the outer half of each collar and map the inner half to its dedicated added three-edge path, making the two copies agree on the cut itself. Distinct cuts have disjoint path interiors. Local finiteness of collars and compact partition supports imply local finiteness of the enlarged graph.

If a graph point belongs to an old simplex, every collar point added to its fiber lies within L_s of the same anchored cover set, as in S `eq:homotopy-anchor`. Its whole fiber has diameter at most

    440s + 2L_s < 500s.

If the graph point is new, its whole fiber lies in the one paired collar union of diameter at most L_s. The proper quotient gluing map therefore descends the continuous map with the required bound. Rescaling from lambda=1 proves (W). This concludes the proposed positive theorem without passing to a conformally distorted ambient distance.

## 8. Endpoint counterexample and infinite whole-fiber width

On R3 with coordinates (t,x,y), take

\[
 g=dt^2+e^{2t^2}(dx^2+dy^2),\qquad u=e^{-t^2}.
\]

Since g dominates the Euclidean metric and is smooth, it is complete: a g-Cauchy sequence is Euclidean Cauchy and converges, and local smooth metric comparison gives convergence in g. The warped-product formulas, or a direct Christoffel computation, give

\[
 \mathrm{Scal}_g=-8-24t^2,\qquad
 \Delta_g u/u=-2-4t^2,
\]

hence `(-6 Delta+Scal)u=4u`. For every compactly supported smooth phi the exact ground-state transform gives

\[
 \int (6|d\phi|^2+(\mathrm{Scal}_g-4)\phi^2)\,d\mathrm{vol}_g
 =6\int u^2|d(\phi/u)|^2\,d\mathrm{vol}_g\ge0. \tag{8.1}
\]

There is no need for u to be square-integrable. Adding `(a-6) integral |d phi|^2` proves the spectral lower bound four for every a>=6.

Every continuous map R3 to a simplicial graph lifts to its universal covering tree, on the connected target component containing its image. Restrict the lift to a Euclidean sphere of radius R. Its compact image is contained in a finite subtree: use the standard compact-subcomplex property for CW complexes with their usual weak/polyhedral topology, and take the finite subtree spanned by its finitely many cells. Embed that finite tree in R2. The Borsuk–Ulam theorem for S2 supplies antipodal points with the same embedded image, hence the same tree image and the same original graph image. Their Euclidean distance is 2R, and their g-distance is at least 2R. Since R is arbitrary, no such map has bounded whole fibers. In particular UW1(R3,g)=infinity, and the obstruction applies to locally finite target graphs as well.

The same calculation gives a useful boundary check in every dimension n=m+1>=3: for `g=dt^2+exp(2t^2)|dx|^2` and `u=exp(-m t^2/2)`, the coefficient `a=4n/(n-1)` gives `(-a Delta+Scal)u=4u`. Only the dimension-three positive theorem is claimed here; the general-dimensional observation is not another finding.

## 9. Prior art, significance limits, and review priorities

The coefficient-4 source explicitly places itself within Gromov's torus-stabilized graph-width theorem and the Chodosh–Li weighted bubble method. A new assertion cannot be credited merely for mentioning spectral curvature or redoing these constructions.

The primary [Chai–Sun manuscript, arXiv:2604.04052v1](https://arxiv.org/html/2604.04052v1) was consulted at its actual statements and relevant formulas. Its convention is `-gamma Delta + R/2`, so its gamma is a/2 here. Theorem 1.4 treats complete stable weighted surfaces, with gamma<3 in the noncompact case; Theorem 1.12 treats torical band width with boundary weighted-mean-curvature conditions; Theorems 1.20–1.23 give splitting and Geroch-type consequences. The same threshold a=6 is therefore already important in the literature. This report does **not** claim discovery of that spectral threshold, the weighted Jacobi method, or the square-completion principle. A band-width theorem is not on its face a whole-fiber graph-width theorem on every complete three-manifold. The proposed additional work is to carry the enlarged coefficient through the source's nonorientable/local cutting, compatible double smoothing and anchored graph assembly, and establish the endpoint failure for that precise graph-width implication.

The actual Theorems 1.1 and 1.2 of [Hirsch–Kazaras–Khuri–Zhang, *Spectral torical band inequalities and generalizations of the Schoen–Yau black hole existence theorem*, IMRN 2024](https://www.math.stonybrook.edu/~khuri/Blackhole_existence.pdf) were also read. Theorem 1.1 bounds the distance between two classes of ends of an oriented open three-manifold, assuming no spherical second-homology classes, scalar curvature bounded below, and a positive spectral bound for `-Delta+c Scal` with c>1/6. Thus a=1/c gives the same upper threshold six. Theorem 1.2 treats compact spin bands with an additional torical hypothesis in odd dimensions. These are substantial prior results, but neither statement directly gives a graph map for all complete three-manifolds under only the spectral assumption. Both remain mandatory comparators for final significance review. No claim that the endpoint warped example is absent from their work is made. Broader searches did not certify novelty and are not positive novelty evidence. The final reviewer must decide whether the global statement and seam extension merit the requested nonroutine gate or reduce to a standard published theorem.

No MathDB score or featured status is claimed. The named target is the spectral extension of Gromov's codimension-two Urysohn-width problem, with the full coefficient interval and no auxiliary global hypotheses, rather than another solution of the source's coefficient-4 statement.

Independent proof review must check: the full square identity (4.1)–(4.2); intrinsic length when gamma>1/2; local exit on incomplete sheets; the extra positive trace term in (6.1) and seam concavity; all pressure and rescaled slab constants; the exact dependence of the source's topological/minimization steps on curvature; whole-fiber anchoring after gluing; and the CW/graph-lift argument in the endpoint counterexample. Symbolic checks only test algebra; they cannot certify the geometric proof or novelty.
