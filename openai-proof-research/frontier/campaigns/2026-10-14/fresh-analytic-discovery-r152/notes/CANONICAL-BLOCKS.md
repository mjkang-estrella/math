# Stronger integrated initial-block reduction

PREFREEZE. This tests the classical canonical polymer expansion against H's actual layered proof; it is not an author theorem at the full kinetic scope.

## Exact factorial generating functional and integrated block control

Let n=floor(mu), and for bounded u with ||u||infinity<r<1 put m(u)=1+int f0 u and p_u=f0(1+u)/m(u). The exact normalized canonical factorial cumulant densities c_h are characterized by

 log E_can product_{a=1}^n(1+u(z_a))
   = sum_{h>=1} mu^h/h! int c_h(z_1,...,z_h) product u(z_i) dz_i.

The identity is formal through each finite degree even though the log is not polynomial. The canonical polymer identity gives

 log E_can product(1+u) = n log m(u) + R_n(u)-R_n(0).

At u=0 the ideal term contributes exactly

 c_h^ideal = (-1)^(h-1)(h-1)! n mu^-h f0^tensor h.

In particular mu c_2^ideal -> -f0 tensor f0, whereas c_1^ideal -> f0.

The correction R_n is a convergent sum over connected collections of physical exclusion polymers on subsets of [n]. A term with q=sum_V I(V)|V| integration slots is a product of graph integrals with product f0(1+u), divided by m(u)^q. Different occurrences of the same particle label in this logarithmic polymer expansion are independent integration copies; they must NOT be geometrically identified. Overlap of labels enforces polymer incompatibility, not equality of positions across copies.

Differentiate h times at zero. Allocate j derivatives to the numerator (at most q falling-j choices) and h-j to m^-q (rising factorial q^(overline{h-j})); each latter derivative inserts an independent f0 factor. Each derivative kernel is an actual finite signed measure. By taking absolute values term by term BEFORE integrating its h observed slots, its total variation is bounded by C_h(1+q)^h times the positive absolute polymer majorant. Reserving e^(c q) in the classical cluster criterion absorbs this factor for every fixed h. The sum of absolute marked cluster terms is therefore <=C_h n²b <=C_h n epsilon. This argument is stronger than a bound on multilinear products of tests: it bounds variation by the explicit marked-measure representation.

Consequently, for each fixed h,

 ||c_h-c_h^ideal||TV <= C_h n epsilon mu^-h
                     <= C_h epsilon mu^(1-h).                 (IB)

The same integrated argument admits small Gaussian weights in finitely many root velocities: the original factor f0 has Gaussian decay, exclusion uses only positions, and a fixed fraction of the Gaussian is reserved before leaf integration. The permissible weight shrinks if repeated root velocity slots are used. The classical polymer parameter remains O(n epsilon³)=O(epsilon).

This gives the actual first-two initial limits and all fixed-order integrated connected scales. It does not give H's pointwise forest envelope uniformly up to the growing initial root cutoff. A scalar Cauchy bound, or (IB) alone, is insufficient for collision-contact trace integrations. No rootwise density domination is inferred from a total-variation estimate.

## How abstract global links fit the finite-complexity dynamics

At a fixed finite root/complexity threshold, first consider ideal canonical blocks. Represent an h-block coefficient (-1)^(h-1)(h-1)! n mu^-h product f0 by a fixed abstract tree on its h labels with h-1 edges, each of size comparable to mu^-1; allocate its fixed combinatorial coefficient outside. These are algebraic links, not constraints on relative positions. Different blocks use their own disjoint initial labels. The exact one-slab identity and resummation in H04 allow these blocks without modification: their proofs use finite Janossy/factorial identities and factorization over exact initial cumulant blocks, not Poisson independence of the whole initial law.

Erase g abstract global edges before using geometric merger coordinates. Suppose the remaining physical contact/local-link graph has c_geom components, p independent physical initial links, and m birth lines. Its dynamic merger count is m-c_geom-p. Integrating one free translation in EACH geometric component, using an L1 birth factor and suprema for its other births, gives source normalization

 mu^(m-h) epsilon^[2(m-c_geom-p)] epsilon^(3p) mu^-g
     = mu^(c_geom-h-g) epsilon^p.                              (S)

If the combined physical+abstract graph is connected, c_geom<=g+1. Thus (S)<=mu^(1-h)epsilon^p. If the abstract component graph has a cycle, c_geom<=g and there is an additional mu^-1. If the physical graph has a dynamic cycle, H's first-redundant-contact argument applies within the corresponding geometric component. Abstract links do not determine relative translations and must never be inserted into H's geometric merger chart as if they did.

At bounded complexity, g,p,c_geom and the number of crossings are bounded. Consequently the identity n_i-a_i=O_K(1), the original fresh-label factorial denominator, the energy-bin flux estimate, and the final C_K(1+n)^d_K(CT/sqrt(L))^n majorant survive. There are boundedly many extra spatial L1 integrations, no extra factorial assignment of ordinary labels, and no moment-dependent ordinary-atom base. This pays finite-complexity ideal-global-link scaling. It is a transparent composition of H's geometric proof and the classical initial coefficients, not a new proposed substantial operation.

For two top roots, the surviving new initial pair connection propagates through two disjoint linear-response branches, giving the negative product -a_t(phi)a_s(psi), with a_t(phi)=int f0 U(0,t)phi. It supplies no new collision noise. To promote this diagram description to a full limit one must still justify the COMPLETE canonical connected expansion and remove all root/complexity/size tails under the actual inhomogeneous initial blocks; this has not been proved here.

## Coarse domination is the real compatibility interface

H04 and H05 repeatedly use a pointwise bound for initial blocks, of the form

 |c_h(Z_h)| <= (Ch)^(Ch) product f0(z_i)
              sum_{trees T} product_{ij in T}[1_{|x_i-x_j|<=R epsilon}+epsilon^nu],

with the exact coarse kernel R=1, nu=1/81 (or a properly proved substitute), constants uniform over orders through A0(epsilon), and Gaussian/spatial envelopes compatible with the imported DHM estimates. H02's sharp bound for bounded h additionally allows physical links of radius R_{h,D}epsilon plus arbitrarily small tails. A canonical analogue must include genuine algebraic global links of order mu^-1, whose leading coefficients are retained rather than discarded as negligible tails.

Replacing a canonical global factor mu^-1 by the larger coarse epsilon^nu is harmless IF a corresponding pointwise forest expansion has actually been proved. It is not proved by (IB). The PT rooted-polymer machinery is a plausible classical way to pay it; its actual two-point result and proof were read, including the v3 correction for nonlocal finite-volume terms. That finite-box two-point theorem is not by itself an all-order inhomogeneous whole-space estimate. Nor does this limitation establish that supplying it is nonroutine.

A fully compatible rooted canonical expansion would then have to be inserted into H's stopped remainders, high-complexity summation, terminal-witness cutoff estimate, and the credited R025 collective time-shift/microscopic-window proof, all on ONE pasted dynamics chosen before fixed moment order. The finite-complexity calculation (S) removes a misleading geometric objection to global links; it does not silently complete those uniform tasks.
