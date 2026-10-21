# Paying the all-state spectral interface

PREFREEZE calculation within the Source215/Hepp composition. This is not a frozen theorem, separate candidate or grade. It uses the actual all-state source proofs to remove a potentially stronger reading of Hepp SectionIII's spectral hypothesis. Constants below are explicit choices relative to source m1 and count constant C, not numerical estimates of those source constants.

## Polynomial spectral measures, with all limits in the source order

Let F be a centered finite linear combination of products of smooth fields in strictly ordered positive-time slabs, the dense class constructed in C os.tex's full-gap proof. At finite cutoff and circumference w, truncate each real smeared field at +/-w inside F, form its normalized slab insertion A_F, and subtract its cylinder vacuum expectation. Call the resulting vector v_{N,w}. If degree(F)=d, the bounded insertion norm is O_F(w^d). P tra:comparison and inp:tails compare its reflected products to the corresponding continuum polynomial products: the comparison error is a polynomial in w times exp(-c_F w). The truncation tail is exp(-c_F w), by factorial moment bounds and Holder. These claims concern finitely many fixed tests, not an expanding collection of F's.

For each fixed integer n>=0 and allowed momentum p define

  nu_{F,N,w,p}=(w/(2pi)) sum_E ||P_E Pi_p v_{N,w}||² delta_(exp(-E)).

The source character formula is unchanged apart from this explicit1/(2pi) normalization, so continuum momentum densities are with respect to dp. For two copies displaced spatially by b∈[-w/2,w/2], their supports fit the3w/4 comparison rectangle once w is large (their time extent n+2l is fixed). The sum over b costs a factor w; it is absorbed in the exponentially small error. Moment convergence plus difference-test bounds give equicontinuity on each fixed spatial interval. C polynomial slab clustering, rotated to spatial separation, bounds the omitted continuum tail exponentially in |b| for every fixed n. Consequently P mass:moments and its positive-polynomial continuous-test passage apply to every such F, and to finite sums of their positive spectral measures:

  lim_(dyadic w->infinity) limsup_(N->infinity) max_(p in I grid)
       | integral Psi(p,x) dnu_{F,N,w,p} - L_{F,Psi}(p) | =0.       (A)

Here I is fixed compact and Psi is continuous on I×[0,1]. The continuum function L is continuous. To justify this without assuming continuous disintegration: Fourier transforms of all integer-time kernels give continuous moment densities in p; n=0 uniformly bounds their masses on I. Polynomial approximation in x then gives a continuous functional for each continuous Psi. Positivity, initially a.e. from the joint spectral measure, extends to every p by continuity. This is the same positive-moment argument as the source. Arbitrary sharp spectral projections are not passed through(A).

## The full mass bottom really is m1

P vis:gap says that for every v<m1, all sufficiently large fixed dyadic w have e_N(w)>v for sufficiently large N. The above centered vectors satisfy

  <v_Nw,T^(n/a)v_Nw> <= exp(-vn)||v_Nw||².

Their norm and each fixed-n matrix element converge in the iterated limit to ||[F]||² and <[F],exp(-nH)[F]>. First take N at fixed w and then w; only after these limits take integers n->infinity in the positive spectral measure argument. Hence [F] has no H-spectrum below v. Density and v↑m1 give H|Omega_perp>=m1. The spin atom gives the opposite bound on the infimum, by packets with momenta tending to0. Poincare covariance then excludes invariant mass below m1: boosting any timelike spectral point with smaller mass to rest would contradict the energy bound. Thus the bottom of the full nonvacuum invariant mass support is m1, not just the spin-visible bottom.

If desired the same argument for even polynomials uses P par:even-gap to give H_even|Omega_perp>=2m1. Parity is preserved by the odd clipping of each elementary field. This is a direct source spectral transfer, not an additional candidate; it is not needed for the following count.

## Upgrade finite spin-visible mass support to finite full mass support

Set u0=3m1/2, p0=m1/4, I=[-p0,p0]. We show how the actual source all-state bound N_{N,w}(u0)<=Cw in limsup_N controls all mass values near m1, rather than relying on a putative common nonzero form factor.

Choose J distinct points of the full invariant mass spectrum in [m1,5m1/4]. Choose pairwise disjoint open mass intervals O_j contained in (m1/2,4m1/3), and compact subintervals K_j⊂O_j whose spectral projections are nonzero. Each K_j can be chosen around its selected support point. In each mass spectral subspace choose a unit vector z_j with rapidity eta in[-1,1]. Such a vector exists: some bounded rapidity interval has nonzero projection, and boosts translate rapidity; alternatively partition the rapidity axis into unit intervals and boost a nonzero piece to the origin.

Average its rank-one density operator over boosts:

  R_j=(1/4) integral_(-2)^2 |U(a)z_j><U(a)z_j| da.

This is a positive trace-class operator of trace1, supported in mass K_j. The spectral measure transforms by eta->eta+a. Since the original rapidity lies in[-1,1], its boost-averaged joint measure, restricted to |eta|<=1, is exactly (1/4) zeta_j(dmu) d eta, where zeta_j is the original mass probability. No a priori absolutely continuous mass measure or smooth form factor is assumed. At fixed mu, p=mu sinh eta and d eta=dp/sqrt(mu²+p²). For p∈I, mu>=m1 on the spectral support, so |eta|<1. Its spatial momentum density is therefore at least

  a0 = 1/[4 sqrt((4m1/3)²+p0²)] >0,                         (B)

uniformly in j. Every energy here is <u0, since sqrt((4/3)²+(1/4)²)<3/2.

Choose continuous0<=Psi_j(p,x)<=1, equal1 on the (p,exp(-sqrt(p²+mu²))) images of I×K_j, supported on the images of I×O_j and on x>exp(-u0). The supports for different j are disjoint at every p. Such functions exist by compact containment and continuity; they can be extended by0 to the rest of I×[0,1]. Applying Psi_j to R_j preserves its density on I, hence the lower bound(B).

Approximate R_j in trace norm by a positive finite sum

  S_j=sum_l |w_jl><w_jl|,

where every w_jl is a centered OS polynomial state of the class used in(A). This follows by norm-continuity of boost orbits, finite Riemann sums of rank-one operators, and density of that polynomial class; the inequality |||u><u|-|v><v|||_1 <=(||u||+||v||)||u-v|| pays each replacement. Arrange ||S_j-R_j||_1 < a0|I|/8.

For a projection-valued joint spectral measure, total variation of the signed scalar measure induced by a selfadjoint trace-class difference is at most its trace norm. Multiplying by the bounded test Psi_j preserves that bound. Thus the continuous density

  L_j(p)=sum_l L_{w_jl,Psi_j}(p)

differs in L1(I) by <a0|I|/8 from the corresponding R_j density, which is >=a0. The open set G_j={p∈I:L_j(p)>a0/2} has complement of length <|I|/4. Choose a finite union of compact intervals U_j⊂G_j, of length >=|I|/2. A finite union suffices by inner approximation of an open subset of a bounded interval; no regularity of its boundary is presumed.

For the finite collection of all w_jl and Psi_j, (A) now ensures, for all sufficiently large fixed dyadic w and then sufficiently large N, a strictly positive finite-cylinder Psi_j integral at each allowed momentum p∈U_j. Hence there is at least one transfer eigenstate of energy<u0 in the j-th mass filter at that momentum. Different j have disjoint energy filters at the same p, and different momenta give orthogonal subspaces. Lattice-point counting in each fixed finite union U_j gives at least |I|w/(8pi) points for sufficiently large w. Therefore

  N_{N,w}(u0) >= J |I|w/(8pi).

Taking limsup_N and using P cou:linear yields J<=8pi C/|I|. The bound is independent of which J masses were chosen; the required w and N may depend on the finite selection, as in the source proof. Thus the full invariant mass spectrum has only finitely many values in [m1,5m1/4]. Its minimum m1 is isolated from the remaining full mass spectrum by some positive gap.

This calculation asserts no uniform numerical gap, no multiplicity bound, no classification of the higher spectrum, and no uniform simultaneous N,w limit. The spin triplet is still the specified scattering subspace. The boost average and trace-norm approximation address the form-factor issue explicitly, rather than supposing every local polynomial detects every momentum.

## Role in this round

This is a compatible extension of the source's all-state count/momentum proof using standard spectral averaging and the source's actual OS polynomial density. It pays the stronger full-mass-isolation reading of H SectionIII before applying its LSZ conclusion. It is retained within the source/classical reduction, not offered as a substantial standalone result or a restricted substitute for an old target. The separate missing nonroutine operation remains nonvanishing of the canonical field's connected on-shell amplitude. The present bound does not supply that amplitude.
