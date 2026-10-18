# Continuous-time construction: two operative attempts

Author derivation, unresolved. No claim that a full target is proved or that primary overlap is exhausted.

## Unperiodized passage and unavoidable overlap in the unchanged cutoff rule

The actual source passage uses disjoint neighborhoods of the sets E_r={(m_r(c+phi(u)),a):(u,a) in K_r}. For maps, c is a freely chosen integer. For vector-field approximation it cannot be freely chosen, as recorded in live-screen.md.

Putting c=0 does not merely invalidate a convenient proof convention. On a good arc choose a local coordinate in which phi(u)=u and whose value range includes (1,3). Choose nonnegative smooth w supported inside (2,3), of integral1, and a smooth amplitude v(a) with integral |v|²=1. The two packets with angular indices1 and2 and amplitudes

 A_1(u,a)=sqrt(w(u))*v(a),
 A_2(u,a)=sqrt(2*w(2u))*v(a)

have exactly the same unfolded pushforward density W(s,a)=w(s)|v(a)|². Smoothness is obtained by choosing w as the square of a bump. Their old angular orthogonality is exact. Both stationary images coincide over the support of w. The source's disjoint stationary-support trimming therefore cannot retain both norms: for disjoint retained subsets D_1,D_2 of the (s,a) image, retained squared norms sum to at most1, whereas the original sum is2. At least one unit of total squared norm is lost. Allowing smooth cutoffs with disjoint supports changes no bound. Normalizing both packets simultaneously does not remove this fixed fractional loss.

The spare-coordinate harmonics still make the exact transformed packets orthogonal before later passages. Hence this example does NOT prove that every continuous-time passage fails. It proves that dropping c while retaining the source's disjoint-image reduction loses a fixed amount on legal finite data. A new construction must retain and later resolve those internal harmonics rather than use the same disjoint cutoffs.

## Smooth time change of the suspension: explicit resonance interface

Work on the smooth mapping torus of the source map (its isotopy class must be checked before identifying this manifold with a standard torus). Write A_0=(1/(2 pi i)) d/dt for the self-adjoint generator of the unit-roof suspension. Its centered spectral decomposition consists of one simple Lebesgue channel and eigenvectors e_n(s)=exp(2 pi i n s), n nonzero integers.

Choose a real smooth base function h with zero integral and a real smooth height bump chi supported in (0,1). The function r(x,s)=h(x)chi(s) is smooth across the suspension seam. For sufficiently small epsilon, a time change by the positive clock1+epsilon r preserves a smooth volume proportional to (1+epsilon r) times the old volume. Under the standard unitary identification with the old L2 space, its generator is

 B_epsilon=(1+epsilon r)^(-1/2) A_0 (1+epsilon r)^(-1/2).

On smooth vectors its derivative at zero is V=-(r A_0+A_0 r)/2. Thus the old integer eigenvector couples to the continuous channel through

 V e_n=-(A_0+n)(r e_n)/2.

This is only an exact first-order formula, not a perturbative spectral theorem. In the direct integral model for the suspension, if p_h is the circle spectral density of h for the source map, the continuous spectral measure of r e_n has density

 p_(r e_n)(lambda)=|chi_hat(lambda-n)|² p_h(lambda mod1)

for almost every real lambda. This follows by Fourier expansion in height with the twisted boundary condition determined by the base spectral variable x, then setting lambda=x+k. In particular the candidate resonant density for the coupling at eigenfrequency n would be n² |integral chi|² p_h(0), if a suitable boundary value p_h(0) existed.

The actual source theorem supplies only an L1 spectral density for each smooth h and a flat cyclic vector which is merely L2. It supplies no continuous or limiting-absorption value at the specific base frequency0. L1 approximation of the flat vector by smooth functions does not establish a pointwise density at0. For example continuous probability densities which vanish on progressively smaller neighborhoods of0 can approach1 in L1 while all take value0 at0. One cannot insert p_h(0)=1 by smooth approximation.

Even a positive resonance density would not by itself establish the required result: every integer eigenvalue must disappear, no singular continuous component may be created, the complete continuous spectrum must remain equivalent to Lebesgue, and its multiplicity must stay one. The perturbation is an unbounded first-order differential operator, not a trace-class bounded perturbation to which a ready-made scattering theorem applies. These are substantive unpaid steps, not consequences of the displayed first variation.

## Actual primary comparison and limits

The source144 introduction is read in full and explicitly credits measurable simple-Lebesgue flows and smooth infinite-multiplicity flows. Prikhodko arXiv1002.2808v1 actual text lines120–205 gives a measurable cutting-and-stacking inverse limit and a flat exponential-sum theorem; this does not supply smooth coordinate control. FFK arXiv1609.03757v2 introduction through its Theorem1 was read; it constructs a real analytic torus flow with a singularity and countably infinite multiplicity. Neither is a substitute conclusion. Its later geometric multiplicity criterion is only located, not yet read. The attempted published Prikhodko2020 PDF returned403; no reading of that body is claimed. The2010 preprint is a distinct version, not silently treated as the2020 paper.

The two mechanisms above are unresolved routes toward a full smooth simple-Lebesgue flow. No component-only, nonsmooth realization, or infinite-multiplicity result is nominated.

## Retained spare harmonics: matrix-density norm obstruction

The source's first coordinate passage preserves exact old angular labels as harmonics exp(2 pi i m a') in the spare coordinate. Thus overlapping stationary images do not immediately destroy Hilbert-space orthogonality. However, after that spare coordinate supplies the next jitter law, conditioning on temporal frequency can expose those phases. Cancellation of their integrals alone is insufficient for the source's whitening estimate.

Here is an exact matrix-density model illustrating the distinction, not a claimed realization by the physical passage. Fix a smooth nonnegative compactly supported density w of integral1. The matrices

 M_N(lambda)=w(lambda) [[1,exp(i N lambda)],[exp(-i N lambda),1]]

are positive semidefinite of rank1 where w>0. Their diagonals are both w. Their off-diagonal measures converge weakly to0 against every bounded continuous test, by the Riemann–Lebesgue lemma. Yet

 integral |(M_N)_(12)|=1,
 integral ||M_N-w I_2||_(trace)=2.

Consequently rapid phases alone provide no matrix-density L1 convergence. For the sum of the two vectors, the scalar density is p_N=2w(1+cos(N lambda)); its L1 distance from2w tends to4/pi, using periodic averaging of |cos|. The same conclusion follows directly for any nonzero w by approximation by step functions. This is precisely the norm in which the source compares densities before whitening; weak convergence is not a substitute.

More explicitly, the Hellinger overlap with the desired scalar density2w is

 integral sqrt(p_N*2w) = 2 integral w sqrt(1+cos(N lambda)) -> 4 sqrt(2)/pi <2.

Both densities have masses tending to2 (the target exactly2), so their squared root-distance tends to4-8 sqrt(2)/pi>0. Whitening cannot be declared an arbitrarily small L2 perturbation from those oscillatory cancellations. The example does not exclude a genuinely averaging jitter construction that controls the entire matrix density. It identifies the required stronger norm estimate.

For a replacement passage that aims to recover the old diagonal or whitened target, actual averaging with strong matrix-density control is needed; fresh geometric variables would also require a proof of reuse in fixed finite dimension. This is not the only possible architecture. An alternative could retain a coherent rank-one spectral matrix with nonzero off-diagonal phase. Such a route must make that phase strongly Cauchy through subsequent passages while retaining physical vector and vector-field closeness. The oscillating example obstructs uncontrolled phase reset, not every coherent frame. Neither architecture is supplied by the presently read source interfaces. Frequency convolution by hand is not a deterministic smooth-flow construction. Constant suspension-height changes move n to n/c but the resonant base spectral argument remains0; they do not repair the boundary-value issue above.
