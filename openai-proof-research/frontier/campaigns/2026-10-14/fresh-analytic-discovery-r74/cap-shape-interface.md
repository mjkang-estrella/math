# Shape and conditional Busemann inputs for the cubic cap

Live supporting derivation; no full-target conclusion. Actual AH lines380–670
were read without output truncation in this continuation. In particular its
Proposition3.4 and Proposition4.2 proofs are now actual proof-body reads.
Boivin's original paper remains unread; the following local estimate avoids
relying on a guessed version of that theorem.

## Uniform local metric continuity

The local approximation and row concentration in same-status-lowering.md
also apply to every horizontal/vertical segment of length between eta*n and
4n in [-2n,2n]^2, for each fixed eta>0. Assign deviations proportional to
segment length, not to n. There are polynomially many such segments, and the
failure bound is polynomial(n,R) exp(-c_eta n/R^7), plus the same coupling
error Cn² exp(-c sqrt(R)), with R=ceil(log(n+2)^4). Both are summable in n.
Consequently, almost surely for all large n, all such segments have s-cost
at most C times their length, with fixed C independent of eta. Shorter
segments are bounded by extending them to length ceil(eta*n) within the box
(or its fixed enlargement); positivity then bounds their costs by C eta*n.
Two coordinate segments give, for every fixed eta>0, almost surely eventually

 T_s(x,y) <= C' (|x-y|_1 + eta*n),  x,y in [-n,n]^2.

This is metric equicontinuity on macroscopic scales, with an arbitrarily small
linear remainder. It is stronger than merely a uniform diameter bound.

## Ordinary shape via the standard subadditive ergodic theorem

The cap is a translation-equivariant factor of iid original and auxiliary
variables, so every nonzero lattice translation is mixing and ergodic. Its
edge expectations are finite. The standard subadditive ergodic theorem gives
for each integer z a deterministic limit T_s(0,kz)/k=mu(z), almost surely and
in L1. This is the usual radial input, stated in AH(3); it is a standard tool,
not a new theorem or a claim of having read Kingman's original paper.
The triangle inequality and stationarity in expectation give subadditivity
and symmetry of mu. The uniform cheap-long-path exclusion in the previous
note gives mu(z)>=c|z|_1; coordinate paths give mu(z)<=C|z|_1. Homogeneity
extends it to a norm on R², with lattice symmetries inherited from the cap.

Take a finite rational directional net. Radial convergence holds simultaneously
on its finitely many rays. Approximate any x of size n by a lattice point kz
on that net within eta*n. The local continuity bound above controls
|T_s(0,x)-T_s(0,kz)| by O(eta*n), and the norm continuity controls
|mu(x)-mu(kz)| similarly. Let eta decrease through a countable sequence.
Thus sup_{|x|>=n}|T_s(0,x)-mu(x)|/|x| tends to zero almost surely.

The extended version in AH Proposition3.4 can now be obtained from its actual
proof: use a fixed high-probability radius after which the origin shape
estimate holds, translate this good-center event, and apply the spatial
ergodic theorem to bound the density of bad centers. Every far center is
within O(sqrt(density)*|x|) of a good center; triangle inequalities transfer
the estimates. This yields the same uniform shifted metric estimate used
there, with arbitrary error epsilon*max(|x|,|y|). The fixed-radius good-center
event is the precise stationary event underlying the displayed density step;
no ergodic theorem for a varying event is assumed.

## Conditional Busemann linearity

If a measurable translation-covariant coalescing family G has been constructed
for s, its Busemann differences are bounded by T_s(x,y), hence integrable,
additive and stationary. Each directional translation is ergodic on the
underlying iid space, so the additive ergodic theorem yields radial limits
rho_G(z)=E B_G(0,z). The same directional net plus the local continuity bound
upgrades radial to uniform linearity, exactly as in the actual AH4.2 proof.
Its extended shifted version follows by the same good-center argument.
The supporting-line and eventual-half-plane conclusions then follow as in
AH4.3. This statement is conditional on the existence of the coalescing family;
it does not construct one or justify label stability.

## Remaining scope

The cap's ordinary and extended shape inputs do not imply an original
moment-free uniform shape theorem: original endpoint correction B(x) need
not have moments. All uses here concern the integrable cap metric only.
The original full-plane target remains unfinished. Initial reference-family
existence, exact AH label setup/finite-change stability, and the pinned
source212's later iid fork/tilt mechanism still require a complete compatible
proof. No independent gate, nomination, or new-to-literature verdict is given.

## Explicit fixed-event extension used by the unified draft

Here is the good-center quantifier order. Fix target error eps>0. Choose a
small deterministic delta>0 so that the local continuity error and norm error
at displacement delta N are <eps N/4; choose the local continuity tolerance
eta similarly. Then choose a small radial error alpha>0. For integer R let
Q_R(z) mean that |T_s(z,w)-mu(w-z)|<=alpha|w-z| for EVERY lattice w with
|w-z|>=R. Ordinary rooted shape implies P(Q_R(0))->1. Choose ONE finite R so
that P(Q_R(0)^c)<c delta², with c smaller than the lattice volume ratio below.
This is a fixed stationary event. Spatial ergodicity says that eventually the
number of bad centers in [-3N,3N]² is less than 2c delta² times its area.
Choose c so that this is smaller than the lattice-point count of ANY radius
(delta N)-ball centered in [-N,N]² (all such balls lie in the larger box).
Consequently every x in [-N,N]² has a good z within delta N.

For x,y in [-N,N]², if |y-z|>=R, compare T_s(x,y) with T_s(z,y) by the
triangle inequality, apply Q_R(z), and compare mu(y-z) with mu(y-x).
The error is at most C(delta+eta)N+alpha(3N)+C_mu delta N. If |y-z|<R,
then |y-x|<=R+delta N, and local metric continuity bounds BOTH T_s(x,y)
and mu(y-x) by O(R+(delta+eta)N). First fix delta,eta,alpha small enough,
then let N grow. This proves sup_{x,y in[-N,N]²}|T_s(x,y)-mu(y-x)|<=eps N
for all sufficiently large N. Taking N comparable to max(|x|,|y|) and adding
a finite constant for the remaining pairs yields the extended bound used
in the draft and parent pasting note. No varying-event ergodic theorem is used.

For a stationary additive Busemann field of a measurable coalescing family,
repeat with Q_R defined by its rooted linear approximation. The comparison
error |B(x,y)-B(z,y)|=|B(x,z)| is bounded by T_s(x,z), and the slope is bounded
by the norm. The identical fixed-event argument gives its extended linear
estimate. For increment fields on an enlarged stationary space whose slope
is a translation-invariant random functional, one may instead use the rooted
uniform asymptote directly: additivity gives B(x,y)=B(0,y)-B(0,x), so the
error is bounded by eps(|x|+|y|)+C_eps. The functional is constant within
that realization; no ergodicity of the enlarged space is presumed.
