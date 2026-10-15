# Second-order unrestricted ball–slab contact and endpoint crossover

2026-10-14. **Research candidate: complete proposed proof, not independently
reviewed or accepted.** The full original competitor class is retained.
Upstream theorem truth is stipulated at
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Nothing here changes
an accepted count, publishes a result, or certifies worldwide novelty.

## 1. Exact statement and credited boundary

On the unit cubic flat torus T^3, let P be De Giorgi perimeter. For
R<1/3 and small epsilon>0 define, over all finite-perimeter pairs,

    L_R(epsilon) = inf { P(E)+P(F)-4pi R^2-2 :
                         E subset F a.e.,
                         |E|=4pi R^3/3, |F|=2(R-epsilon) }.

There are no symmetry, smoothness, topology, connectedness, or graph
restrictions. Write

    ell=|log epsilon|, S=epsilon^2/ell,
    T2=epsilon^2 log(ell)/ell^2, delta=1/3-R,
    g(R)=2pi sqrt(4R^3/3)-4pi R^2.

Let B_* be the compact translation orbit of radius-1/3 balls, let
eta_0=(4pi/81)/10, and let M_B be the same paired infimum with only the
additional closed constraint dist_L1(E,B_*)<=eta_0. F has its original
unrestricted class even in this auxiliary minimum.

**Proposed theorem.** Uniformly in the joint limit R<1/3, R->1/3,
epsilon->0,

    M_B(R,epsilon) = 2pi epsilon^2/(ell+log ell)
                         + O(epsilon^2/ell^2).                    (A)

In particular,

    M_B=2pi S-2pi T2+o(T2).                                     (B)

For all sufficiently close parameters, the original unrestricted minimum
satisfies the credited identity

    L_R(epsilon)=min{M_B(R,epsilon),g(R)}.                        (C)

Consequently, for every moving family R_epsilon<1/3 tending to 1/3,
with no rate or monotonicity assumption, if

    (delta_epsilon-3S)/T2 -> alpha in R,

then

    (L_(R_epsilon)(epsilon)-2pi S)/T2
                  -> min{-2pi,(2pi/3)alpha}.                    (D)

A precise sequential interpretation of the O in (A) is a uniform bound by
C epsilon^2/ell^2 for all sufficiently close parameters; constants do not
depend on delta/epsilon or delta/S. The result also includes fixed R in a
sufficiently small compact radius interval if the same localization and
regularity are made uniform there, but no such additional claim is needed.
No claim about the actual contact-set radius, radial symmetry of exact
minimizers, a unique transition, or exact coexistence is made. The shift
of the asymptotic crossing is delta=3S-3T2+o(T2).

Credited inputs: R018/I275/I277 supply the fixed-radius all-BV contact
reduction and exact charts; I346 supplies the leading uniform ball estimate,
two separated wells, and the exact cylinder local minimum g(R), hence (C).
Those are not new results here. The new argument is (A), particularly its
unrestricted nonlinear lower bound at a smaller scale. Formula (D) is an
algebraic consequence once (A) and the credited identity are proved.

## 2. Exact prior interfaces checked and used

The stipulated scalar input is actual Theorem `intro:main` of the pinned
cubic-three-torus paper. Its profile is

    I(V)=min{(36pi)^(1/3) v^(2/3),2 sqrt(pi v),2},
    v=min(V,1-V),

with exhaustive equality classification. At V=4pi/81 exactly balls and
shortest coordinate tubes occur. At outer limiting volume 2/3 the occupied
coordinate slab is the strict scalar minimizer, by complementation. Thus
both separate deficits in this problem are nonnegative for nearby R<=1/3.

Here is the I346 reduction being credited, including its quantifiers.
BV compactness gives exact global and closed-neighborhood localized paired
minimizers. A ball projects on a coordinate axis into an interval of length
2/3, whereas a coordinate tube has constant cross-sectional area 4pi/81
along its own axis. The endpoint ball and tube orbits therefore have L1
separation at least 2(4pi/81)/3. Their eta_0 neighborhoods are disjoint.
Any sequence of exact minimizers with R->1/3, epsilon->0 and deficit->0
has a ball/slab or parallel-tube/slab equality limit. Every sufficiently
low-energy exact global minimizer lies in one of the two neighborhoods.
This proves reduction to their two local minima for all sufficiently close
parameters, without restricting the original competitors.

For a localized minimizing replacement, the neighborhood boundary is
inactive. Free inner and outer patches of its equality limit give a common
ambient flow with an invertible two-volume Jacobian. For nearby measurable
pairs it corrects total volume error q with parameter, perimeter cost, and
L1 displacement O(q), preserving inclusion. Scalar lattice competitors
(H intersect F,H union F), or (E intersect H,E union H), have summed
perimeter at most the scalar comparison perimeter plus the unchanged
perimeter and total paired L1 change exactly the scalar symmetric
difference. Volume correction and local minimality give common scalar
quasiminimizing constants. Small comparison balls remain inside the
inactive constraint; larger balls and larger-perimeter comparisons obey
the trivial bounded-perimeter inequality. This covers every comparison
in AFM Definition 2.5, not only smooth or volume-preserving ones.

AFM Theorem 4.2 then gives whole-boundary normal graphs converging in
C^{1,beta} for every beta<1/2. The limiting boundaries can be disconnected;
the theorem applies separately to E and F. L1 convergence selects the
occupied slab interval. Reference centering removes exactly the three
sphere degree-one moments and makes each outward face height V^+,V^-
mean zero. The exact spherical mean is quadratic, not zero. These are
changes of representation of the same nested pair. The relative axial
center h is retained.

On the cylinder branch the centered Jacobi eigenvalues are
4pi^2 k^2+(m^2-1)/rho^2. At rho=2/9, after the transverse translation modes
are removed, the remaining gap is at least
min{4pi^2-81/4,243/4}>0. Its constant mode is quadratic by exact volume.
Hence a C1-small exact cylinder replacement has
P(E)>=2pi rho+c||u||_H1^2. Together with P(F)>=2 and the exact tube/slab
competitor with a fixed positive clearance, this proves its local minimum
is exactly g(R). This is an exact local bound; no error o(delta) is
normalized at the smaller scale T2. These checked steps are I346's
technical contribution and yield (C).

For ball-localized exact replacements I346 further gives, uniformly,

    ||psi||_H1 + ||V^+||_H1 + ||V^-||_H1 <= C sqrt(S),
    int_(S_R) psi omega_j=0, j=1,2,3,
    b=average_(S_R) psi=O(S).                                  (2.1)

The compact radius interval, free patches, chart denominators, sphere gap
and flow Jacobian stay uniformly nonsingular at R=1/3. Reading the complete
arguments is needed here; a fixed-R asymptotic is not substituted with a
varying R. Prior PASS labels alone are not premises for new deductions.

## 3. A quantitative nonlinear remainder from the actual AFM contract

This step uses the C^{1,beta} conclusion, not a rate assumed for C1
convergence. Fix beta=1/4. After normalized subsequences and rebasing to
S_R and the actual reference slab width, the graph C^{1,beta} norms are
bounded uniformly. AFM gives this on fixed limiting surfaces; smooth
rebasing and the finite-dimensional reference centering preserve a uniform
bound. If such a bound failed jointly, a sequence R_n->1/3, epsilon_n->0
of counterexamples would have a normalized smooth equality limit and
contradict AFM. The finite choices of slab axis and compact translation
orbits cause no loss.

Here is the elementary interpolation used. If a gradient has Hölder
seminorm bounded by C and maximum magnitude M, on a surface disk of radius
c M^(1/beta) it has magnitude at least M/2. Surface area is bounded below
by a constant times the squared radius. Therefore

    ||Du||_L2^2 >= c M^(2+2/beta),
    ||Du||_infinity <= C ||Du||_L2^(beta/(1+beta)).

For small M the disk is within a uniform reference chart; the nonsmall
case is excluded by the small L2 norm. Poincare/connectedness and the mean
bound control ||u||_infinity by C||Du||_infinity plus its mean. Use each
face separately. With (2.1), the reference sphere and face graphs obey

    ||psi||_C1 + ||V^+||_C1 + ||V^-||_C1 <= C S^(1/10).          (3.1)

The exact-volume sphere expansion from I277 is

    P(E)-4pi R^2 = Q_R(psi)/2 + Rem_B,
    Q_R(psi)=int_(S_R)(|D psi|^2-2psi^2/R^2),
    |Rem_B| <= C (||psi||_infinity+||Dpsi||_infinity^2)
                    ||psi||_H1^2.

The face remainder is at most C||DV||_infinity^2 ||DV||_L2^2.
Writing f=psi-b, the degree-zero/degree-one-free function f belongs to
the positive sphere Jacobi space, and Q_R(psi)=Q_R(f)+Q_R(b), with
|Q_R(b)|<=C S^2. Hence, for

    Q=Q_R(f)+int|DV^+|^2+int|DV^-|^2,

we obtain the quantitative relation

    D_R(E,F)=Q/2 + O(S^(11/10)+S^2).                          (3.2)

Since S^(11/10)=o(epsilon^2/ell^2), this is stronger than the needed
o(T2). No quantitative graph convergence was imported from an unstated
regularity theorem. It was deduced from AFM's bounded Hölder seminorm and
the paid energy estimate. This is the first reason the old o(S) remainder
need not remain an obstruction.

## 4. Full Jacobi/face inverse kernels and a uniform trace estimate

The second reason is that no fixed finite-mode truncation or fixed
relative localization loss is used below.

### 4.1 Kernel facts, proved directly

For the mean-zero flat unit two-torus, let G_T be the inverse kernel of
-Delta. It has

    G_T(x,y)=-(1/(2pi)) log|x-y|+O(1)                         (4.1)

in a fixed diagonal chart, with a bounded remainder, and is bounded away
from the diagonal. One construction suffices: take a smooth compactly
supported cutoff of -(1/(2pi))log|x| in a period cell. Its negative
Laplacian equals delta_0 plus a smooth annular function of integral -1.
Subtract the smooth mean-zero error using its Fourier coefficients divided
by 4pi^2|k|^2. The correcting series is smooth and bounded, since the error
is smooth. This constructs (4.1) with mean zero.

On S_R, let K_R be the inverse of -Delta_(S_R)-2/R^2 restricted to
spherical degrees l>=2. By the addition formula it is

    K_R(R omega,R eta)
       = sum_(l>=2) (2l+1) P_l(omega dot eta)
                              /[4pi(l(l+1)-2)].              (4.2)

The sphere mean-zero Laplace inverse has coefficients
(2l+1)/[4pi l(l+1)], l>=1, and kernel
-(1/(4pi))log(1-omega dot eta)+a constant. The latter follows directly
by applying the spherical radial Laplacian off the pole and checking the
unit logarithmic flux at the pole. The difference between its l>=2
coefficients and (4.2) is O(l^-3), uniformly summable since |P_l|<=1;
removing degree one is a bounded finite-rank term. It follows that

    K_R(x,y)=-(1/(2pi))log|x-y|+H_R(x,y),
    |H_R(x,y)|<=C,                                          (4.3)

uniformly for R in a fixed compact positive radius interval; K_R is also
bounded on the two opposite polar patches. The normalization is with
respect to physical sphere area. Indeed the R^-1 normalization of each
spherical eigenfunction cancels the R^-2 eigenvalue. The change from
unit chord distance to physical distance adds only log R, uniformly
bounded here. This argument handles all low nontranslation modes exactly.

For a bounded weighted C1 curve measure sigma with a finite logarithmic
self-integral, the squared norm of its trace functional on the appropriate
quadratic space is its double kernel integral. This can be verified by
finite Fourier/spherical sums and the Cauchy–Schwarz inequality, then by
smooth approximation of the measure. In the present curves the only
singularity is log|theta-phi|, which is integrable; mollification has the
same uniform logarithmic majorant. Alternatively apply the identity first
to smooth graphs and smooth source densities and pass to the trace limit.
For our C1 graph functions the traces also converge uniformly under smooth
function approximation. Thus the only inequality needed is rigorously

    |int u d sigma|^2 <= Q_surface(u)
                              int int K d sigma d sigma.    (4.4)

Projection onto mean-zero, or onto l>=2, is already built into K; sigma
itself need not have zero mass. On a direct sum of quadratic spaces the
kernel norm is the sum of their kernel integrals. No H1 point trace occurs.

### 4.2 The actual deformed circles

For a ball replacement, the exact I275/I277 chart gives at either pole

    W^pm(x)=A_pm(x) psi(F_pm(x)),
    A=(2R+p)/[sqrt((R+p)^2-|x|^2)+sqrt(R^2-|x|^2)],
    p=psi(F(x)),                                            (4.5)

where F is the actual inverse horizontal parametrization, not its reference
approximation. At physical horizontal radius a, the maps

    theta -> F_pm(a(cos theta,sin theta))

are uniformly bilipschitz at scale a: their pairwise physical chord
lengths are between c a|exp(i theta)-exp(i phi)| and
C a|exp(i theta)-exp(i phi)|. Indeed the forward horizontal map is
G(y)=(1+psi(q(y))/R)y, whose derivative is uniformly close to I;
its inverse and the reference sphere graph have uniform bilipschitz
constants on a fixed polar chart. This estimate is for *all* angular pairs,
including near the diagonal. The two polar curves stay a fixed positive
distance apart.

A useful exact cancellation is A(p,0)=1 for every small p. Smoothness of
(4.5) in the fixed compact coordinate range and its dependence on |x|^2
therefore imply

    |A_pm(a exp(i theta))-1|<=C a^2.                        (4.6)

There is no additive O(||psi||_C1) pointwise height error. This is why the
actual nonlinear chart can be retained in the dual estimate.

On the direct sum space for (f,V^+,V^-), define

    Lambda_a(f,V)=sum_pm (1/(2pi)) int_0^(2pi)
        [V^pm(a exp(i theta))
         -A_pm(a exp(i theta)) f(F_pm(a exp(i theta)))] dtheta.

The two torus source measures have mass one each. The two sphere source
measures have density A_pm dtheta/(2pi), mass 1+O(a^2) each; they enter
with the same negative sign. Each of the four self-kernel integrals is

    (1/(2pi))log(1/a)+O(1)+O(a^2 log(1/a)).

To see the uniform O(1), divide pairwise distance by a and use the
bilipschitz estimate and integrability of
|log|exp(i theta)-exp(i phi)||. The weighted masses give exactly the
stated O(a^2 log(1/a)) correction. The sphere cross integral is bounded
by separation of the two poles. The two faces occupy different quadratic
summands, so there is no cross-face kernel term. For 0<a<a_0, this proves

    ||Lambda_a||_*^2 <= (2/pi)log(1/a)+C,
    Lambda_a(f,V)^2 <= [(2/pi)log(1/a)+C] Q.                 (4.7)

All constants are uniform in the actual small C1 graphs and in nearby R.
The four self traces, not just two, must be counted. Their coefficient
2/pi is essential for the final 2pi energy coefficient. The bounded
regular part contains global volume and low-mode effects; they are not
lost at the larger energy scale S.

## 5. Unrestricted lower bound at the second scale

Take an arbitrary sequence of ball-localized exact minimizing replacements
with R->1/3, epsilon->0. Use the normalizations and estimates above. Actual
inclusion in vertical coordinates is exactly

    V^pm(x)-W^pm(x) >= epsilon +/- h
                           -q_R(|x|),
    q_R(r)=R-sqrt(R^2-r^2).                                (5.1)

Choose the deterministic test-circle radius

    a=sqrt(epsilon/ell), L=log(1/a)=(ell+log ell)/2.

This is a test radius, not a claim that an unknown contact set is circular.
Sum the two circle-averaged inequalities. The relative axial drift cancels
exactly. With psi=f+b, (4.5)–(4.6) and (2.1) give

    Lambda_a(f,V) >=2epsilon-2q_R(a)-C|b|
                  >=2epsilon-C epsilon/ell-C S.            (5.2)

Here q_R(a)=a^2/(2R)+O(a^4), uniformly. The last expression is positive
for small epsilon; no bound on h/epsilon is required. Applying (4.7),

    Q >= [2epsilon-C epsilon/ell-C S]^2 /[(2/pi)L+C].

Using (3.2) and expanding only bounded algebraic denominators yields

    M_B(R,epsilon) >= pi epsilon^2/L-C epsilon^2/ell^2
                  = 2pi epsilon^2/(ell+log ell)
                                      -C epsilon^2/ell^2.   (5.3)

The error S^(11/10)+S^2 was absorbed because it is o(epsilon^2/ell^2).
Every constant is uniform along every such sequence. Uniformity for all
sufficiently close parameters follows by contradiction and the same
compact normalized limit/AFM argument; no rate of R->1/3 is introduced.

This proves a lower bound for the auxiliary exact minimum over its full
finite-perimeter class. Arbitrary original competitors have at least the
minimum; they have not been declared graphs, quasiminimizers, or symmetric.
Unlike I275's leading argument, no fixed loss 1-zeta or unspecified o(S)
remains at this step. No nonlinear free-boundary PDE or unknown contact-set
shape is being assumed.

## 6. Tangent obstacle recovery with exact volumes

Fix a small d>0 uniformly below the polar chart radius and the fixed free
patch clearances. Let a=a(R,epsilon) be the unique small solution of

    a^2[log(d/a)+1/2]=R epsilon,
    H=log(d/a), A=a^2/R=epsilon/(H+1/2).                     (6.1)

Uniqueness follows because the derivative of the left side is
2a log(d/a)>0 for 0<a<d. The solution is small for small epsilon.
Define a nonnegative radial relative-height profile by

    Z(r)=epsilon-r^2/(2R),      0<=r<=a,
    Z(r)=A log(d/r),            a<r<=d/2.

The values and derivatives agree at r=a by (6.1). On d/2<r<d use a fixed
smooth nonnegative outer cutoff of the logarithmic expression, vanishing
smoothly at d. This modifies all energies by O(A^2), all L1 norms by
O(A), and does not affect the contact region. At r=a the profile is C1
with bounded piecewise second derivatives, sufficient for an admissible
C1,1 graph and the area calculation. No uncounted vertical rim is present.

The logarithmic portion is above the parabolic obstacle: their difference
vanishes at a and its derivative for r>a is
r/R-a^2/(Rr)>=0. In the cutoff region r>=d/2 the obstacle
 epsilon-r^2/(2R) is negative and Z>=0. Thus everywhere

    Z(r)>=epsilon-r^2/(2R) where that right side is positive,
    Z(r)>=epsilon-q_R(r) on the full polar chart.             (6.2)

Use *actual horizontal coordinates*. On the upper sphere cap replace
sqrt(R^2-r^2) by sqrt(R^2-r^2)-Z(r)/2; on the lower cap reflect this
construction. Move each corresponding flat outer face outward by Z(r)/2.
Then the actual gap is

    q_R(r)-epsilon+Z(r)>=0.

Outside the caps the original gap is positive. This proves inclusion of
the entire inner boundary. Its embedded compact vertical slices have
their extrema on that boundary, while the outer occupied slices are
intervals. Hence the entire region is contained. The initial inner
modification only contracts the ball on the two polar caps.

Both lost inner volume and gained outer volume are O(epsilon/ell). Apply
independent corrections on the same fixed free equatorial and exterior
face patches as I275/I346, with exact amplitudes O(epsilon/ell). The
inner correction expands a patch strictly inside F; the outer correction
contracts a patch outside E. Uniform positive gaps preserve inclusion.
The inverse-function volume equations are exact. Correcting supports are
disjoint from the polar supports and the two target volumes are attained.
All interfaces remain admissible finite-perimeter boundaries. A smooth
recovery could also be obtained by rounding the C1,1 junction with an
arbitrarily smaller obstacle-preserving perturbation; this is not needed
for the all-finite-perimeter infimum.

Here are the energy errors at the required scale; fixed d is not sent to
zero after epsilon. Direct radial integration gives, before the outer
cutoff change,

    J=int|DZ|^2
       = pi a^4/(2R^2)+2pi a^4 H/R^2
       = 2pi epsilon^2 (H+1/4)/(H+1/2)^2,                  (6.3)
    int Z = O_d(epsilon/ell),
    int Z^2=O_d(epsilon^2/ell^2),
    int r^2|DZ|^2=O_d(epsilon^2/ell^2),
    ||DZ||_infinity=O(sqrt(epsilon/ell)).                  (6.4)

The fixed cutoff changes J by O(A^2)=O(epsilon^2/ell^2) and preserves
(6.4). For example the annular weighted-gradient integral is
2pi A^2 int_a^d r dr=O_d(A^2); the core contributes O(a^6).
The annular L2 integral follows by the substitution log(d/r); the core
contributes O(epsilon^2 a^2). These are uniform in nearby R.

For completeness, compute the inner cap area in vertical coordinates,
not with a fixed metric distortion factor. The reference graph is
s_0(x)=sqrt(R^2-|x|^2), the change is v=-Z/2, and Taylor expansion of
sqrt(1+|Ds_0+Dv|^2) gives its linear first variation, quadratic coefficient
I+O(r^2), and error at most C||Dv||_infinity int|Dv|^2. The integrated
linear term is (2/R) times the signed cap volume change. It cancels with
the first variation of the exact equatorial volume correction; the latter
has quadratic remainder O((epsilon/ell)^2). Thus the fixed-volume inner
quadratic cap cost differs from one half of its *flat* Dirichlet energy
only by the weighted-gradient term in (6.4), the correcting-bump cost,
and the cubic gradient remainder, all O(epsilon^2/ell^2). No fixed
relative O(d^2) loss is retained. The lower cap has the same sign after
using its outward displacement convention.

Each face has the ordinary flat Dirichlet expansion and a quartic-gradient
error. Its correction cost is O(epsilon^2/ell^2); there is no flat-face
linear area variation. Four patches with individual height magnitude Z/2
therefore contribute J/2 in total, up to O(epsilon^2/ell^2). Consequently

    D_R(recovery) <= pi epsilon^2 (H+1/4)/(H+1/2)^2
                                      +C epsilon^2/ell^2.    (6.5)

Equation (6.1) implies

    2H=ell+log(H+1/2)+log(d^2/R),
    H=(ell+log ell)/2+O_d(1),                              (6.6)

uniformly in nearby R. To justify the last expansion first the defining
equation gives H~ell/2, and then its logarithm is log ell-log 2+o(1).
Substitution in (6.5) gives the upper bound matching (5.3). The recovery
converges to the radius-R ball, so it belongs to the ball neighborhood
for all sufficiently close parameters. This proves (A).

The constructed tangent radius satisfies a^2~2R epsilon/ell. This is
supporting geometry of the recovery, not a theorem that every minimizer
has a circular contact set of that radius. The lower bound only tested
an arbitrary shrinking circle at the comparable scale.

## 7. Expansion and crossover

The identity

    1/(ell+log ell)
      =1/ell-log ell/ell^2+O((log ell)^2/ell^3)

and (A) imply (B), since epsilon^2/ell^2=o(T2) and
(log ell)/ell->0. Uniformity in R is preserved.

Direct differentiation of g at R=1/3 gives g'(1/3)=-2pi/3;
Taylor expansion with a bounded second derivative gives

    g(1/3-delta)=(2pi/3)delta+O(delta^2).                    (7.1)

Under delta=3S+alpha T2+o(T2), one has delta=O(S) and
delta^2/T2=O(epsilon^2/log ell)->0. Thus

    (g(R)-2pi S)/T2 ->(2pi/3)alpha.

Apply the exact identity (C) and (B) to obtain (D). No unspecified
leading-order error is compared at scale T2. The cylinder's error is
exactly zero before its elementary Taylor expansion; the ball's error
is quantitatively O(epsilon^2/ell^2).

## 8. Research status, incremental mechanism, and review targets

This is a complete proposed proof under the precise scalar and AFM inputs,
not an independent PASS. The essential new lower passage is the combination
of (i) quantitative nonlinear control derived from the already available
C^{1,beta} regularity, and (ii) a full positive Jacobi/face trace compliance
for the *actual* deformed curves. It avoids both a growing low-mode cutoff
and a fixed geometric loss, while retaining all nontranslation low modes.
The summed trace also cancels axial drift exactly. The upper bound pays
curvature and volume corrections at O(epsilon^2/ell^2) through integrated
weighted errors, rather than a fixed relative chart estimate.

The contact-radius logarithm and its log–log inversion are classical;
see the bounded primary-literature record in literature.md. Neither that
formal inversion nor the technical minimum-of-two-wells step is nominated
as a discovery. Whether the new all-BV second-scale lower passage is a
substantial incremental contribution beyond R018 is for a separate
independent contribution gate. This research proposes it as a candidate
for that assessment, without a count increment or priority claim.

Focused proof-gate checks: uniform C^{1,1/4} bounds after changing radius
and reference centers; interpolation (3.1); the sphere kernel normalization
and uniformly summable difference series; weighted actual-curve self
energies and the four-trace factor in (4.7); exact drift cancellation;
fixed-volume vertical area cancellation and integrated O(r^2) upper errors;
and the credited exact two-well/cylinder identity over the full BV class.
