# Full strict-BV continuity, continuation r2: unresolved

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party material is private
and retains its original rights. This is research work, not a manuscript,
independent proof review, contribution approval, acceptance or publication.

**Full target B is neither proved nor disproved in this continuation.**
There is no substantial complete theorem nomination. In particular, the old
Sobolev continuity result A remains technical and is not re-nominated.

The new work below proves the full tail condition U-tail, proves continuity
of each fixed positive-lower-radius envelope under the original signed
strict convergence, and identifies a vanishing fine-scale source budget.
It also treats arbitrary monotone signed flat profiles, rather than just
the old symmetric ramp. These are progress toward B, not substitutes for it.
The sharp local measure inequality U-sharp remains unpaid in its full scope.

## 1. Unchanged statement and authenticated starting point

Put

    A_r g(x) = (pi r^2)^(-1) integral_{B(x,r)} g,
    M f = sup_{r>0} A_r |f|.

The balls are centered Euclidean disks. BV(R^2) means real, globally
integrable functions with finite Euclidean distributional variation.
The precise target is:

    for EVERY f,f_j in BV(R^2),
    ||f_j-f||_1 -> 0 and |Df_j|(R^2) -> |Df|(R^2)
    imply |D(M f_j)|(R^2) -> |D(M f)|(R^2).                 (B)

There are no support, sign, smoothness, jump or Cantor restrictions.
The output lies in L2 intersect BV_loc with globally finite variation;
global L1 output is not asserted. The already-paid local L1 convergence of
M f_j to M f and the resulting variation lower passage are retained.
Strict convergence is never replaced by ||Df_j-Df|| -> 0.

The full frozen r5 directory is retained byte-for-byte under
`inputs/private/frozen-r5/`. Its seal has the user-supplied detached SHA256

    0141a77c195a33b988dea9621bbf45577414b22ed0d8a0723c436a665764bc24.

Before executing its verifier, this continuation authenticated that hash,
both inventories, and every inventoried input/output. Its read-only verifier
then replayed its checker successfully: 74 authenticated files, B unresolved,
no substantial complete theorem. This is authentication and self-checking,
not an independent proof PASS of A. Its full candidate and prior findings
are appended to `assignment-and-history.md`, together with the full supplied
original brief and current objections.

## 2. Source contracts and standard operations

All pinned mathematical premises are accepted under the user's stipulation,
not audited. The revision is
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` in openai/math. Set P to

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/build/

The actual interfaces used are:

* P + `sections/introduction.tex`, `thm:main`: W11 input yields W11_loc
  output and a global L1 gradient bound with an absolute constant C.
* P + `sections/extension.tex`, `lem:sobolev-band`: the SIGNED envelope
  S_{a,b} g has variation at most C ||grad g||_1 when b/a is a power of two,
  independently of the number of scales, and Lipschitz constant at most
  ||grad g||_1/(pi a^2). This is stronger than the abstract norm theorem.
* The same section, `cor:bv-input`: every real BV input has the output
  specified above, with |D(Mf)|(R^2) <= C |Df|(R^2).
* P + `sections/prices.tex`, `eq:hat-refinement`,
  `eq:prices-scalar-defects`, `eq:prices-scalar-defect-budget`: the EXACT
  telescoping scalar cancellation budget, including the terminal density.
* P + `sections/local.tex`, `lem:local`, `eq:local-direction`: local
  unfavorable directional gradients cost discounted error pieces and do
  not charge the positive cone measures. The full multiscale assembly
  additionally pays endpoints, direction changes and spatial weights.
  This interface is examined as a possible route, not assumed to give B.
* P + `appendices/analytic-tools.tex`: translation, max/equality-set
  calculus, square localization, Euclidean variation and local lower
  semicontinuity. The full appendix was read in this continuation.

`source-contracts.json` separates current read extents from inherited ones,
and gives exact local paths, labels and URLs. The source's constant C does
not become 1 by a continuity or compactness assertion.

Some BV operations used below can be obtained directly from these
approximation and variation operations. In particular, for g=|f|,

    g in BV,             |Dg| <= |Df| as measures.             (2.1)

Indeed mollify f, use the Sobolev chain inequality, and test local variation
against compactly supported smooth vector fields. For a nonnegative
continuous compact weight psi, the resulting bound is the limit of
integral psi (rho_epsilon*|Df|), which tends to integral psi d|Df|.
The test-field supremum gives (2.1). The same approximation proves the BV
translation bound ||g(.+z)-g||_1 <= |z| |Dg|(R^2).

If f_j converges strictly to f, write mu_j=|Df_j|, mu=|Df|. Then

    mu_j -> mu narrowly, and {mu_j} is tight.                  (2.2)

Here is a proof that does not require strong derivative-measure convergence.
Distributional convergence and uniform total variation give Df_j -> Df
against C_0 vector tests. Every vague cluster lambda of mu_j satisfies
lambda >= mu by the local variation formula, whereas its total mass is at
most lim mu_j(R^2)=mu(R^2). Thus lambda=mu. For any open ball B_R,
liminf mu_j(B_R)>=mu(B_R), and subtracting from the convergent total masses
gives limsup mu_j(R^2\B_R)<=mu(R^2)-mu(B_R). Exhaustion proves tightness;
vague convergence plus tightness gives narrow convergence. The same argument
applies to subsequences. None of this implies |D|f_j|| -> |D|f|| narrowly.

## 3. U-tail is paid for the full signed strict sequence

We prove, with an absolute constant C_1, that EVERY real f in BV(R^2)
and R>0 satisfy

    |D(Mf)|({|x|>8R})
       <= C_1 |Df|({|x|>R}) + C_1 ||f||_1/R.                 (3.1)

The proof also gives the same estimate for

    T_t g = sup_{r>=t} A_r g,    g=|f|,                     (3.2)

provided R>=t. All quantities on the left of (3.1) are full variation
measures, not just jump parts or absolutely continuous parts.

### 3.1 Sobolev tail estimate

Let g>=0 be in W11. Fix s>0 and let theta vanish on B_s, equal one outside
B_{2s}, satisfy 0<=theta<=1 and |grad theta|<=C/s. Put h=theta g. Then

    ||grad h||_1 <= integral_{|x|>s}|grad g| + C||g||_1/s.     (3.3)

For |x|>4s, every ball centered at x of radius r<=|x|/2 lies where h=g.
If such a radius attains Mg(x), then Mh(x)=Mg(x), since h<=g. The same
equality holds at Lebesgue contact points Mg(x)=g(x), because h(x)=g(x)
and Mh(x)>=h(x). The equality-set rule for W11_loc functions therefore
charges all such points to ||grad Mh||_1, at most C||grad h||_1 by the
pinned bound. The equality-set rule for Sobolev functions follows by ACL
and the one-dimensional zero-level-set derivative rule, or by the density
argument in the source appendix.

At every remaining Lebesgue point with nonzero g, some attaining radius
r>|x|/2 exists: disk averages are continuous in r, tend to zero at infinity,
and tend to g(x) at zero. This radius is an interior radial maximizer.
For a fixed x define V(r)=integral_{B(x,r)}g and let J(r) be the integral of
the nonnegative radial trace of g on the circle. On each compact annulus,
the map r -> g(x+r omega) is W11 in r with values in L1(S^1), hence has a
continuous version there. This follows by the polar change of variables,
Fubini and the radial weak derivative grad g(x+r omega) dot omega.
Consequently J is continuous, V'=J, and integration by parts gives

    grad A_r g(x) = (pi r^2)^(-1) integral_{B(x,r)} grad g,
    |integral_B grad g| <= J(r),
    partial_r A_r g(x) = J(r)/(pi r^2)-2V(r)/(pi r^3).

The formulas first hold at almost every r and then at every positive r
using these continuous versions. Joint continuity of the ball integrals
of the L1 function grad g also gives the displayed spatial derivative at
each x,r. At the maximizing radius partial_r A_r g=0, so

    |grad Mg(x)| = |grad A_r g(x)|
       <= (2/r) A_r g(x)
       <= 16 ||g||_1/(pi |x|^3).                            (3.4)

Touching supplies the equality at differentiability points of Mg; no
derivative of a selected radius is taken. Integrating (3.4) outside B_{4s}
costs 8||g||_1/s, since integral_{|x|>4s}|x|^(-3)dx=pi/(2s).
Together with (3.3) this proves

    integral_{|x|>4s}|grad Mg|
       <= C integral_{|x|>s}|grad g| + C||g||_1/s.             (3.5)

Measurability of the partition is obtained by writing the suprema over
the continuous radius families (or rational radii and compact intervals).
One can use the entire measurable equality set {Mh=Mg} as the first set;
its complement has only large-radius optimizers, up to null sets.

For T_t, the signed-band bound and passage through the increasing dyadic
bands [t,2^N t] give

    integral |grad T_t h| <= C||grad h||_1.                  (3.6)

It is Lipschitz, so there is no singular derivative. All its optimizers
exist when h is nonzero; zero input is harmless. The same equality-set
argument works. If s>=t, any remaining optimizer r>|x|/2>2s is strictly
greater than t, so (3.4) still applies. Thus (3.5) holds for T_t g as well.

### 3.2 Passing the estimate to arbitrary BV inputs

Let g=|f| and g_epsilon=rho_epsilon*g, with a nonnegative smooth compact
probability kernel supported in B_epsilon. These functions are W11,
nonnegative, converge in L1 to g, and

    |grad g_epsilon| <= rho_epsilon*|Dg|.

Take s=2R in (3.5), epsilon<R. Tonelli and (2.1) give

    integral_{|x|>2R}|grad g_epsilon(x)| dx
       <= |Dg|({|y|>R}) <= |Df|({|y|>R}).

The maximal outputs converge locally in L1 by the already-paid argument
(or by strong L2 approximate-identity convergence for this fixed g).
Variation lower semicontinuity on the OPEN set {|x|>8R} now proves (3.1).
For T_t, uniform convergence follows from

    ||T_t g_epsilon-T_t g||_infinity
       <= ||g_epsilon-g||_1/(pi t^2),                       (3.7)

and the identical lower-passage argument proves its tail bound. Its global
variation bound <=C|Dg|(R^2) also follows this way from (3.6).
No upper semicontinuity of variation was used in this passage.

Finally the L1 norms of f_j are bounded and (2.2) makes mu_j tight.
Applying (3.1) to each f_j yields precisely

    lim_{R->infinity} limsup_j
       |D(Mf_j)|(R^2\B_R)=0.                               (U-tail)

Open versus closed spheres cause no issue: replace R by, for example,
R/2 in an upper bound. This proves U-tail with ALL quantifiers of B.
It is a technical deduction from the pinned bound and the old tail
mechanism, not a substantial-result nomination.

## 4. Fixed positive lower radii: a BV compactness argument

For every t>0, the ORIGINAL signed strict sequence satisfies

    grad T_t |f_j| -> grad T_t |f| in L1(R^2;R^2).            (4.1)

There is no assertion that |f_j| converges strictly. The mechanism uses
domination by |Df_j| and a special feature of circles, instead of assuming
strong convergence of D|f_j|.

### 4.1 Atomless measures and the circle interface

The vector measure Du of any planar BV function has no atoms. To prove
this directly, suppose a=Du({x_0}). Its distributional curl is zero.
Test that identity with epsilon phi((x-x_0)/epsilon). Its first derivatives
are bounded uniformly and supported in a shrinking ball. The non-atomic
remainder contributes a quantity tending to zero; the atom contributes

    a_2 partial_1 phi(0)-a_1 partial_2 phi(0)=0.

Arbitrary gradients of phi at zero force a=0. Since |Du|({x_0})=|a|,
the variation is atomless too.

For ANY finite atomless positive measure lambda in the plane, at most
countably many distinct circles have positive lambda mass. Distinct
circles intersect in at most two points, of zero lambda mass. Thus any
finite family of such circles is essentially disjoint, and the sum of
their masses is bounded by lambda(R^2). For each positive integer N,
only finitely many can have mass >=1/N; their union over N is countable.
In particular, the centers of all positive-mass circles form a countable
set. Outside it, lambda(partial B(x,r))=0 for EVERY r>0.

For g in BV, A_r g is globally Lipschitz with constant at most
|Dg|(R^2)/(pi r^2), by the translation bound. Its weak gradient is

    grad A_r g(y) = Dg(B(y,r))/(pi r^2) a.e. y.              (4.2)

This is the distributional convolution identity; Fubini proves it with
the indicator disk kernel. If |Dg|(partial B(x,r))=0, that right-hand
side tends to Dg(B(x,r))/(pi r^2) as y->x: the symmetric difference of
the balls lies in an annulus of thickness |y-x| whose mass tends to zero.
The bounded weak gradient then implies differentiability of A_r g at x
with this value. In detail, on a sufficiently small ball the essential
supremum of the difference of its weak gradient from that constant is
arbitrarily small; subtract the corresponding affine function and use
the Lipschitz/weak-gradient bound on that convex ball. This bounds the
first-order remainder and proves differentiability. Thus (4.2) holds
at every such x, not merely for a fixed r almost everywhere.

Write g_j=|f_j|, g=|f|, eta_j=Dg_j and eta=Dg. We have eta_j -> eta
against C_0 tests by L1 convergence, and |eta_j|<=mu_j. If r_j->r>0
and mu(partial B(x,r))=0, then

    eta_j(B(x,r_j)) -> eta(B(x,r)).                          (4.3)

To see this, approximate the fixed disk indicator from inside and outside
by continuous cutoffs whose discrepancy is supported in a thin annulus.
The error for eta_j is bounded by mu_j of that annulus. Narrow convergence
of mu_j and then the zero boundary mass make the limsup error arbitrarily
small. The moving disks lie between disks of radii r-delta and r+delta
eventually, so the same argument gives the moving-radius assertion.

### 4.2 Optimizers and global gradient convergence

Exclude the countable union of the circle-center exceptional sets for
mu and all |Dg_j|, and the null sets where the Lipschitz functions
T_t g,T_t g_j are not differentiable. At any remaining x, all disk
averages in question are differentiable at x for ALL positive radii.

If f is nonzero, T_t g(x)>0. Convergence (3.7) holds with g_j in place
of g_epsilon. Optimizing radii r_j>=t exist, and the bound
A_r g_j(x)<=||g_j||_1/(pi r^2), together with the positive limiting value,
bounds r_j above at this fixed x. Any convergent subsequence r_j->r
therefore has r>=t and attains T_t g(x), by uniform convergence of the
averages and continuity in r of A_r g(x). Touching and (4.3) give

    grad T_t g_j(x)
       = eta_j(B(x,r_j))/(pi r_j^2)
       -> eta(B(x,r))/(pi r^2)
       = grad T_t g(x).

All possible limiting optimizers give the same last gradient. The
subsequence principle proves a.e. convergence of the full sequence.
Their gradients are bounded by sup_j mu_j(R^2)/(pi t^2), so dominated
convergence proves local L1 convergence. If f=0, strictness gives
mu_j(R^2)->0, and the global signed-band bound proves (4.1) immediately.
In the nonzero case, the T_t tail bound of Section 3 and (2.2) make
these gradients uniformly tight. Combining local convergence with that
tail bound proves the global assertion (4.1).

This extends the positive-radius proof interface to the actual topology
of B. It does NOT permit sending t to zero uniformly in j.

## 5. Fine scalar cancellation budgets really do vanish under strictness

This section concerns Df_j itself, not D|f_j|. It isolates a useful source
operation that survives staircase concentration, while explaining why it
has not solved B.

For a finite vector measure h, let phi_{k,q} be the planar product tents
on mesh 2^(-k), exactly as in `eq:hat-refinement`. Write

    h_{k,q}=integral phi_{k,q} dh,
    A_k(h)=sum_q |h_{k,q}|,
    A_k^c(h)=sum_q |c(h_{k,q})|,

where c:R^2->R is a fixed linear functional. Positivity, partition of unity
and positive refinement show that A_k(h) increases to |h|(R^2), and
A_k^c(h) increases to |c(h)|(R^2). For completeness, the upper bounds
are the triangle inequality. For the reverse limit choose a continuous
compact vector test n with |n|<=1. Then

    A_k(h) >= sum_q n(q) dot h_{k,q}
            = integral (sum_q phi_{k,q}(x)n(q)) dot dh(x).

The interpolant converges uniformly to n, and the test-field variation
formula proves the claim. Scalar tests give the c version.

Strict vector-measure convergence h_j->h also implies

    |c(h_j)|(R^2) -> |c(h)|(R^2).                            (5.1)

Here is a direct proof of the specific Reshetnyak-type fact needed.
Write h_j=sigma_j |h_j| and choose n in C_c with |n|<=1 approximating
the polar sigma of h in L1(|h|). Put

    delta_j = |h_j|(R^2)-integral n dot dh_j.

These nonnegative deficits tend to the arbitrarily small corresponding
deficit for h. Since
|sigma_j-n|^2<=2(1-n dot sigma_j), Cauchy--Schwarz bounds

    integral |sigma_j-n| d|h_j|
       <= [2 |h_j|(R^2) delta_j]^(1/2).

Replacing |c(sigma_j)| by |c(n)| costs at most ||c|| times that bound.
The integral of the continuous compact function |c(n)| against |h_j|
converges by narrow convergence of the variation measures, proved as
in (2.2). Do the same for h and then improve the polar approximation.
This proves (5.1). Existence of n follows from regularity: approximate
sigma by finitely many constant unit vectors on disjoint compact sets
and give these disjoint continuous cutoff neighborhoods.

At each FIXED k, A_k(h_j)->A_k(h) and A_k^c(h_j)->A_k^c(h). The individual
tent integrals converge; tightness bounds the contribution of all tents
outside a finite set by an arbitrarily small tail. Consequently

    lim_{k->infinity} limsup_j
       ( |h_j|(R^2)-A_k(h_j) ) = 0,                        (5.2)
    lim_{k->infinity} limsup_j
       ( |c(h_j)|(R^2)-A_k^c(h_j) ) = 0.                    (5.3)

Define scalar defects at level l by one half of the increase in the
scalar absolute tent mass, exactly as in the source. Their total from
all levels l>=k is

    sum_{l>=k,q} d^c_{l,q}
       = ( |c(h_j)|(R^2)-A_k^c(h_j) )/2.                    (5.4)

This follows by finite telescoping and the limit just proved. For smooth
inputs stopped at level m, the source's terminal density defect yields
the same right side, independent of m>=k. Thus (5.3) really makes the
entire fine scalar-pairing budget small. It is not a false claim that
||Df_j-Df|| becomes small. In the monotone staircase example, the
derivative measures are mutually singular but their relevant scalar
pairing budget is zero in the interior.

This also makes the ACTUAL discounted source prices vanish at fine
observation scales. Indeed, starting its price formula at level k and
stopping the density at any level m>=k, column normalization and the
41^2 neighboring-root multiplicity give

    sum_{l=k}^m sum_Q D_Q
       <= [41^2/(1-2^(-alpha))] sum_c sum_{l=k}^m sum_q d^c_{l,q}
       = [41^2/(2(1-2^(-alpha)))]
           sum_c ( |c(h_j)|(R^2)-A_k^c(h_j) ).                (5.5)

The terminal defects are included in the equality, just as in the
source. The fixed palette is finite. Thus (5.3) sends the limsup in j
of (5.5) to zero as k->infinity, UNIFORMLY in m>=k. No endpoint price
or spatial-weight price has been erased in this algebraic assertion;
(5.5) concerns precisely the D_Q prices defined in that source.
For a BV measure, the same numerical formula uses its terminal variation
measure in place of the terminal density; the telescoping proof is
unchanged. This observation does not extend any local analytic source
estimate to nonsmooth inputs without proof.

There is a parallel precise improvement for the neighboring-direction
budget. The source proof gives at each level l, with L=12,

    sum_q a_{l,q} E_l(q) <= C(A_l(h_j)-A_{l-L}(h_j)).

This follows there by charging the squared polar disagreements to
H_{p,l}=sum_q lambda_{pq} a_{l,q}-a_{l-L,p}, using the lower bounds on
the two relevant positive refinement coefficients. Summing from l=k
to m, every positive increment A_v-A_{v-1} occurs at most L times,
and none occurs before k-L+1. Consequently

    sum_{l=k}^m sum_q a_{l,q} E_l(q)
       <= CL( |h_j|(R^2)-A_{k-L}(h_j) ).                    (5.6)

This tends to zero in the same iterated limit by (5.2). These two
refinements identify a real vanishing-defect mechanism in the strongest
source operations. They do not complete a sharp coefficient-one estimate
for the output. The source also has initial and terminal run endpoints,
spatial-weight and winning-radius operations that must be compared with
the limiting output's calibrated flux, rather than simply bounded by
another C times the input mass.

There is a precise signed obstruction to applying (5.3) to the actual
averaged input. Across a monotone transition from -1 to +1, Df_j is
positive normal-directed with mass 2, so strictness is possible; D|f_j|
has negative and positive normal masses of size 1 each, while the
limiting |f| is locally constant. At any fixed coarse mesh before
j->infinity those opposite tent masses cancel, whereas
|D|f_j||(local patch) stays near 2. Therefore the fine scalar defect
budget for h_j=D|f_j| need not vanish. This does not contradict (5.3),
whose hypothesis is strict convergence of h_j, not domination by mu_j.

Even for nonnegative sequences, (5.2)--(5.4) alone are not presented as
a proof of U-sharp: one must compare the output's signed calibrated flux,
not replace its variation by C times an input budget. This continuation
has not completed that assembly with coefficient one.

## 6. Arbitrary monotone signed flat layers: an exact model calculation

This is a one-normal-variable, translation-invariant model, not a
globally integrable planar BV input. It does not impose a profile
assumption on B. It tests the sign-crossing obstruction in Section 5
without the old symmetric-ramp restriction.

Let q:R->R be ANY bounded nondecreasing function with limits

    q(-infinity)=-A, q(+infinity)=B,    A,B>=0.

Jumps and singular continuous parts are allowed. Put h=|q| and

    k_r(s)=2/(pi r) sqrt(1-s^2/r^2)_+,
    S_t h(s)=sup_{0<r<=t}(k_r*h)(s),
    c >= (A+B)/2,      H_{t,c}=max(c,S_t h).

If B>=A, then H_{t,c} is nondecreasing and

    Var_R H_{t,c} = (B-c)_+                 for EVERY t>0. (6.1)

If A>=B, reflection makes it nonincreasing and its variation is
(A-c)_+. Hence in all cases the answer is (max(A,B)-c)_+.
For c=(A+B)/2 this is |A-B|/2, including zero when A=B.

Proof. If c>=B>=A, the conclusion is immediate from h<=B. Suppose
B>A and c<B. The case A=0 is also immediate because h=q is
nondecreasing. For A>0 choose a crossing position z separating the
nonpositive and nonnegative parts of q; if q has a zero interval,
choose any point of that interval. In the BV chain rule in one variable,

    Dh = P-N,
    P,N >=0,    P(R)=B, N(R)=A,
    supp N subset (-infinity,z], supp P subset [z,infinity).

One can obtain this explicitly by P=D(q_+) and N=-D((-q)_+).
If q jumps across zero, P and N may both have an atom at z; this is
permitted and the displayed identity remains exact. Thus no
absolute-value strictness is assumed.

Let s be a continuity point of q with q(s)>A. Then s>=z and
P([z,s])=q(s)>A. The kernel k_r is continuous, nonnegative, even and
nonincreasing in |s|. For y in [z,s], k_r(s-y)>=k_r(s-z), whereas for
y<=z the reverse inequality holds. Therefore

    (k_r*Dh)(s)
       >= k_r(s-z)(P([z,s])-N(R)) >=0                       (6.2)

for EVERY r>0; the P mass to the right of s contributes nonnegatively.
Since k_r is continuous with compact support and Dh is finite,
k_r*Dh is continuous and is the distributional derivative of k_r*h.
Each average is C1. Inequality (6.2) at the continuity points, whose
complement is countable, makes every average nondecreasing on the
right-hand region {q>A}, and its supremum retains monotonicity there.

On the left-hand region {q<=A}, for almost every y<=s we have h(y)<=A,
and for y>=s we have h(y)<=B. Evenness of k_r gives

    (k_r*h)(s) <= (A+B)/2 <= c.                             (6.3)

Thus H_{t,c}=c on that region. There is no downward mismatch at the
boundary: the averages are continuous, their values from the left
are <=c at the boundary, and their supremum on the right is
nondecreasing and at least c after taking the maximum. The limits
of H_{t,c} are c at -infinity and B at +infinity, since q(s)->B
and the zero-radius limit is h(s) at Lebesgue points. It follows
that its variation is B-c. Reflection proves the A>B case; when
A=B all h<=A<=c. This proves (6.1).

The same conclusion holds with a nonnegative even continuous unimodal
probability kernel in place of each k_r, by the same proof. No such
generality is nominated as a theorem for the campaign.

Why this matters and why it is insufficient: a genuine flat jump's
nonlocal maximal baseline is at least (A+B)/2. A constant baseline of
that size removes the valley's extra variation for EVERY monotone
signed profile, at EVERY cap size, without symmetry or absolute
continuity. But an arbitrary planar strict sequence need not have
exactly one-dimensional monotone layers on a common patch. Turning
near-alignment of derivative polars into stability of (6.1), with
varying tangential geometry and a varying positive-radius baseline,
is NOT proved here. Nor does (6.1) settle diffuse/Cantor contact
concentration or staircase approximants in smooth contact regions.

## 7. Exact unresolved step, full scope preserved

Let nu_j=|D(Mf_j)|. These measures are bounded by the pinned C estimate;
Section 3 makes them tight for every original signed strict sequence.
The entire remaining condition is

    for EVERY sequence in (B) and EVERY weak-* cluster nu of nu_j,
                      nu <= |D(Mf)|.                       (U-sharp)

Equivalently, for every nonnegative phi in C_c(R^2), prove

    limsup_j integral phi d|D(Mf_j)|
           <= integral phi d|D(Mf)|.                        (7.1)

This condition is still unpaid for arbitrary real inputs, with all
absolutely continuous, jump and Cantor concentrations included.
The fixed-positive-radius theorem (4.1) pays compactness wherever
one can restrict optimizing radii uniformly below by t>0; it does
not provide a uniform t->0 passage.

For clarity, once U-sharp is proved, B follows with no additional
condition: from each subsequence tightness gives a further subsequence
with narrow positive-measure limit nu and convergence of total masses.
Local L1 convergence and the test-field variation formula give
|D(Mf)|<=nu. U-sharp forces equality, hence convergence of total masses.
Conversely B and local L1 convergence force equality of every cluster
by the same argument. Thus, with U-tail now paid, U-sharp is genuinely
equivalent to the full remaining assertion, not a narrowed target.

One can reduce attempts at the upper passage to smooth compactly
supported approximants without assuming their derivatives converge
strongly: if an original sequence violated the upper bound, choose
u_j in C_c^infinity with ||u_j-f_j||_1<1/j,
||grad u_j||_1 within 1/j of |Df_j|, and

    |D(Mu_j)|(R^2) >= |D(Mf_j)|(R^2)-1/j.                    (7.2)

To justify simultaneous choices, first cut off each fixed BV f_j far
away (the product-rule error is <=C||f_j||_1/R and the derivative
tail tends to zero), then mollify. These are strict smooth compact
approximations of that fixed f_j. Local L1 output convergence and
global variation lower passage ensure (7.2) eventually along the
approximation. Choose the diagonal term after j is fixed. Then u_j
is itself a smooth strict sequence tending to the ORIGINAL f, and
the violation survives. This is a reduction of counterexample
search or proof obligations, not a positive answer to B with a
regularity restriction substituted.

The attempted new mechanism is therefore concrete: fine signed
polarization defects vanish by (5.2)--(5.4), positive-radius gradients
converge by (4.1), and exact monotone sign layers lose the spurious
absolute-value budget by (6.1). What is still missing is a sharp
calibrated estimate that combines these facts for arbitrary planar
vanishing-radius winners. The pinned local estimate with a constant
C, or the individual half-jump bound, cannot be cited as that estimate.
No counterexample to B has been found.

## 8. Bounded updated primary comparison

Gonzalez-Riquelme's centered one-dimensional continuity result,
[arXiv:2109.09691v1](https://arxiv.org/pdf/2109.09691v1), Theorem 1,
assumes strong W11 convergence. Proposition 12 subtracts affine
functions and controls the derivative residual; this is the already
credited technical route for A. The derivative residual is not small
for strict staircase approximants. The present budget (5.4) instead
tracks the exact signed scalar cancellations in the pinned source.
Its vanishing does not itself assemble a sharp bound for Mf_j.

Gonzalez-Riquelme--Kosz,
[arXiv:2009.05729v1](https://arxiv.org/pdf/2009.05729v1), Theorem 1,
treats the ONE-DIMENSIONAL UNCENTERED operator. Its input norm is
|f(-infinity)|+Var(f), applied to the DIFFERENCE in continuity; this
is not the strict topology. Lemma 3 uses this norm for uniform input
and maximal convergence; Proposition 8 uses ordered partitions to
recover interval variation; Lemmas 9--12 use uncentered optimizing
intervals and flatness on the contact set. None is the planar centered
strict-sequence upper passage. This paper was newly downloaded and
its exact norm/interface and selected proof operations were read.

Lahti--Weigt,
[arXiv:2510.01936v1](https://arxiv.org/pdf/2510.01936v1), Theorem 1.2
and Proposition 4.15, give individual half-jump control, with the
BV_loc regularity premise supplied here by the pinned source. Their
Theorems 1.1 and 4.14 retain the Cantor blow-up/contact hypotheses;
Remark 1.7 records singular measures with only linear blow-ups.
Their jump proof excludes small radii above upper traces and uses a
continuous positive-radius envelope. It does not bound continuous
variation accumulating at a jump along a strict sequence. Formula
(6.1) treats full model variation, but its exact flatness remains
an explicit limitation, so it does not remove this full-scope gap.
The arXiv version page checked on 2026-10-16 lists only v1.

The older fractional and optimizing-radius references and their read
limits remain in the frozen r5 contracts. No alpha=0 transfer from a
positive-order estimate is made. Search strings and primary leads are
in `search-log.md`; this bounded check is not a worldwide novelty
certificate or proof that B is a named open problem.

## 9. Checks, provenance and disposition

`checks.py` exercises arbitrary asymmetric monotone step profiles,
including jumps across zero, many plateaux, reflected profiles, and
finite Cantor-staircase profiles. Disk averages use the exact circular
cap distribution, not pixel sampling. It checks (6.2), baseline
monotonicity and endpoint variation, and tests the exact tent-refinement
budget against atomic staircases. These computations test formulas
and catch sign/topology mistakes; they are not proofs of B, the
general BV deductions, source truth or contribution substantiality.

`verify.py` first authenticates the detached root seal, both inventories,
every inventoried byte (including itself and receipts), and full file
membership. Only then does it run either checker or the frozen r5
verifier, with bytecode writing disabled, comparing stored receipts.
It never regenerates inventories, receipts or the seal. Mutation
tests use disposable copies under this owned directory and remove
them before sealing. The SHA256 of `seal.json` is detached in the
handoff; `seal.sha256` is its convenience copy, not an alternative
root of trust. No mathematical independent-review claim is attached.

All writes stayed within `strict-bv-continuity-r2/`. There were no
nested agents, shared edits, staging, commits, count changes, external
messages, publication, manuscript or formalization. The requested
handoff is an unresolved full-target research continuation. No new
acceptance or independent review is requested on these supporting
deductions alone.
