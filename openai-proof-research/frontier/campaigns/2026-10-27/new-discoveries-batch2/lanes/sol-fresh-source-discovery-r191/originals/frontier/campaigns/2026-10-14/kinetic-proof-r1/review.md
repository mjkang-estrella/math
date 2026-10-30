# Independent proof gate — frozen kinetic-window Factory candidate

Date: 2026-10-14. **Verdict: REPAIR for the original, unchanged I340 target.**

Candidate: `../kinetic-window-factory/candidate.md`, SHA256
`7c71805a0029bf5badcdbed37355775741e7aeb2513a3fba0a9a64b1f8fd2208`,
28,868 bytes. Source truth at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
is stipulated. This is a proof review of the new deductions, not an audit of
upstream truth. No acceptance, publication, substantial-result count, external
contribution review, or full formalization is authorized by this report.

## 1. Scope and verdict

The original target is preserved: whole-space three-dimensional deterministic
hard spheres, diameter epsilon, activity mu=epsilon^(-2), the exact
grand-canonical exclusion/product-activity law including N=0, and the entire
supplied regular Boltzmann interval. The conclusion is the unsmoothed,
exactly centered finite-test-vector limit in cadlag path space with J1 and
C-tightness. No equilibrium, independent restart, short-time replacement,
periodic box, or integration of the process is substituted.

The collective time-shift argument is substantially different from giving a
redundant contact a nonexistent independent time. Its normalization and time
averaging can be made valid. I found one defect in the definition of the
extended histories: the construction drops chronology while claiming a
single all-time trajectory. A determined redundant event may then lie after
a subsequent prescribed merger. The asserted trajectory and induction are
not defined as written on that part of the enlarged domain. Section 2 below
gives a deterministic example and an exact repair by retaining a
shift-invariant chronology indicator. This is a repair to the candidate's
proof, not a counterexample to Lemma W or the gas.

With that repair, the flux-tree domination, factorials, link scaling,
Gaussian budget, and summability close at the required mu^(1-h) scale. The
final-slab history-flag extension E' is a valid consequence of H's finite
kernel identity; section 4 gives the extra details needed to make that
consequence explicit. Increment cumulants, third-moment microscopic closure,
chaining, and exact-centering transfer then close the original target.

A second required repair deletes the unqualified claim of weak convergence
for the uniform topology on all of D. J1 convergence plus C-tightness is the
correct requested theorem. The uniform metric on D is nonseparable and its
Borel sigma-field is larger; random jump times need not give random elements
of that Borel space. No such measurability assertion has been supplied.
One may instead state that every J1 Skorokhod representation with a continuous
limit converges uniformly almost surely, or simply retain J1 and C-tightness.
This issue does not affect the original target.

## 2. Required analytic repair: the extended history domain

### 2.1 A missing chronology test is real

The frozen candidate defines a redundant time by a forward ray beginning at
the preceding events of its incident lines, but only constrains the dynamic
merger times in `D`. It explicitly drops the redundant chronology tests.
Consider diameter one and collinear data, embedded in R3. All the displayed
incoming fluxes are strictly positive. Use geometric contact normal +e1;
then incoming means the relative velocity is negative. Initially the birth
velocities on lines 1,2,3,4 are -1,0,3,4. Prescribe these event slots:

1. merger C(1,2) at 1/5;
2. merger C(2,3) at 2/5;
3. redundant C(1,2), determined by the forward ray;
4. merger C(1,4) at 9/20.

At the first event put x1=0, x2=-1. After its reflection the velocities on
1,2 are 0,-1. At the second event x2=-6/5 and choose x3=-11/5; its reflection
makes the velocities on 2,3 equal to 3,-1. Consequently the relative flight
on 1,2 is r(t)=12/5-3t, and its next entering time is 7/15. This satisfies
the candidate's forward-ray lower bound 2/5. It nevertheless exceeds the
next merger time 9/20. After processing that redundant reflection the
candidate's current affine branch on line 1 is x1(t)=3t-7/5. At 9/20 this is
-1/20; choosing line 4's position to be -21/20 makes the next formal merger
incoming, with relative velocity -1.

Thus all merger times are ordered and all the local entering tests pass,
but the prescribed event order is 1/5,2/5,7/15,9/20. A single chronological
trajectory cannot have those prefix velocities. At actual chronological
time 9/20, line 1 has not yet undergone the redundant reflection; it is at
zero, not -1/20. This is not a grazing/equality issue. The strict time and
flux inequalities persist under small perturbations of the data. Scaling
all displayed positions and velocities by epsilon gives the same event
times for every positive diameter epsilon, so the unit-diameter example
is not an epsilon-size restriction. The example
identifies the domain defect without asserting that this enlarged point is
a physical gas history. Physical points already obey the missing test.

The candidate's Monte Carlo script does not test this case: its covariance
samples have no initial links, have only one redundant event, and always put
that event after every merger. It compares final velocities and the last
redundant time, not a full all-time path with an intermediate redundant event.
The successful simulations are consistent with this defect.

### 2.2 Exact replacement

For a fixed prescribed global event order, use exactly H06
`lem:sharp-merger-coordinates` on the initial forest components and the
dynamic merger forest. Each isolated line begins with a pre-first-event
affine origin and velocity v_p. An initial forest determines origin
differences by y_l; its component has one still-free common translation.
At a merger, solve the relative translation of its two previously disjoint
groups by the displayed contact equation, translating *every* already
constructed segment of the moved group. This preserves all its earlier
contacts, all its y_l, and all its computed times. Keep one free common
translation for the new group; at the end fix it by X, the pre-first-event
affine origin of the prescribed representative. The merger forest gives a
unique such solution, just as in H. Redundant contacts never solve a new
translation. This recursively defines the coordinate map on the enlarged
branch domain, with the original birth-velocity, X, y, t, omega coordinates;
it does not assert a new global change-of-variables formula there. The
original Jacobian was already taken on the physical chart before domination.

Extend every line to all real times. At each step maintain its affine
current segment, all earlier segments, and its group translation. Process the slots in order. For a
merger use its prescribed time and current incoming segments. For a redundant
slot solve the candidate's entering-flight equation. At a merger with prescribed time t_g use its current affine incoming
branches extrapolated to t_g, compute the flux, and reject if the flux is
not incoming. At a redundant slot compute the unique entering crossing at
or after the later of the two incident preceding event times, rejecting if
there is none. Declare the branch zero unless the new event time is
strictly after the preceding global slot (the first slot has lower bound
minus infinity). These tests use only coordinates already known at that
step. Thus all processed event times are strictly increasing in the
prescribed global order. Let Q_G be this chronology indicator. Retain Q_G in the
extended integrand:

    F_ext,new = F_ext * Q_G.

Equivalently, abort as soon as a newly encountered event precedes the
previous processed event. This rule uses only prefix information. Extend the
result by zero after aborting. Simultaneous and grazing physical branches
have the same null-set treatment as H; this repair introduces no new
coarea variable or Jacobian.

On the physical domain, every chronology test already holds, so
F_G <= F_ext,new and all physical contact times agree with their extended
ones. Outside that domain lifetimes, acceptance, and slab tests on redundant
contacts may still be dropped. The all-time paths now exist: the initial
segment before the first event has velocity v_p, each C-update is elastic,
and later straight segments are sewn at their actual chronological times.

The simultaneous shift preserves Q_G, since it adds the same theta to every
computed time. Induction gives the candidate's shear on X and the physical
initial-link coordinates y, with the birth-segment velocities fixed. It also
gives covariance of every event time and branch flag. The affine origins of
initial-link endpoints are shifted by -theta*v_p exactly because these are
lines born at zero in the physical chart. A birth at a positive interface
carries its own independent input; it is not a new variable on a continued
line. The fixed-theta shear has determinant one.

After extension, v_p in the input factor remains its independent
pre-first-event velocity coordinate. It need not equal the instantaneous
velocity at the fixed interface birth time on a nonphysical extended branch.
This is allowed: on the physical domain they agree, and the extension is a
positive majorant, not a new gas law. Every input position still has the form
X+d_p, and its Gaussian velocity argument is still v_p. This detail should
be stated explicitly when retaining the L1/L-infinity birth bound.

Carry Q_G through averaging (W1). It is theta invariant and at most one.
It may be dropped for the final time-volume upper bound after the discrete
flux-tree estimate. Keeping it does not reduce the desired domination or
change any discrete coefficient. Therefore this repair suffices; it does
not leave an additional unproved shrinking-window lemma.

## 3. W after the repair: complete normalization and summation audit

For fixed birth velocities, common translation, initial-link offsets,
merger times and normals, all branch choices are prefix measurable. At a
node of the discrete merger-pair tree the velocities are the same for all
choices of its next pair. All intervening redundant reflections have already
been processed, and unrealizable children have weight zero. The sum of child
fluxes is at most n_i^(3/2)*sqrt(E0), where E0 is the sum of the squared
independent pre-first-event velocities on all m lines. On the enlarged
chronological histories all m lines may be regarded as present for all time;
elastic reflections conserve their *total* energy E0. Thus every subset of
slab-i lines has energy at most E0. This proves the same one-step estimate
even if some formal events fall outside their physical line lifetimes. It
does not rely on imposing physical lifetimes again.

Iterating yields the product over slabs of
(n_i^(3/2)*sqrt(P))^(a_i) on the energy bin E0<=P. This is exactly the
argument used in H06 `eq:sharp-pair-flux`–`eq:sharp-pair-products`.
The constrained/aborted branch can only lower the child sum. Initial-link
offsets and spatial translations do not enter this upper bound.

The non-invariant factors after shifting are controlled as follows.

* Integrate the common translation X first. One input costs its spatial L1
  norm; the others cost their spatial supremum. The displacement-independent
  bound is C^m*exp(-b E0). It remains true even when formal positions are far
  outside the physical birth or observation domains.
* Each link ball is contained in its velocity cylinder. Its volume is at
  most C*epsilon^2*(tau*|u_l|+epsilon). No independent theta per link is used;
  replacing simultaneous theta membership by a product of containing sets
  is a positive upper bound. Since p<=K, the product of velocity factors is
  at most C_K*(1+E0)^(p/2). This does not introduce a power of mu.
* A component with c=1 has m-1-p dynamic mergers. Thus its activity and
  the new link volumes give

      mu^(m-h) * epsilon^(2(m-1-p)) * epsilon^(2p) = mu^(1-h).

  This verifies the crucial scale. The original epsilon^p extra initial-link
  gain is lost; connected normalization is preserved.
* Integrating the theta-window indicator costs |J|/tau. Ordered merger-time
  simplices enlarge by the factor product_i(1+a_i), bounded by (1+n)^L.
  Empty simplices contribute one, including the case with no dynamic merger.
  Redundant Q_G constraints are dropped only for this positive volume bound.
* The number of marked incident C-atoms is at most the total number of
  events, which is n+O_K(1). It adds one polynomial degree.

A fixed Gaussian budget must be chosen *before* K and the moment order.
For example absorb (1+E0)^(p/2) in exp(b E0/8), at constant C_{K,b}, and
run the velocity-volume/energy-bin argument with a fixed smaller exponent.
The remaining integration factor per ordinary birth/merger is independent
of K. A constant in the exponential atom base can change numerically from
an earlier version of the envelope calculation, but it is fixed, independent
of K and order. Enlarge L once for this fixed exponent if necessary; H05
`prop:cutoff` allows every fixed L>=L0. The full supplied T is unchanged.
No choice of L depending on K or accuracy is necessary or justified.

The candidate's phrase "base unchanged" should therefore be understood as
"no K- or order-dependent change in the per-atom base". The total estimate is

    (|J|/tau) C_K (1+n)^(d_K+L+1) (C*tau*sqrt(L))^n mu^(1-h).

H06's fresh-label denominator product_i n_i! survives. The original finite
forest exploration and C/O graph determine its coefficient before taking
this positive majorant. Neither shifting coordinates nor deleting an
indicator introduces a new labeling or a new partition. At most O_K(1)
redundant contacts, initial links, and crossing roots still cost only
polynomial choices. The energy-bin sum and Stirling/entropy step are exactly
H06's, now with the fixed reserved exponent. With C*T/sqrt(L)<1 this is
summable over sizes and the fixed number L of slabs. This proves the repaired
W uniformly in J, epsilon, and pulse placement.

## 4. Remaining proof chain

### 4.1 R2: uniform moving pulses and remainders

This is justified by H04's actual kernels, not by assuming uniformity of
constants in a theorem stated only for fixed observations. Keep two pulses
and a fixed set of at most j root labels, always ending at T. Their update
maps have uniformly bounded scalar marks, independent of s,t. Compatibility,
acceptance, and the positive forest/stopped bounds ignore the mark values.
Possible segment placements of the fixed observation list cost a fixed
polynomial in diagram size. Removing their selection restrictions bounds all
pulse locations by the same positive majorant. In the coarse regime those
polynomial factors are cutoff powers of fixed order and are absorbed by the
same complexity budget.

Consequently, for fixed required accuracy, one K works for every s,t. Choose
initial-link tail exponent D>2K+M, and choose the complexity accuracy high
enough before multiplying by mu^h, h<=j. The variation bound
exp(-c Lambda_L) beats every fixed epsilon power uniformly. The artificial
initial tails also beat every assigned power. There is no claim that an
arbitrary bounded observable has Gaussian-weighted microscopic remainders.
Only unweighted TV remainders and bounded powers of the scalar mark are used.

### 4.2 R3: E' is a kernel consequence, with no illicit two-record test

H04 `eq:autonomous-observation` explicitly permits a test of root histories.
Replace the final partial-slab root-output delta kernel by its pushforward
to the pair consisting of the usual root output and the flag
r=1{root velocity jumps in (a,b]}. This is a measurable bounded function of
the autonomous final-slab history. There are finitely many accepted
collisions under the caps. The exact finite Janossy/forest proof therefore
applies unchanged. Spectator cancellation is pointwise, fresh-label
coefficients stay mu^j/j!, and every stopped-kernel estimate multiplies a
positive integrand by a factor at most one.

Earlier slabs carry no flag: r is computed by the final output kernel using
the state at the preceding interface. One can keep all designated final-root
histories explicit in that final slab, while retaining H's canonical unmarked
one-root resummations below it. Do not absorb a flagged final singleton into
an *unmarked* final g_i and then try to recover the flag from its endpoint.
If a canonical convention instead continues a bounded number of final roots
to zero, the existing dummy-line root losses are fixed powers, absorbed by
K as in H04. Either convention is harmless for the high-complexity tail;
neither creates one record per collision.

The per-root flags factor across disjoint global components. Thus the proof
of H04 `lem:diagram-labels` still gives factorial-cumulant inversion as the
connected sum on the decorated output space. Actual decorated normalized
factorial masses remain at most one because r<=1 and N is conserved. The
partition-polynomial TV comparison in `thm:marked-expansion`(ii) is unchanged.
Its positive complexity majorants are independent of a,b and of the final
partial endpoint. There are only L possible final slab indices.

Refine each autonomous C-cluster by its complete accepted C history as in
`lem:one-root-bridge` and `lem:stopped-variation`. Its root velocity can jump
only at a displayed C-atom, so r<=N_(a,b](root). This is the exact property
used with W. This is not an endpoint test of the form z(t)!=free(z(s)), and
it is not an application of the literal additive-pulse mark theorem to a
non-additive mark. It is a separate elementary extension of the finite
root-output identity, with its hypotheses and estimates verified above.

### 4.3 R4–R6 and later steps

The factorial-to-ordinary identity has the correct block factor mu^h.
Multiplying the repaired W estimate mu^(1-h)*delta by mu^h gives
C*mu*delta. For j<=4 this gives the displayed ordinary cumulant bound of
Proposition I; using the same bound for the c1 test |y| gives its uncentered
absolute expectation estimate. Centered fourth moments are
(kappa4+3*kappa2^2)/mu^2. Relabeling arbitrary-power errors is legitimate,
including cross products with mu*delta because delta<=T.

For Count, the E' decorated factorial hierarchy is exactly the hierarchy
of the point process retaining only roots with r=1. Its factorial
moment/cumulant relation is therefore the usual one. With x=mu*alpha<=1,
all partition products are O_p(x+mu^p epsilon^P) after increasing the source
accuracy if needed. Ordinary Count^3 equals Count^(3)+3 Count^(2)+Count,
so the third-moment bound follows; no missing diagonal term is discarded.
There are O(T/alpha) subinterval pieces and the threshold is eta*sqrt(mu).
At alpha=mu^(-3/2), the union bound is

    C eta^(-3) [mu^(-1/2)+mu^3 epsilon^P],

which vanishes for P>6. Counting particles that jump rather than total
collisions is sufficient for the pathwise bounded-test estimate. Conservation
of N and E(N/mu)^p<=C give the free-flight contribution O_P(mu^(-1)).
The absolute expectation increment from I gives the centered correction
O(mu^(-1)) plus arbitrary-power error. Intervals crossing slab interfaces
split into at most two pieces; the pasted phase paths do not jump at an
interface. Collision times have no deterministic-time atoms under the
transversal absolutely continuous chart measures, and the right-continuous
convention handles endpoint intervals.

The microscopic exponent is compatible with chaining. With theta=1/8,
mu^(-1)*alpha^(-4theta)=mu^(-1/4). The finest dyadic spacing is between alpha
and 2alpha. The fourth-moment error sum costs at most
R*alpha^(-1-4theta)=R*alpha^(-3/2); the stated stronger condition
R*alpha^(-2)->0 is satisfied by epsilon^P, P>6. The coarse dyadic terms have
tail sum O(2^(-k0/2)); the microscopic modulus fills the final grid gaps.
This proves C-tightness coordinatewise and hence for every fixed finite
vector. Small individual jumps alone are never used as a tightness proof.

The global coupling and exact-centering comparison are correctly uniform
in time. The exponent is
-1+(21/20)*(21/22)=1/440. The pathwise discrepancy outside the global event
is zero, and its probability tends to zero; no fourth-moment transfer on
that exceptional event is assumed. Tightness plus H's FDD limit identifies
the unique continuous Gaussian law. These steps prove precisely the
original J1+C-tight target once the W definition is repaired.

## 5. Presentation correction and limitations

Exclusions item 11 contains a minor arithmetic error. Its displayed
second-moment union bound simplifies to T/eta^2, not T*mu^(1/2)/eta^2.
It still does not vanish, so the conclusion that this second-moment estimate
is insufficient remains correct. This does not affect the third-moment
calculation actually used in Proposition M.

The "uniform topology" sentence needs the substantive measurability repair
explained in section 1. The phrase "base unchanged" should be replaced by
the explicit fixed-Gaussian-budget argument in section 3. The E' proof should
include the decorated final-output kernel and the component-factorization
argument in section 4.2. No further quantitative cycle estimate is required
after the repaired W: cycles are bounded absolutely with the window factor,
not discarded at a qualitative rate.

This review does not establish worldwide novelty. No external literature was
opened and no companion paper was reviewed for duplication here; contribution
review remains a separate gate. It does not certify any Lean development.
The exact rational counterchart checks the identified definition defect;
it is not numerical evidence for the final theorem. The original candidate
files were read-only throughout. All review files are confined to this
review directory, with hashes and exact reading extents in provenance.json.
