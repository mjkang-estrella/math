# W010 norm-selected cubic: independent algebraic review

2026-10-08. Disposition: **REVISED; exact local mechanism survives.**
Verified factoring complexity improvement: **NONE**.

Equations (1)–(6) are correct with the qualifications below. There is a stronger
survivor than the proposal states: **the actual acquired sampler has positive
expected residual-collision drift for every symmetric law with positive legal
probability**, not just flat laws. A negative raw expected-drift counterexample
therefore does not exist. Individual legal parameters can have negative drift;
an explicit symbolic example is supplied. The proposal's suggestion that root
removal can defeat the *raw expectation in (4)* should be withdrawn. If intended
only as a statement about an individual update, it is correct.

This is a local probability theorem, not a concentration-rate theorem or a
factoring bound. It does not preserve flatness or yield an early-depth envelope.
The source, proofs, and limitations are specific to W010, not imported from
W007 or W009. W008's scalar-computation branch remains separate.

## Scope and frozen evidence

The governing inputs and the complete submitted proposal were frozen before
the review. See [input manifest](W010-norm-cubic-review-inputs-manifest.json),
[frozen proposal](W010-norm-cubic-review-input-research--hypotheses--W010.md),
and [assignment record](W010-norm-cubic-review-brief.txt).
The frozen STATE is contextual; the explicit W010 assignment governs this work.
No linked historical child report or disposition was imported as mathematical
evidence. The conic count is proved below, so no external primary source was
needed or consulted. No novelty claim is made.

The [exact certificate](W010-norm-cubic-review-certificate.py) uses only standard
library integer/rational polynomial arithmetic. Its
[output](W010-norm-cubic-review-certificate-output.json) verifies displayed
identities and the one predetermined symbolic support. It contains no candidate
execution, finite-field enumeration, prime/weight search, sweep, simulation, or
asymptotic fit. The general inequalities are proved in this report, not certified
by sampling. No shared source, Lean, state, package, commit, or publication change
was made. All written paths use the assigned review prefix.

## 1. Update, anchors, symmetry, and legality

Put F_beta(T)=T^3-beta*T and Q(z,u)=z^2+z*u+u^2. Direct expansion gives

    (T-z)(T-u)(T+z+u) = T^3-Q(z,u)*T+z*u*(z+u).

Consequently, when beta=Q(z,u),

    F_beta(z)=F_beta(u)=F_beta(-z-u)=-z*u*(z+u).

This proves (2) over any commutative ring. On the stated clean chart, z, u,
z-u, and z+u are units; the common output c=-z*u*(z+u) is a unit. For odd N,
c and -c are distinct. The four values z,u,-z,-u are distinct and the two
signed pairs merge into opposite, distinct outputs. The third listed root
need not be new: -z-u=z when u=-2z, and -z-u=u when z=-2u. A third distinct
occupied fiber must not be counted automatically.

If P is monic and odd, P^3-beta*P is monic and odd, of formal degree three
times deg(P). This formal degree statement supplies no fiber-growth estimate.
Zero is absorbing even when beta is zero or a nonunit. There is no division
in the update; gcd(beta,N) is not part of this protocol.

For uniform input over F_p, an odd P has a symmetric output probability law:
the bijection x -> -x pairs the fibers of a and -a. Write nu(0)=0 and
nu(a)=mu(a) for a!=0. These are **unnormalized residual masses**; s=1-m.
Symmetry gives

    Pr(z,u!=0) = s^2,
    Pr(z=u!=0) = v,
    Pr(z=-u!=0) = v.

The last two events are disjoint for odd p. Thus ell=s^2-2v is exactly the
local legal probability, and the acquired beta law is K(beta)/ell when
ell>0. If ell=0, the support has at most one nonzero opposite pair and no
legal acquisition is available. Conditional means then have no definition.

## 2. Collision decomposition, including beta=0

For two different current outputs a,b,

    F_beta(a)-F_beta(b)=(a-b)*(a^2+a*b+b^2-beta).

Compute collision mass using **ordered** pairs. The new off-diagonal
contributions to the full mass m^2+v are exactly:

* a,b nonzero, b!=a,-a: K(beta).
* b=-a!=0: collision occurs precisely when a^2=beta. Their ordered mass is
  sum_a nu(a)nu(-a)=A(beta), not 2A(beta).
* Exactly one endpoint zero: the other satisfies a^2=beta. Both orders
  contribute 2m*B(beta).

There are no other off-diagonal pairs. The new zero mass is m'=m+B(beta).
When beta is a nonzero square, its two roots are +/-a and symmetry gives
B=2nu(a), A=2nu(a)^2, hence B^2=2A. At beta=0, the definition excludes
a=0, so A=B=0. The same holds for a nonsquare. Subtracting (m+B)^2 yields

    v'-v = K+A+2mB-(2mB+B^2) = K-A,
    m'-m = B.

This proves (3) for every beta, not merely sampled parameters. Weighting by
the unconditioned legal parameter probabilities K(beta) proves (4):

    D_v := E[1_legal*(v'-v)] = sum_beta K(beta)^2 - sum_beta K(beta)A(beta),
    D_m := E[1_legal*(m'-m)] = sum_beta K(beta)B(beta).

For beta=0 specifically, F_0(T)=T^3, there is no new root mass, and the entire
gain is K(0). If chi(-3)=-1, no nonzero legal pair has Q=0. If chi(-3)=1,
such pairs are allowed and must stay in the sampler. No singular-chart
exclusion of beta=0 is justified.

## 3. Forced energy and a universal positive-drift theorem

Define

    S := v^2-2q4 = sum_(z,u legal) nu(z)^2*nu(u)^2.

Let O range over the orbits of legal ordered pairs under interchange and
simultaneous negation. Each orbit contains exactly four distinct pairs,

    (z,u), (u,z), (-z,-u), (-u,-z),

all with the same Q and weight. Write c_O=4nu(z)nu(u). Then

    K(beta) = sum_(O: Q(O)=beta) c_O,
    sum_beta K(beta)^2 = 4S + R,
    R := sum_beta sum_(O!=O', Q(O)=Q(O')=beta) c_O*c_O' >= 0.       (7)

The inner sum in R is ordered; equivalently it is twice the unordered-orbit
sum. Thus 4S is the **exact same-orbit contribution**, not all the energy.
R includes all collisions between different sign/interchange orbits. A third
occupied cubic root can contribute to R; it was not assumed present. The
trivial bounds are 0<=R<=ell^2-4S, since sum K=ell. No stronger estimate
on the cross-orbit terms is asserted merely from fourfold symmetry.

The root-removal term admits a separate, elementary bound. Fix beta=a^2!=0.
The vertices +/-a have no legal neighbor with Q(z,u)=beta: for z=a the
equation becomes u(u+a)=0, and similarly for z=-a. On all other nonzero
vertices the symmetric legal relation Q(z,u)=beta has degree at most two,
since it is a monic quadratic equation in u. For weights w_z=nu(z),
2w_z*w_u <= w_z^2+w_u^2 gives

    K(beta) <= sum_z degree_beta(z)*nu(z)^2
            <= 2*(v-A(beta)).                                  (8)

Only square beta matter when multiplying by A. Since

    sum_beta A(beta)=v,          sum_beta A(beta)^2=2q4,

we obtain

    T := sum_beta K(beta)A(beta) <= 2v^2-4q4 = 2S.                (9)

Combining (7)–(9) proves the stronger survivor

    D_v = 4S+R-T >= 2S+R >= 0.                                 (10)

If ell>0, some legal pair has positive weight, so S>0 and D_v>0. In
particular,

    E[v'-v | legal] >= (2(v^2-2q4)+R)/(s^2-2v) > 0.             (11)

These inequalities hold for every symmetric probability law, including all
reachable W010 laws. They do not require flatness, a bound on polynomial
degree, a favorable support, or a conic equidistribution assumption. They
also explain why searching for a negative *raw expected* drift would fail.
The root penalty is at most half the fourfold forced contribution.

These inequalities have not supplied a concentration rate sufficient to pay
for acquisition.
S can approach zero when nearly all residual mass lies on a single opposite
pair; ell can also vanish. No claim such as q4=o(v^2), a lower bound on R in
terms of v alone, or independence of successive reachable laws is supplied.

At the uniform start, S=(p-1)(p-3)/p^4 is of order 1/p^2, whereas the full
sum K^2 is of order 1/p. Thus R is already much larger than the forced term
at depth zero. Merely demonstrating R>0, or even R much larger than 4S,
would not establish a new concentration advantage.

## 4. Flat support and the precise weighted counterexample

For a flat symmetric residual support of size M, each occupied point has
mass d=s/M. A sampled legal pair places its entire four-element orbit in
K(beta), so K(beta)>=4d^2. At most two support points can be square roots
of beta, so A(beta)<=2d^2. Therefore each legal update has

    v'-v >= 2d^2.

This pointwise flat-law claim is correct. M is even, and ell>0 requires
M>=4. Afterwards, an output can receive one, two, or three occupied
nonzero fibers, while an opposite root pair may disappear into zero.
The residual masses need not remain equal. The pointwise proof cannot be
iterated, although theorem (10) supplies a separate expected-drift result.

A cheap exact witness separates these notions. For **every prime p>109**,
put mass t on each of +/-3 and +/-5, mass H on each of +/-7, and zero mass
m=1-4t-2H at the origin. Take t,H>0 with 4t+2H<=1. The six different
sign/interchange orbits have the following parameters and masses:

    Q(3, 5)=49,  Q(3,-5)=19:        K=4t^2 at each;
    Q(3, 7)=79,  Q(3,-7)=37:        K=4tH at each;
    Q(5, 7)=109, Q(5,-7)=39:        K=4tH at each.

All six residues are distinct for p>109. These are all legal pairs: there
are three unordered opposite-pair choices, two sign types per choice,
and four ordered pairs per orbit. The only overlap between these parameters
and the occupied root squares {9,25,49} is beta=49. Thus

    Delta v at beta=49 = 4t^2-2H^2,
    D_v = 32t^4+56t^2*H^2 > 0.

For the fixed choice t=1/12, H=1/4, m=1/6,

    ell=7/18,       v=11/72,
    Pr(beta=49 | legal)=1/14,
    Delta v at beta=49=-7/72,      v'=1/18,
    D_v=67/2592,                  E[Delta v | legal]=67/1008.

Indeed F_49(3)=F_49(5)=-120, F_49(7)=0, with opposite images for the
negative inputs. For primes p>109, -120 is nonzero. This is one symbolic
support and one chosen mass assignment, not a numerical search.
These rational masses are not asserted to be the pushforward of uniform
F_p input, still less reachable by W010. They refute only an unrestricted
pointwise weighted-law claim. The universal expected claim has been proved
instead, so no reachability assertion is needed for that survivor.

## 5. Uniform conic count and first-step expectations

Set epsilon=chi(-3), h=chi(3), C=p-epsilon-4, D=3+h, with chi(0)=0.
The change x=2z+u is bijective in z for each u, and

    4Q(z,u)=x^2+3u^2.

Here is a self-contained count. For nonzero c, the equation
(x-y)(x+y)=c has exactly p-1 solutions, by choosing the first nonzero
factor. Since 2 is invertible, this implies

    sum_y chi(y^2-c)=-1.

For beta!=0 the conic therefore has

    sum_u [1+chi(4beta-3u^2)] = p-epsilon

points. For beta=0 it has p+(p-1)epsilon points. To impose legality when
beta!=0, remove the following disjoint sets:

    z=0 or u=0:       2(1+chi(beta));
    z=u:             1+chi(beta/3)=1+h*chi(beta);
    z=-u:            1+chi(beta).

Their intersections would be the origin, which is not on this nonzero
conic. At beta=0, all four excluded lines meet the conic only at the
origin, because p>3; remove that origin just once. It follows that

    k_0=(p-1)(1+epsilon),
    k_beta=C-D*chi(beta) for beta!=0.

The total is

    sum_beta k_beta=(p-1)(1+epsilon+C)=(p-1)(p-3),

which proves all of (5), including ell=(p-1)(p-3)/p^2. It is positive
for every p>3. Possible zero k_beta values simply mean that parameter
cannot be acquired; they are not omitted conditioning factors.

At uniform input, m=1/p, nu(a)=1/p for a!=0. For nonzero squares beta,
A=2/p^2 and B=2/p; elsewhere A=B=0. Using the equal counts of nonzero
squares and nonsquares gives

    sum K^2 = ((p-1)^2(1+epsilon)^2+(p-1)(C^2+D^2))/p^4,
    sum K A = (p-1)(C-D)/p^4,
    sum K B = (p-1)(C-D)/p^3.

Divide by ell to obtain exactly the proposed (6):

    E[Delta v | legal]
      = ((p-1)(1+epsilon)^2+C^2+D^2-C+D)/(p^2*(p-3)),
    E[Delta m | legal] = (C-D)/(p*(p-3)).

Adding the initial masses proves

    E[v_1 | legal]=2/p+O(1/p^2),
    E[m_1 | legal]=2/p+O(1/p^2).

These are **conditional expectations**, not pointwise assertions about
every acquired parameter. In fact m_1 is 3/p for an acquired nonzero square
beta and 1/p otherwise. When epsilon=1 and beta=0 is acquired,
v_1=3(p-1)/p^2. This distinction matters if the informal sentence following
(6) is used later. No first-step exponent gain follows.

## 6. Composite tape and acquisition cost

The CRT statements require **distinct** primes p,q>3. If N=p^2, the two
independent field components do not exist; square inputs need a separate
case. No all-composite algorithm is established by this semiprime analysis.

Condition on a fixed active joint state, or on its entire realized past.
Two fresh uniform residues modulo N supply independent field pairs at p
and q. Write C_p,C_q for their local legal events. All four tested residues
are units modulo N precisely on C_p intersect C_q. Hence

    Pr(clean | state)=ell_p*ell_q,
    Pr(beta_p=b,beta_q=c,clean | state)=K_p(b)*K_q(c).

For the recorded map process, update only on clean acquisition. On every
other outcome leave the map fixed; a proper gcd also records success and
terminates the actual algorithm. One may freeze the state after termination
to define all later scheduled increments as zero. Then, at an active state,

    E[Delta v_p | state]=ell_q*D_v,p,
    E[Delta m_p | state]=ell_q*D_m,p,

and conversely for q. Thus the factor in the proposal is correct. In
particular, the full stopped-and-frozen residual process has nonnegative
one-step conditional mean increment by (10). This does not say that
conditioning the ensemble on continued failure preserves its means.

Clean transitions factor **at a fixed state**. Shared no-op timing and
conditioning on survival can couple the prime histories. The proposal's
correlation warning should be read as “cannot assume independence of the
relevant history ensemble,” not “every possible clean-conditioned history
ensemble is necessarily correlated.” The statewise product law above is
valid and does not supply a full-tape factoring success probability.

Individual gcd tests preserve proper factors that a multiplied test could
hide. Zero/full gcds, proper successes, paid failures, and unstarted stages
must retain their actual statuses. If an implementation aborts on a full
gcd before performing the other specified tests, its success channels need
to be described accordingly. Adding coefficient, derivative, or beta gcds
would define a different protocol. All already-zero values remain zero
under subsequent cubic updates.

For the stated sequential circuit evaluator, a fresh sample at depth j
costs O(j+1) modular operations. Creating k accepted layers with one raw
attempt per layer costs O(k^2). More generally, with T raw attempts at
depths j_t<=k, the acquisition cost is

    O(sum_(t<=T)(j_t+1)) <= O(T*(k+1)).

Thus k **raw** stages also have an O(k^2) cap, but obtaining k **accepted**
updates after arbitrarily many paid failures has no unconditional O(k^2)
guarantee. There is no lower bound here on every factoring implementation
or on tapes that stop early with a factor. A depth-k probe and the final
fresh absorption sample each cost O(k+1), with gcd/bit costs still payable.
The final map P*(P-a) need not be odd; the symmetric laws above are for the
cubic training phase. Its new root mass is m+nu(a) when a!=0 (m when a=0),
so a fresh local sample gives expected root-mass increment v. Proper CRT
separation, probe count, and full success/cost accounting remain additional
obligations.

## 7. Literal reservoir debt

Suppose the pool stores fixed input records and every accepted update is
applied to all their current values. Let c_j be the number of distinct
current residue values. A deterministic global map cannot split a class.
The selected distinct classes z and u become equal, so c_(j+1)<=c_j-1.
Starting with M distinct values permits at most M-1 accepted updates
without replenishment. Duplicated input records only lower initial c_0.

If the stored value set is closed under negation, the four distinct classes
z,u,-z,-u undergo two disjoint mergers, with opposite nonzero outputs.
Then c_(j+1)<=c_j-2, and an accepted step always leaves a nonzero opposite
pair. A sharper signed-pool bound, when initially at least one such pair
is present, is at most floor(M/2)-1 accepted updates. This also follows
by counting nonzero opposite-pair classes: at least one disappears per
accepted update and at least one remains. An initial zero class persists;
any additional absorption only reduces capacity further. These statements
hold modulo N on the clean unit chart as well as in one field.

Updating every one of M retained records over k layers costs O(M*k)
modular operations; replenishing with a fresh input at depth k costs
O(k+1). If identical records are deduplicated, actual work may instead
depend on the evolving class count. A lazy or compressed implementation
needs its own accounting. The class-count argument closes only the stated
finite-pool scheme, not all possible acquisition algorithms.

## Disposition and next mathematical question

Accept the executable cubic update, exact sampler, all equations (1)–(6),
pointwise flat-law gain, statewise CRT no-op factors, and literal reservoir
debt with the scope qualifications above. Correct the negative-expected-
drift suggestion using theorem (10). Retain the symbolic example as a
warning against pointwise weighted monotonicity and flat-law iteration.

The strongest survivor is a **strict local expected-drift theorem for all
symmetric laws with ell>0**, hence for reachable W010 laws. This resolves
the sign of the drift, not the size or useful time scale of concentration.

The next mathematical question is quantitative: along the actually reachable,
stopped W010 process, how do S_j=v_j^2-2q4_j, the distinct-orbit energy R_j,
and the legal probabilities ell_p,j and ell_q,j evolve jointly, and do they
produce useful root/fiber mass within a paid acquisition and probe budget?
A proof may exploit the universal sign while controlling its rate; a contrary
envelope must be proved anew for this sampler. Neither a favorable arbitrary
support nor first-step conic counts settle it. No depth sweep is selected by
this review, and no factoring complexity improvement is claimed.

The [delivery manifest](W010-norm-cubic-review-manifest.json) inventories and
hashes the frozen inputs, report, assignment record, and exact certificate.
