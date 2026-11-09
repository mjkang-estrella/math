# W009 independent audit: the actual three-anchor sampler

2026-10-08. Independent T3 child audit of the frozen original proposal and
parent derivation. Disposition: **the displayed algebra and sampler laws pass,
subject to the conditioning and execution qualifications below**. Verified
factoring improvement: **NONE**. No candidate experiment is selected.

The strongest concrete positive result is an executable sampler whose
acquisition probability is exactly proportional to its off-diagonal pairing
mass, together with a pointwise nondecrease of residual collision mass for a
flat residual input. The strongest supplied falsifier is also valid: the
specified distribution on `{1,2,3}` over F_7 has conditional residual drift
`-5/147`. Thus the positive squared-energy term does **not** establish universal
nonnegative drift. Reachability of that distribution is not established, and
its negative residual drift does not negate its simultaneous root absorption.

No identity proves a persistent useful correlation, a paid way to construct
one, or improved total factoring time. In particular, this audit establishes
neither the proposed `O(1/p)+O(c^2)` non-forced bound nor its failure for
reachable laws. Completed W007 growth and W008 computation reviews were not
repeated. Their scoped conclusions are supplied context, not new conclusions
of this audit.

## 1. Frozen inputs and scope

The [input manifest](W009-pinned-review-inputs.json) records SHA-256 hashes and
byte-for-byte copies of AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md,
docs/SPECIFICATION.md, the research checkpoint, and both W009 texts. The
[task brief](W009-pinned-review-brief.txt) preserves the instructions and supplied
proposal/derivation. The relevant checkpoint was read for scope; its historical
reviews were not reopened. This report refers to the frozen texts even if the
parent subsequently edits the live files.

The two mathematical source hashes are:

- Proposal, `research/hypotheses/W009.md`:
  `e2e61c7c257160a38586165cb07f6bed4dedc19523accd7b321f7317b90a3d69`.
- Derivation, `research/findings/W009-pinned-energy-law.md`:
  `9bf6c7cd3f1a172b9fed3d0bd7730c6641cd44dcc18e48292c9f7146da23b122`.

All writes belong to `research/findings/W009-pinned-review*`. No shared state,
task registry, solver, Lean, dependency, commit, publication, recursive
delegation, candidate run, reachability search, or prime sweep was performed.
The only executable mathematics was exact polynomial expansion and the single
stated F_7 certificate. No external prior-art theorem was inspected or imported;
the parent's bibliography leads remain unverified applications.

## 2. Projective algebra, fibers, and exceptional points

Fix an odd prime. For this section `a` is nonzero and
`delta=1+a*t` is nonzero. In homogeneous coordinates set

    M = [[-1,a],[t,1]],
    A(U,V)=U*(U-a*V),  B(U,V)=V*(V+t*U).

Then `M^2=delta*I`, `det(M)=-delta`, and `M` is non-scalar. Hence its
projective action `iota` is an involution. The numerator and denominator of
`F=[A:B]` have no common projective zero: if `U=0`, then `B=V^2`;
if `U=a*V`, then `B=delta*V^2`; and at infinity `A=U^2`.
This is a genuine degree-two morphism, including when `t=0`.

For `I_U=a*V-U` and `I_V=t*U+V`, direct identities give

    A(I_U,I_V)=delta*A(U,V),
    B(I_U,I_V)=delta*B(U,V).

Thus `F(iota(z))=F(z)` everywhere projectively. More decisively, for a second
point `[R:S]`,

    A(U,V)*B(R,S)-A(R,S)*B(U,V)
      =(U*S-R*V)*(U*S+R*V+t*U*R-a*V*S).

The factors express respectively equality of the two points and the relation
that they are exchanged by `iota`. Therefore every fiber on P^1(F_p) is
exactly one involution orbit. A fixed point contributes one input point, with
algebraic ramification multiplicity two; it contributes no new off-diagonal
collision. No additional rational point can join that fiber.

On an affine chart the last identity is the proposal's difference formula:

    F(z)-F(r)=(z-r)*(z+r+t*z*r-a)/((1+t*z)*(1+t*r)).

It requires both displayed denominators nonzero. The acquired incidence

    a*(z*r-y*w)+y*w*(z+r)-z*r*(y+w)=0

is equivalent to its second factor after multiplying by `y*w`. It is a
criterion for a merger of **distinct** affine non-pole inputs. It must not
replace the diagonal `z=r`, which is always a collision. The homogeneous
factorization supplies the omitted projective cases.

For a legal triple,

    t=(a-y-w)/(y*w),
    delta=(a-y)*(a-w)/(y*w),
    1+t*y=(a-y)/w,  1+t*w=(a-w)/y.

These prove all four planted identities: `0 <-> a` and `y <-> w`.
The orbits are distinct because all three anchors are distinct nonzero finite
points. If `t!=0`, then `b=iota(infinity)=-1/t` is nonzero;
`b=a` would force `delta=0`, and `b=y` or `b=w` would contradict the last
two nonzero denominators. Thus finite `b` is distinct from `0,a,y,w`.
If `t=0`, then `b=infinity` and infinity is fixed. In either case
`F(0)=0` and `F(infinity)=infinity`.

The affine fixed-point equation is `t*z^2+2*z-a=0`. For `t!=0` its
discriminant is `4*delta!=0`, so it has zero or two roots; infinity is not
fixed. For `t=0`, there is exactly one affine fixed point `a/2`, together
with infinity. Consequently the total projective fixed-point count is always
zero or two. The distinction between total and affine counts is essential.

## 3. An N-only chart protocol and its exact legal event

Assume only the stated scope `N=p*q` with distinct odd primes. Small-prime
removal is paid preprocessing. The following specifies one complete ordering
of the original checks; it does not require knowing `p`, `q`, their laws, or
their projective charts.

1. Draw three independent uniform residues modulo N, charging exact sampling.
   Evaluate the current projective circuit on all three, obtaining unimodular
   pairs `[U_i:V_i]`. Evaluation uses the homogeneous recurrence, with reductions
   modulo N. No per-stage point inversion is required.
2. Check `gcd(V_a,N)`, `gcd(V_y,N)`, `gcd(V_w,N)` in that order. For every
   check in this protocol, return a proper gcd as a factor; on gcd N retain a
   failed attempt and stop this attempt; on gcd 1 continue.
3. Now invert the unit denominators and form `a,y,w`. Check, in order,
   `gcd(a,N)`, `gcd(y,N)`, `gcd(w,N)`, `gcd(y-w,N)`.
4. Invert the known unit `y*w`, compute `t=(a-y-w)/(y*w)` modulo N, and
   check `gcd(1+a*t,N)`. On gcd 1 append this stage to the circuit.

Each pair remains unimodular at both primes: the no-basepoint proof above
applies to every previously accepted stage. There is no need to invert `t`.
In particular, `t` may be zero at one prime and nonzero at the other, and the
projective update is still valid. `b=-1/t` is an analytic local description,
not an inversion required of the N-only implementation.

Passing all checks is equivalent, componentwise, to `a,y,w` being finite,
nonzero and pairwise distinct. The last missing inequalities `a!=y,w`
are exactly what the unit `delta=(a-y)*(a-w)/(y*w)` enforces. Thus the clean
event is precisely the intersection of the two local legal events. Checking
the product `delta` can hide complementary component zeros: a full gcd need
not say that the same anchor equality holds at both primes. It is still a
failed attempt, not a claimed factor. Separately checking `a-y` and `a-w`
could expose more early factors, but that would be a separately specified,
charged check policy with a different outcome law.

Optional intermediate gcds of `U,V,U-a*V,V+t*U` can retain additional early
factor opportunities. Their order and stopping behavior must be recorded.
They cannot reject a tuple that is clean at the final stage: once zero or
infinity occurs locally it remains there. They can change which non-clean
tuples yield early factors rather than full-gcd failures.

The parent sentence that every unsuccessful draw has already paid for three
evaluations is literally valid for step 1 above, which completes all three
before chart checking. An eager implementation that stops during evaluation
may pay only a prefix. Charge its actual prefix; do not simultaneously assume
three full evaluations and free early stopping. Both implementations must
retain every failed attempt in the accounting.

## 4. Legal mass, exact reindexing, and zero-mass events

Use `z0=mu(0)`, `h=mu(infinity)` to avoid confusing the zero mass with a
coordinate. Let `nu` be the unnormalized restriction of the probability law
`mu` to F_p^*, extended by zero at 0 and infinity. Define

    s=sum nu,  v=sum nu^2,  u=sum nu^3,
    q4=sum nu^4,  q5=sum nu^5.

Inclusion-exclusion for three independent residual draws gives

    ell=sum_(a,y,w distinct) nu(a)*nu(y)*nu(w)
       =s^3-3*s*v+2*u.

This uses the original sampling law, not `nu/s`. The probability of drawing
three residual points is `s^3`; conditioning each draw into the residual
support would have already incurred a different rejection cost.

For nonzero `a` and `delta!=0`, define the ordered pairing sum

    Pi(a,t)=sum_(r in F_p^*, iota(r) in F_p^*, r!=iota(r))
                       nu(r)*nu(iota(r)).

Each size-two residual orbit contributes twice its mass product. For fixed
`a,t`, the ordered pairs in this sum are exactly the legal ordered `(y,w)`
which acquire that parameter: `w=iota(y)` rearranges to
`t*y*w=a-y-w`. Neither point can equal `a`, because `iota(a)=0`;
all other legal restrictions are present in the summation. Conversely each
legal triple yields one such ordered pair and one `t`. Consequently

    Q(a,t):=Pr[legal and acquired (a,t)]=nu(a)*Pi(a,t),
    sum_(a!=0,t:delta!=0) Q(a,t)=ell.

There is no missing factor of two. Unordered orbit sums would require one,
but both the original ordered anchor draws and Pi already count both
orientations. When `ell>0`, the conditional map law is `Q(a,t)/ell`.
The anchor marginal is in general **not** proportional just to `nu(a)`:

    sum_t Pi(a,t)=s^2-v-2*s*nu(a)+2*nu(a)^2,
    Pr[a and legal]=nu(a)*[s^2-v-2*s*nu(a)+2*nu(a)^2].

For nonnegative finite laws, `ell=0` if and only if fewer than three
distinct nonzero finite values have positive mass. In particular no local
legal triple exists over F_3. At `ell=0` there is no conditional acquired-map
law and no conditional expectation given legal. Expressions written as
`ell*E[X | legal]` must instead be defined by the legal-truncated sum
`sum_legal Pr[triple]*X(triple)`, which is zero. This is not a definition
of the undefined conditional expectation. All unnormalized formulas below
remain valid and are zero, including both absorption numerators. Any terms
with `nu(a)>0` then have `Pi(a,t)=0`.

## 5. Collision, residual drift, absorption, and forced mass

Let `c=sum_(P^1) mu^2=z0^2+h^2+v`. The orbit description proves

    c_new-c=sum_r mu(r)*mu(iota(r))-sum_(r=iota(r)) mu(r)^2.

This counts each newly merged orbit with contribution `2*mu(r)*mu(iota(r))`.
With `nu(b)=0` when `b=infinity`, the pointwise identities are

    z0_new=z0+nu(a),  h_new=h+nu(b),
    s_new=s-nu(a)-nu(b),
    c_new-c=2*z0*nu(a)+2*h*nu(b)+Pi(a,t),
    v_new-v=Pi(a,t)-nu(a)^2-nu(b)^2.

Subtracting the increments of **both** atom squares proves the last line.
It remains valid when infinity is fixed; then there is no pole absorption
term. Residual fixed points contribute their old mass square on both sides,
so no fixed-point correction may be added again to Pi.

Define `D` to be the legal-truncated residual drift. Reindexing the actual
sampler gives the parent's exact degree-five identity

    D=sum_(a,t) nu(a)*Pi(a,t)*[Pi(a,t)-nu(a)^2-nu(b)^2].

For `ell>0`, `E[v_new-v | legal]=D/ell`. For `ell=0`, `D=0`
without a conditional expectation. Similarly the degree-four increments are

    G0=(s^2-v)*v-2*s*u+2*q4,
    Ginf=sum_(a,t) nu(a)*Pi(a,t)*nu(b).

The zero-square removal numerator is

    H0=(s^2-v)*u-2*s*q4+2*q5.

For example, fixing the first anchor mass `x=nu(a)`, the ordered distinct
pair mass among the remaining support is
`(s-x)^2-(v-x^2)=s^2-v-2*s*x+2*x^2`.
Multiplying successively by `x`, `x^2`, or `x^3` and summing proves the
legal-mass, `G0`, and `H0` formulas for an arbitrary weighted support.
The infinity analogues have no such moment-only simplification supplied:
the location `b` depends on the actual involution.

One can separate the forced pair from all other residual orbits without any
oracle. For each legal tuple set

    R(a;y,w)=Pi(a,t)-2*nu(y)*nu(w) >= 0.

The positive numerator `A=sum_(a,t) nu(a)*Pi(a,t)^2` is exactly

    A=T_forced+T_other,
    T_forced=2*sum_legal nu(a)*nu(y)^2*nu(w)^2
            =2*s*(v^2-q4)-4*v*u+4*q5,
    T_other=sum_legal nu(a)*nu(y)*nu(w)*R(a;y,w).

Thus `0<=T_forced<=2*s*v^2<=2*c^2`, as claimed in the proposal when read
as an **unnormalized expected** contribution before legal conditioning.
It is not a pointwise bound on the planted orbit in every sampled triple,
nor a `2*c^2` bound on its conditional contribution `T_forced/ell`.
The forced zero orbit has already been separated as `2*z0*nu(a)` in the
full collision law; it is not an extra positive term in residual drift.
`T_other` is the precise unsolved quantity in the proposed first gate.

Growing either marked atom is not itself a factor certificate. For a fixed
CRT map, a fresh probe tested by both final-coordinate gcds has a proper
factor whenever its component labels among `{0,infinity,residual}` differ.
Its probability for these tests alone is

    1-z0_p*z0_q-h_p*h_q-s_p*s_q.

This follows from fresh CRT independence; matching labels yield gcd 1 or N.
It is a local diagnostic, not the probability of surviving training or the
complete stopped algorithm's success. Averaging over survived histories
requires their actual joint law.

## 6. Multiplicative coordinates and the exact diagonal correction

The projective map `phi_a(r)=1-a/r` sends
`0 -> infinity`, `a -> 0`, and `infinity -> 1`. Direct substitution gives

    phi_a(iota(r))=delta/phi_a(r).

Set `rho_a(x)=nu(a/(1-x))` on F_p^* with `x!=1`, and `rho_a(1)=0`.
The omitted coordinate 0 is precisely the anchor being removed. The
zero-weight coordinate 1 is the original infinity, even when `mu(infinity)`
is positive: rho represents the residual law, not the full law.
Also `phi_a(b)=delta`, including `t=0`, where both sides equal 1 and
`nu(b)=rho_a(1)=0`. Therefore

    Pi_a(delta)=sum_(x*y=delta,x!=y) rho_a(x)*rho_a(y),
    nu(b)=rho_a(delta),
    ell=sum_(a,delta!=0) nu(a)*Pi_a(delta).

The coordinate change is bijective on the relevant inputs, so ordered
multiplicities and weights are preserved. There is no normalization or
Jacobian factor for these discrete masses.

To compare with a conventional multiplicative energy, define

    r_a(delta)=sum_(x*y=delta) rho_a(x)*rho_a(y),
    d_a(delta)=sum_(x^2=delta) rho_a(x)^2.

Then `Pi_a=r_a-d_a`, and its energy is
`sum_delta (r_a-d_a)^2`, not the ordinary energy with just
`sum_x rho_a(x)^4` subtracted. There are cross terms, and two square roots
of the same delta can both carry diagonal weight. This distinction must
survive any future import of a literature bound. The current derivation's
description “with the diagonal removed” is correct with this interpretation.

For support `S` and `B={1/r:r in S}`, the transformed support is exactly

    (-a)*(B-1/a) with its zero removed.

For a flat multiplicative coset `S=lambda*H` of size `m`, every contributing
pin `a in S` in fact gives the same transformed support
`T=(1-H)\{0}`. This is a purely algebraic specialization, not a promise
about reachable laws. Write `d=s/m`,

    r_T(delta)=#{(x,y) in T^2: x*y=delta, x!=y},
    R_T=(m-1)*(m-2),
    E_off(T)=sum_delta r_T(delta)^2,
    C_T=sum_(delta in T) r_T(delta).

For `m>=3` and positive residual mass the exact specialization is

    ell=m*d^3*R_T,
    A=m*d^5*E_off(T),
    H0=m*d^5*R_T,  Hinf=m*d^5*C_T,
    E[v_new-v | legal]=d^2*(E_off(T)-R_T-C_T)/R_T.

Here `Hinf` denotes the pole-square removal numerator, not `Ginf`.
The identities follow by substituting `rho_a=d*1_T` and summing over m
pins. They identify precisely which shifted-subgroup statistic a focused
source check would need. No bound for it is imported here; no subgroup
constructor, hidden order, square-root sampler, weight selector, or
energy-evaluation oracle is supplied. Even a theorem for this flat coset
case would need its field-size hypotheses and would not automatically
apply to nonflat adaptive output laws.

## 7. The two controls and the one exact F_7 certificate

For any flat residual support S of size m with mass `d=s/m` at each point,
let K be the number of size-two involution orbits wholly inside S, and let
`epsilon=1` if finite `b` lies in S and zero otherwise. Every legal triple
has `K>=1`. The exact pointwise formula is

    v_new-v=(2*K-1-epsilon)*d^2 >= 0.

If `b` is outside S this is at least `d^2`; otherwise it can be zero.
This proves the parent's flat-law claim, including arbitrary existing
marked masses. The next residual law need not be flat: singleton orbits
carry d whereas fully paired orbits carry 2d. Reapplying the flat-law
conclusion at subsequent stages is therefore unjustified without a new
invariant. No comparison theorem for arbitrary polynomial updates is needed
or asserted in this audit.

For exactly three positive residual masses alpha,beta,gamma, each of the
six ordered legal triples has mass `alpha*beta*gamma`. Each of the three
anchor labels occurs twice, so its conditional probability is 1/3 even
when the masses differ. Finite b is outside this support; if b is infinity
its residual mass is also zero. The only residual paired orbit consists
of the other two support points. Hence, with `s=alpha+beta+gamma`,

    ell=6*alpha*beta*gamma,
    E[v_new-v | legal]=(s^2-2*v)/3,
    E[z0_new-z0 | legal]=s/3,
    E[h_new-h | legal]=0.

Every such clean update leaves exactly one positive residual atom (the merged
other two points), so its next local legal mass is zero. This is a further
exact consequence for this support class, not a reachable-state theorem;
subsequent early factor opportunities still require the stopped CRT law.

In the specified F_7 law, `mu(1)=5/7`, `mu(2)=mu(3)=1/7`, and all other
masses are zero. The two orderings of the remaining anchors give the same
map for each anchor:

- `a=1`, remaining anchors 2 and 3: `t=4`, `delta=5`, `b=5`,
  `Pi=2/49`, residual drift `-23/49`; the residual output has mass `2/7`.
- `a=2`, remaining anchors 1 and 3: `t=4`, `delta=2`, `b=5`,
  `Pi=10/49`, residual drift `9/49`; the residual output has mass `6/7`.
- `a=3`, remaining anchors 1 and 2: `t=0`, `delta=1`, `b=infinity`,
  `Pi=10/49`, residual drift `9/49`; the residual output has mass `6/7`.

Each ordered tuple has probability `5/343`; each acquired map has
unnormalized probability `10/343`, exactly `nu(a)*Pi`, and conditional
probability 1/3. Thus

    ell=30/343,
    E[v_new-v | legal]=-5/147,
    D=-50/16807,
    A=220/16807,  H0=270/16807,  Hinf=0,
    G0=10/343,  E[z0_new-z0 | legal]=1/3,  Ginf=0.

Here all residual pairing is forced: `T_other=0`. The example therefore
directly falsifies the assertion that acquisition bias or its squared
positive term must dominate absorption for every law. It supplies no
reachable-state counterexample and no factoring lower bound.

The [exact checker](W009-pinned-review-check.py) passed 20 integer polynomial
identities and the six legal triples of this one distribution. Its
[JSON certificate](W009-pinned-review-check.json) retains each map, fixed
points, pushforward law, weights, and totals. Polynomial tests of moments
use three abstract masses; the general-support proofs are the combinatorial
arguments above. No numerical field larger than F_7, initial-state search,
parameter sweep, or candidate factoring execution occurred.

For completeness, both original uniform controls also pass analytically.
For the uniform projective input, with f the total fixed-point count,

    c_new=2/(p+1)-f/(p+1)^2.

For uniform affine input, if `t!=0`, exactly one affine input is paired
with the zero-mass infinity point and f is now the affine fixed-point count:

    c_new=(2*p-1-f)/p^2.

If `t=0`, all p affine points have affine partners and only `a/2` is
affinely fixed, giving `(2*p-1)/p^2`. Thus no accepted first update has
greater collision mass than that polynomial control. These are pointwise
controls, not persistence or complete-work results. At the actual uniform
affine start the local legal probability is
`(p-1)*(p-2)*(p-3)/p^3`, not the legal probability under a uniform
projective-input diagnostic.

## 8. CRT conditioning, failed charts, and paid retries

Fix the complete current circuit/history before drawing fresh samples.
Uniform residues modulo `p*q` have independent uniform CRT components.
The two triples are therefore independent conditional on this fixed history,
and the exact joint clean probability is

    C=ell_p*ell_q.

When C is positive, conditioning on joint cleanliness gives the product
of the two locally normalized `nu(a)*Pi/ell` map laws. The local formula
`D_p` is normalized by `ell_p`, not C; its joint-clean unnormalized
contribution is `ell_q*D_p`. The same distinction applies to G0 and Ginf.
None of these is a success probability for factoring.

The complement `1-C` contains both proper-gcd successes and full-gcd
failures. Let R be the probability of an early proper factor under the
specified check/stopping policy and let J be the probability of a retained
full-gcd failure; then `C+R+J=1`. The two ell values alone do not generally
determine R or J.

For the ordered protocol in section 3 this can be made exact without a
factor oracle. For analysis only, let `j_p,j_q` denote the first failing
local check, with a special value infinity for no failure. Independent
fresh CRT sampling makes these labels independent at fixed history. Then

    C=Pr[j_p=infinity]*Pr[j_q=infinity],
    J=sum_(finite i) Pr[j_p=i]*Pr[j_q=i],
    R=Pr[j_p!=j_q]=1-C-J.

If the labels differ, the earliest failure is a zero at just one prime and
returns a proper gcd. If they agree at a finite check, that gcd is N. This
also explains why altering the check order or splitting a product check
can alter the early-factor law. These labels are proof variables, never
inputs provided to the implementation.

Now specify that a full-gcd failure leaves the circuit unchanged and retries
with independent fresh samples; a proper factor terminates the factor task,
and a clean tuple advances the stage. Put `H=C+R=1-J`.
For H positive, the number T of attempted triples until **clean or factor**
is geometric with

    E[T]=1/H,
    Pr[termination is clean]=C/H,
    Pr[termination is factor]=R/H.

If one attempted triple has mean paid cost e, including all its conditional
prefixes, then the mean cost until this termination is `e/H` by renewal.
No independence between a trial's cost and its outcome is required. If
`e_J,e_C,e_R` are the corresponding conditional mean costs, then
`e=J*e_J+C*e_C+R*e_R`, omitting zero-probability terms. When C is positive,
conditioning the actual process to end clean still gives `E[T | clean]=1/H`,
but its conditional expected work is `J*e_J/H+e_C`, not generally `e/H`.
The acquired tuple on that terminal clean attempt has the same clean-law
distribution as a single attempt conditioned clean.

The number `1/C` describes an abstract procedure that discards **every**
non-clean attempt and continues even after a proper factor, or the special
case R=0. It is not the expected stopping time of the factor-terminating
implementation when R is positive. No algorithm needs to continue after
returning a factor merely to realize a clean-chart law.

If C=0, no clean stage can be acquired: a conditional clean law is undefined.
There may still be early factors. If R is positive the stage terminates with
a factor after mean `1/R` trials; if R=0, repeat-until-clean never terminates.
A finite cap L always remains meaningful. For H positive it gives

    Pr[clean within L]=C*(1-J^L)/H,
    Pr[factor within L]=R*(1-J^L)/H,
    Pr[cap exhausted]=J^L,
    E[min(T,L)]=(1-J^L)/H.

If H=0 the cap always exhausts after L attempts. All exhausted attempts
remain charged. Rebuilding the map after failures, history-dependent check
policies, or changing the retry budget invalidates this fixed-map geometric
calculation; those choices need their own conditional recurrence. Averaging
survived histories does not justify substituting products of marginal mean
ell values or assuming the two prime histories stayed independent.

At depth j, three full evaluations cost O(j+1) modular operations with the
explicit chain; gcds, inverses, randomness, reductions, storage, and bit widths
are additional paid operations. The final-chart protocol uses a fixed number
of gcds/inversions per attempt; optional intermediate checks can add O(j+1)
gcds. All residues and parameters can be kept at O(log N) bits by modular
reduction. One probe costs O(j+1) such operations; formal degree doubling
does not make evaluation free.

The stated O(k^2) acquisition work is the baseline for one attempt at each of
k stages. Actual work sums the paid attempt costs over all retries and
restarts, and over the histories that reach each stage. Even if factoring
events were absent, the fixed-stage multiplier would be `1/C`, which can be
large or undefined; no uniform bound on it is supplied. The exact law here
is a charged acquisition description, not a complete expected-time bound.

## 9. Disposition and the next proof obligation

Accept the original homogeneous update, difference and incidence identities,
projective collision law, uniform controls, and derivation (1)–(6), with
ordered sums, both marked atoms, and legal conditioning interpreted as above.
Use unnormalized sums at ell=0. Describe the squared pairing term as an
actual sampling bias or candidate mechanism, not an established computational
advantage. Qualify the three-full-evaluation sentence by the chosen execution
order and replace any unqualified repeat-until-clean cost by the stopped
outcome law.

The constructive survivor is specific: three ordinary paid draws produce
`Q(a,t)=nu(a)*Pi(a,t)` without computing Pi, and flat residual support obeys
`Delta v=(2*K-1-epsilon)*(s/m)^2>=0` pointwise. The exact F_7 certificate
closes the attempted extension to every weighted law. Neither result resolves
the next acquired law or the useful mismatch of the two CRT components.

The next work that could change the disposition is a proof about the actual
reachable sequence: control `T_other`, both absorptions, and the joint
cost/survival law, or give a fully paid generator and a persistence argument
for a favorable family. The flat coset specialization identifies a concrete
shifted-energy expression but supplies neither such generator nor persistence.
No new experiment is authorized by these identities alone. Keep the distinct
scalar-computation direction active; no conclusion here closes it or factoring
generally.

Reproduction: run `python research/findings/W009-pinned-review-check.py` from
the project root. It writes only its owned JSON certificate. No shared code
was changed and no project/Lean suite was run under this source-and-identity
review scope. The [delivery manifest](W009-pinned-review-delivery-manifest.json)
and [SHA-256 list](W009-pinned-review-delivery.sha256) freeze all delivered
inputs, checker source, evidence, and this report.
