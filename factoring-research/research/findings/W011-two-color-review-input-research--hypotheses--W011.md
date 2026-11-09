# W011 — retain two absorbing colors while removing training

2026-10-08. Parent constructive wave. PROVISIONAL; no improved factoring
bound. This changes the computation: a fixed, cheap map replaces quadratic
fresh-anchor acquisition, while two symmetric absorbing targets prevent
complete concentration from automatically producing only full gcds.
The W010 adaptive norm envelope does not apply to this parameter rule.

## A. A critically fixed cubic, and its exact limitation

The normalized map C(T)=(3T-T^3)/2 fixes +-1 critically and fixes 0.
It arises from the one-anchor critical cubic T^3-3a^2 T by carrying the
critical image a_new=-2a^3 and normalizing by that known unit scale.
After the initial choice, no fresh current-map evaluation is needed.
Under x=(T+1)/2 it becomes g(x)=3x^2-2x^3, with critical fixed 0,1.
This is a polynomial identity; real attraction is not finite-field evidence.

Its target-root factorization is explicit:

    g^k(x)=x^(2^k) product_(j=0)^(k-1) [3-2g^j(x)]^(2^(k-1-j)).

The distinct geometric zero count is (3^k+1)/2 in good characteristic,
not 3^k and not the multiplicity 2^k at zero. For each fixed j, the
integer polynomial 2g^j(X)-3 is Eisenstein at 3: modulo 3 its only
nonzero coefficient is the leading one, and its constant term is -3.
Consequently it is irreducible over Q. A fixed-depth prime-average
interpretation via Frobenius/Burnside would give one root on average per
such factor, not geometric-degree many roots. That interpretation needs
its precise prime-limit and exceptional-prime hypotheses independently
checked; it must not be extrapolated to k growing with p. The same
factorization for target 1 follows from g(1-x)=1-g(x).

Affine conjugates of this single map have the same local basin sizes.
They cannot provide independent new map shapes by relabeling the seed.
The following family supplies a varying shape while preserving the colors.

## B. A one-parameter odd quintic with two fixed targets

For a not in {0,1,-1}, put

    b(a)=(a+2)/(2a(a+1)^2),
    F_a(T)=(3T-T^3)/2 + b(a)*T*(1-T^2)^2.                    (1)

Everything is evaluable modulo N using additions, multiplications and one
initial unit inversion. First gcd-test a,a-1,a+1 individually, return a
proper factor, and otherwise reject any full-gcd chart. For odd N the
remaining denominator is a unit. Testing 2 handles even N beforehand.
The map is odd, fixes 0,1,-1, and has F'_a(1)=F'_a(-1)=0.
It sends a to 1 and -a to -1. The factorization to be audited is

    F_a(T)-1 = (T-1)^2 (T-a) Q_a(T) / [2a(a+1)^2],
    Q_a(T)=(a+2)T^2+(a+2)^2 T+2(a+1)^2.                   (2)

The +1 identity follows by T -> -T and oddness. a=-2 is legal and gives
b=0, reducing to C; it is not silently discarded. Other collisions among
the displayed roots must retain multiplicities. The remaining quadratic
has discriminant a(a+2)(a^2-2a-4); its roots are not granted to the code.

Three computational uses have different costs:

* FROZEN parameter: sample a uniformly modulo N once, perform the chart,
  and use the same F_a at every step. Each fresh seed walk costs O(k)
  through k iterations, with O(1) parameter acquisition. This is the
  selected screen. Critical fixed points do not imply large rational basins.
* FRESH FLAT parameter at every stage: choose a uniformly on the same unit
  chart, independently of the current value. For a non-target t!=0,
  F_a(t)=+1 is the equation b(a)=b(t), of degree at most three in a;
  F_a(t)=-1 similarly uses b(-t). Thus at most six locally legal a hit
  either target. The proposed local bound is 6/(p-3) per accepted flat
  parameter, plus all raw chart-factor outcomes in a complete protocol.
  This cheap refresh has no proposed superlinear absorption mechanism.
* IMAGE-SELECTED parameter: maintain P and choose a=P(r) from a fresh input,
  outside 0,+-1, before appending F_a. At a fixed odd local law, each update
  absorbs at least the two actual occupied fibers at +-a. If v_res sums
  squared masses outside 0,+-1, the raw locally legal target increment is
  at least 2v_res. Extra quadratic roots can add mass but are not supplied
  for free. Fresh acquisition again costs O(k^2) across k raw slots.

The frozen use is materially different from replacing an unknown sampler
by free uniform points from its current image. Only its initial parameter
and seed are uniform; their later states are correlated deterministic images.

## Two-color extraction and complete stopping law

Let P be any odd composition of these maps. For uniform x over an odd
prime field let h_p(k)=Pr[P(x) in {+1,-1}] after k steps. Odd symmetry
makes the two target probabilities h_p(k)/2 each, and h_p is nondecreasing.
For fixed maps modulo distinct p,q, test gcd(P(x)-1,N) and gcd(P(x)+1,N)
separately. The endpoint success probability is exactly

    S_end = h_p+h_q-(3/2)h_p*h_q.                           (3)

In particular S_end >= (1/2)*max(h_p,h_q). Even complete two-color
concentration at both primes gives success probability 1/2. This explicitly
removes the one-atom masking failure; it does not provide concentration.
CRT independence here is for a fixed map and fresh uniform seed only.

For a FROZEN F_a, let Delta h_p(j) be its first-hit probability at step j,
with h_p(-1)=0 and j=0 including seeds already at a target. Use gcds in
order P-1, then P+1; stop on a proper factor or a full gcd. A full gcd means
both components have reached the same absorbing color, so continuation
would not help for this frozen-target protocol. At most k map updates
are allowed. With fresh uniform CRT seed,

    S_stop(k)=1-(1-h_p(k))*(1-h_q(k))
                -(1/2) sum_(j=0)^k Delta h_p(j)*Delta h_q(j),   (4)
    E[map updates]=sum_(j=1)^k (1-h_p(j-1))*(1-h_q(j-1)).       (5)

The factor one half counts equal colors at simultaneous first hits.
Different colors at simultaneous hits yield a proper factor.
These formulas include the full-gcd failures; no success conditioning.
They do not include parameter-chart early factors, which are recorded
separately and cost work. Gcd, bit, inversion and random-bit costs remain
payable in addition to (5).

## What would change complete complexity

For the frozen candidate, a useful branch would acquire a good a with a
controlled N-only probability, and a large local basin within few steps.
With per-trial expected work A and full success probability S, independent
restarts cost A/S even if cost and success are correlated. Relative to a
sqrt(p) collision control, the necessary optimistic scale is

    [1+E(map updates)]/S_stop substantially below sqrt(p).      (6)

The left side omits gcds, setup constants and bit costs; it is an optimistic
screen, not an achieved runtime. Beating that scale would still not by
itself beat ECM or GNFS or establish an all-input theorem.

The cheap falsifier is an exact small-field basin census for prespecified
parameters, including slow and empty basins, before any larger search.
The map is fully specified and the cost saving (no fresh deep training)
is real; the unsupported piece is useful basin supply and hitting time.
The study below is diagnostic finite evidence only. It cannot prove a
basin-growth exponent or justify selecting the hidden factors as inputs.

## Fixed diagnostic preregistration

Freeze this note before running. Use standard library only, a total
60-second diagnostic wall budget starting before prime/parameter setup,
and no additional parameter tuning after results. Output all scheduled,
completed, failed and unstarted records and frozen-source/config hashes.

Field-pair sizes: b in [7,9,11,13,15]. Let p be the first prime >=2^b,
and q the next prime; exact trial division is diagnostic setup, charged
against its wall budget. Each pair represents one fixed public N=pq.
For parameter seeds 0..15, independently initialize random.Random with
integer 11000+100*b+seed and draw exactly one a=randrange(N). This choice
uses N only. Perform all three parameter gcds in order a,a-1,a+1 until a
proper factor; a full gcd does not suppress later checks. Record any
chart success or full failure. Do not resample the a for that record.
For a clean chart compute b(a) mod N and reduce the actual map at p,q.
The hidden factors are used ONLY by the local diagnostic to analyze the
map. They are never claimed as permitted candidate inputs.

For each clean map, compute its functional graph on F_p and F_q and reverse
BFS from +1 and -1 to obtain exact first-hit histograms. This O(p+q)
field-table computation is an ORACLE DIAGNOSTIC, not the candidate evaluator.
Do not count its cost as a proposed factoring implementation. Check that
the two target histograms agree by oddness. Evaluate (3)-(6) for every
k in [0,1,2,4,8,16,32,64,128,256]. Retain zero-success cases explicitly.
Include the critically fixed cubic C as one extra fixed-map control per
field pair; do not duplicate it once per seed or call it Pollard rho.

Primary rejection rule: on EACH of the two largest field pairs, at least
8 of the 16 originally scheduled parameter records must be clean and have
min_k [1+E(updates)]/[S_stop(k)*sqrt(p)] <=1/4, or the frozen-family
pilot is REJECTED for this window. Chart successes/full failures and
unstarted trials do not count toward those eight; report their actual
statuses separately. This is deliberately an optimistic oracle-depth
screen: passing only licenses independent validation and an N-only depth
schedule, never a factoring speedup claim. Also report every fixed depth,
not just the best depth. No monotone trend fit or dropped seed is allowed.
A deadline that prevents evaluation of a primary pair makes the screen
INCONCLUSIVE, not a pass or an invented zero-cost failure.

No shared solver or Lean implementation is selected by this diagnostic.
The independent mathematical reviewer separately checks (1)-(5), the cubic
Eisenstein argument and tightly focused primary prior art. Pending review
does not change the registered data or permit extending the budget.
