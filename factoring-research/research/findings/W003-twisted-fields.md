# W003 Lens A — An explicit quadratic lift and its mixed-target obstruction

2026-10-08. **UNACCEPTED: submitted symbolic construction and deductions,
pending a separate independent review.** Verified COMPLETE classical factoring
complexity improvement: **NONE**. No mathematical experiment or implementation
was executed.

The concrete realization below selects two distinct real quadratic fields from
`N,R`, tests a finite list of common relations, and decides the mixed targets
by an explicit exhaustive search with elementary exact field-root tests. It
fails for a stronger reason than missing smoothness or an unproved productive
character: **each field has a real embedding at which every permitted relation
is positive and the requested twist is negative.** Neither orientation of the
mixed target is attainable, even if the relation list is enlarged without bound.

This closes this quadratic-lift realization, not the full W003 interface or
all two-field constructions. Its only factor successes come from elementary
cases, explicitly counted gcd tests, and the directly recognizable roots
`R=j^2 mod N` in the short relation scan. Literal subset enumeration wastes
`N^(1+o(1))` work per typical balanced-semiprime trial. Removing that wasted
search using the sign certificate leaves a familiar gcd sampler with complete
expected upper bound `N_0^(1/2) poly(log N_0)`. Neither is an improvement.

## 1. Frozen scope, dependencies and evidence status

The W003 brief is unchanged, with SHA-256
`fc8f5cf42a34b020833832a56994421c183e22a8fd2e951a6cb9c6cee14ab629`.
Its exact bytes, the governing records, relevant corrected reports/dispositions
and inspected primary archives are preserved in
[W003-twisted-inputs.json](W003-twisted-inputs.json) and its named snapshot tree.
The separate [delivery manifest](W003-twisted-delivery.sha256) identifies this
submission and its adjacent evidence. No Lens B draft was read. The parent owns
shared state, task records and acceptance; none was edited here.

The read governing records are AGENTS.md, README.md, docs/SPECIFICATION.md,
RESEARCH_LOOP.md, RESEARCH_TEAM.md, current STATE and W001 synthesis. Current
W002 dispositions, not historical provisional labels, govern dependencies:

- W002 B accepts its corrected finite-list algebra and proves that its particular
  CFRAC stream can have arbitrarily large kernel with trivial productive image.
  Its original report's broader support wording is superseded by its disposition.
- W002 C accepts corrected finite algebra and accounting but closes its tensor
  and factored realizations as additive speedups. None of its conditional ECM
  success model is used here.
- H027's corrected §6 already states the sufficient root-fiber condition. Its
  disposition and root-entropy prior-art note forbid promoting that condition
  into a new generation theorem.
- H028's disposition and report separate common residues from common field
  square classes. H031's corrected report/disposition supply the localization
  caution and distinguish an actual square test from ideal parity. Their
  samplers, supply laws and trial bounds are **not** imported.

The mathematical statements newly derived below remain unaccepted. The source
inspection record is [W003-twisted-source-notes.md](W003-twisted-source-notes.md).
All evidence is symbolic reasoning or source inspection, not observed algorithm
performance, a Lean proof, or a machine refinement.

## 2. A finite N-only program and explicit field selection

For complete factorization, first handle 1, use deterministic polynomial-time
primality testing, remove powers of 2, and test perfect powers by exact integer
root searches for exponents `2,...,bit_length(N)`. A discovered `N=M^k` is
handled by recursively factoring M and restoring multiplicities. These are
paid polynomial-bit operations. Every proper factor is checked by division.
Thereafter N is odd, composite and not a perfect power, so it has at least two
distinct prime divisors; repeated prime factors are still allowed.

Put `n=bit_length(N)`. A cold trial draws exactly n independent fair bits as
the integer x. If `x>=N`, return FAIL; this rejection consumes a trial. For
`x<N`, inspect `gcd(x,N)`: return a verified proper factor, count `gcd=N` as
FAIL, and on the unit branch compute `R=x^2 mod N` in `[1,N-1]`. The outer
routine retains x. The inner routine receives only N and R. It is deterministic
here, so its independent-random-tape length is zero. All of its selection,
ordering, root choices, failure and stopping rules depend only on these inputs.

Define

    u = R+2N,
    D_1 = u^2+N,       D_2 = u^2+3N,
    f_i(T) = T^2-D_i,  K_i = Q[T]/(f_i),  alpha_i = T mod f_i.       (2.1)

This is one explicit quadratic-lift rule; it is not a claim of optimal
polynomial selection. The padding makes its termination and irreducibility
independent of any distribution of R.

For both i, `u^2<D_i<(u+1)^2`, since `3N<2u+1`. Thus both polynomials are
irreducible over Q. For `s=u^2+2N`,

    D_1 D_2 = s^2-N^2,
    (s-1)^2 < D_1 D_2 < s^2,                         (2.2)

where the first strict inequality follows from `N^2<2s-1`. Consequently
`D_1 D_2` is not a square. Two nonsquare positive integers define the same
quadratic field only if their product is a rational square, which, for an
integer, would be an integer square. The fields are therefore distinct, not
merely two defining polynomials for one field.

The degree is exactly two, and `4N^2<D_i<10N^2` for odd `N>=3`. Coefficient
bit lengths are `O(n)`. Moreover,

    D_i = R^2 mod N,   f_i(R)=0 mod N,
    gcd(D_i,N)=1,      gcd(f_i'(R),N)=gcd(2R,N)=1.      (2.3)

There is no polynomial-selection rejection loop. As executable validation,
perform integer square tests on `D_1,D_2,D_1D_2`, and check the displayed
congruences and gcds in this order. The proofs show that all pass on the
unit domain. This costs polynomial time and space. No factoring of D_i,
field discriminant, maximal order, or known divisor of N is supplied.

Irreducibility is important: applying a field-square algorithm in a reducible
quotient would be invalid. Here reducibility never occurs. If a different
selection rule produced a factorization `f=gh`, evaluations at R would need
separate gcd tests: a proper gcd is useful, gcd 1 or N is not. One could not
silently keep such an f as a field or credit every rejection as a factor. That
alternative rule is not part of (2.1).

## 3. Relations, target search and actual quadratic-root routine

The finite attempted pair list is `(a_j,b_j)=(j,1)`, `1<=j<=n`, in increasing
j order. Compute the signed integer `v_j=j^2-R` and `gcd(v_j,N)`. Return the
first verified proper factor. If the gcd is N, verify and return the already
known root `y=j mod N` to the outer routine. This is a root-recognition branch,
not success of the mixed-field target; its two trivial outer signs still fail.
If the gcd is 1, retain the original j and the two elements

    g_ij = j^2-alpha_i,
    phi_i(g_ij) = j^2-R mod N.                         (3.1)

Let h be the retained count. On an early-return prefix `0<=h<=n`; reaching
subset search means `h=n`. Nonzero field elements are automatic:
alpha_i is irrational. All retained modular images are units. Thus a product
of retained images is a unit, including the empty product. There is no
smoothness rejection and no claim that a smooth factor base has been built.
This intentionally elementary realization exposes the exact target-search
cost instead of granting a square-class basis.

Enumerate every h-bit subset mask in binary order, including zero. For each
mask recompute, by a sequential scan of retained rows, the two exact products

    Q_i = product_(selected j) (j^2-alpha_i)
        = A_i+B_i alpha_i,   A_i,B_i in Z.             (3.2)

Try the original orientation first. Test `U_1=alpha_1 Q_1` for being a square
in K_1. A root w_1 would give `z_1=w_1/alpha_1` and hence
`Q_1=alpha_1 z_1^2`. Only after this test succeeds, test `U_2=Q_2`, obtaining
`z_2=w_2`. Verify both exact identities and perform §4 recovery. If an actual
root test fails, or recovery cannot yield a valid output, continue to the
opposite orientation: test `alpha_2 Q_2` first and then `Q_1`. After both
orientations fail, advance to the next subset. Return FAIL after exhaustion.

Here is the full terminating square test, with no field-square oracle. In
`K=Q(alpha), alpha^2=D`, where D is a positive nonsquare integer, take
`U=A+B alpha` with integer A,B. A root `w=a+b alpha` must satisfy

    a^2+D b^2=A,       2ab=B.                         (3.3)

If `B=0`, test whether A is a nonnegative rational square and whether A/D is
a nonnegative rational square. The corresponding possible roots are a and
`b alpha`; verify them and choose the first in that order with nonnegative
nonzero coefficient. Zero has its usual unique zero root. If `B!=0`, compute
`E=A^2-D B^2`. A root requires E to be the square of a rational number, hence
of an integer. If E is negative or not an integer square, return NONSQUARE.
For `s=isqrt(E)`, try `t=(A+s)/2` and then `t=(A-s)/2`. For each t which is
a positive rational square, take the positive rational `a=sqrt(t)`, put
`b=B/(2a)`, and verify (3.3). Return the first verified root, or NONSQUARE.

Completeness follows from
`(a^2-D b^2)^2=E` and `a^2=(A +/- sqrt(E))/2`; with `B!=0`, a cannot vanish.
For `B=0`, (3.3) forces `a=0` or `b=0`. A rational-square test reduces its
fraction and tests numerator and denominator by exact integer square roots.
Binary-search integer square roots and schoolbook arithmetic give a
conservative `O((L+log D+1)^3)` bit bound for L-bit input coefficients.
Nonsquare determination is included. The returned root is represented by two
reduced rational numbers and checked exactly, with polynomial bit lengths.

The field roots, if any, are determined without x. No numerical real-root
approximation, external factorization primitive or unbounded enumeration of
possible roots occurs. The only exponential search is the explicitly paid
subset enumeration.

## 4. Denominator-cleared maps and recovery in both orientations

Let `A_i^ord=Z[alpha_i]`, `delta_i=f_i'(alpha_i)=2alpha_i`. Evaluation at R
is a map on this order and extends to

    A_i^ord[alpha_i^(-1),delta_i^(-1)] --> Z/NZ,        (4.1)

because both R and 2R are verified units. There is no map from all of K_i
to Z/NZ. In particular a rational coordinate denominator must not simply be
inverted modulo N.

If `w_i^2=U_i` with the integral U_i used in §3, w_i is an algebraic integer.
The usual order-multiplier fact `f_i'(alpha_i) O_(K_i) subset Z[alpha_i]`
therefore gives

    h_i=delta_i w_i in Z[alpha_i],
    h_i^2=delta_i^2 U_i.                              (4.2)

Compute h_i using exact field arithmetic, cancel rational coordinates, check
that its coefficients are integers, and verify (4.2) before reducing. This
is the same justified order multiplier used in ordinary NFS; the integrality
and invertibility conditions are part of the procedure, not free assumptions.
Stevenhagen §7 describes this multiplier; H031's corrected localization scope
is respected.

On a twisted side, `z_i=w_i/alpha_i`, so define

    zbar_i = h_i(R)/(2R^2) mod N.

On an untwisted side, `z_i=w_i`, so define

    zbar_i = h_i(R)/(2R) mod N.                        (4.3)

Both denominators are verified units. Check the reduced square equations and
gcds. A proper gcd of an image would be a verified factor; a full gcd is a
failure, never a factor. In fact on this retained-row domain all the reduced
roots must be units: their squares, times the unit R where appropriate, equal
the unit `q=Q(R)`. Thus no additional zero or nonunit success is hidden here.

For the original orientation, `R zbar_1^2=zbar_2^2=q`, and the root of R is

    y=zbar_2/zbar_1 mod N.                            (4.4)

For the opposite orientation, `zbar_1^2=R zbar_2^2=q`, and

    y=zbar_1/zbar_2 mod N.                            (4.5)

Verify `y^2=R mod N` before returning y. The outer routine computes both
`gcd(x-y,N)` and `gcd(x+y,N)`, returning only a verified proper divisor.
Changing either field-root sign changes y only by a global sign. Field
embeddings are not new random CRT signs: alpha_i is the fixed algebraic
generator with reduction R; its real embeddings are used to test feasibility,
not interchanged with the reduction map.

## 5. Decisive obstruction: the inhomogeneous target is outside the image

For any field K containing alpha and a real embedding sigma with
`sigma(alpha)<0`, every nonzero pair of rational a,b satisfies

    sigma(a^2-b^2 alpha)=a^2+b^2 |sigma(alpha)|>0.      (5.1)

All products of such elements are positive at sigma. Nonzero squares are
positive there as well. Hence

    product_j (a_j^2-b_j^2 alpha) = alpha z^2          (5.2)

is impossible. z cannot be zero because the product is nonzero. The same
argument allows repeated factors, arbitrary signed a,b, rational a,b, and
negative integer exponents: inverses of positive numbers remain positive.

Both fields (2.1) have the embedding `sigma_i^-(alpha_i)=-sqrt(D_i)`. Thus the
twisted root call in **either** orientation fails on **every** subset. The
mixed-target root completion probability is exactly zero for every admissible
N,R, independently of the row cap. The early recognizable-root branch of §3
remains separate. This is an arithmetic impossibility for
this realization, not just an absent theorem or a conjectured low probability.

More explicitly, the finite-list square-class map would be

    Phi: F_2^h --> (K_1^*/K_1^*2) x (K_2^*/K_2^*2),
    e_j |--> ([g_1j],[g_2j]).                         (5.3)

The targets are `([alpha_1],[1])` and `([1],[alpha_2])`. Real sign is a
well-defined square-class character. At the negative embedding of a twisted
field every column has sign bit 0 and its target has bit 1: the required
linear system includes `0=1`. This single explicit character certifies that
the target is outside the image. No basis for the whole square-class group
is constructed or needed for this negative certificate.

Finite-prime ideal-exponent parities alone would miss that certificate.
Even after those parities vanish, the square-root ideal need not be principal,
and a generator can differ by a nonsquare unit. Nonmaximal-order coordinates
add further complications. Actual tests in §3 decide the element square
condition including all these issues; no class-group or unit oracle is
assumed. Adding the real-sign row rejects this instance before all that work.
The size of a homogeneous kernel says nothing about this inconsistent
inhomogeneous target.

The norm interpretation gives the same obstruction: `a^2-b^2 alpha` is the
relative norm of `a+b sqrt(alpha)` from `K(sqrt(alpha))`. At a negative real
place the extension becomes complex and its nonzero norms are positive.
The target alpha is negative there and cannot be such a norm. This uses only
the displayed elementary real-place identity, not a granted norm solver.

Even adjoining common nonzero rational scalar factors to the two-field rows
does not fix the simultaneous target here: their signs at the two negative
embeddings agree, whereas a mixed target has opposite signs there. Allowing
unpaired elements, different field elements or fields where alpha has no
negative real conjugate changes the interface. This proof does **not** rule
out those choices or claim that sign pairing always forces trivial roots in
every number field.

## 6. Norm geometry and why ordinary NFS supply does not transfer

For arbitrary integers a,b in these quadratic fields,

    Norm_(K_i/Q)(a^2-b^2 alpha_i)=a^4-D_i b^4.         (6.1)

For the actual list `(j,1)`, `1<=j<=n`, and sufficiently large N, `j^4=o(N^2)`
uniformly, so `|j^4-D_i|=Theta(N^2)`. These are actual norm sizes, not just an
upper envelope. For a general box `|a|,|b|<=H`, the simple bound is
`|Norm|<=(1+D_i)H^4`. Cancellation near `a/b=D_i^(1/4)` could give smaller
values, but this trial does not obtain or credit them, and the sign obstruction
would persist even if such values were supplied.

Our arbitrary R is uniform on unit squares only after the outer unit
conditioning; it is not a chosen small NFS common root. The safe lift (2.1)
has height `Theta(N^2)` even for small R. This deliberately paid height gives
no coupling with the usual carefully selected NFS polynomial/root law. The
norm calculation closes the claimed small-norm geometry for **this** selector;
it is not a proof that every N,R-dependent selector needs large coefficients.
Nor does large norm by itself prove a small smoothness probability for a
structured sequence. No such probabilistic substitution is made here.

## 7. Complete trial work, space and success, including early gcds

Write P(n) for a fixed polynomial bound covering the chosen elementary
preprocessing. A scan multiplying (3.2) by `j^2-alpha_i` uses

    A' = j^2 A-D_i B,       B' = j^2 B-A.

Coefficient magnitude grows by at most `D_i+n^2+1` per included row. Thus
products and twisted inputs have coefficient bit length `O((h+1)n)`, at most
`O(n^2)`. Rational roots, order multipliers, exact verification and modular
evaluation all have polynomial bit lengths and costs. Sequential scans and
rewinds suffice; the subset counter has h bits. No large uncharged lookup
table, random-access oracle, square-class advice or amortized field factory
is present.

Selection/validation and all n relation gcd attempts cost polynomial time.
Recomputing a product and applying the explicit root test and possible
reconstruction for one orientation costs conservatively
`O((h+1)^3 n^3)`. There are at most `2^(h+1)` orientations. Hence the literal
finite program has

    T_trial <= P(n)+O(2^h (h+1)^3 n^3) <= 2^n poly(n),
    S_trial <= poly(n).                               (7.1)

Early returns do not pay unexecuted later work. Rejected words, full gcds and
their directly recognized root outputs, all failed subsets, exact nonsquare
tests, integer/rational operand widths
and output verification are included. Space reuses the same product and root
tapes; exponentially many masks are not retained. These are on-paper bit
bounds, not timings.

Let `U_N` be the set of unit residues x for which the ordered inner scan
returns a proper factor before any full-gcd root return. Let `J_N` be the set
of unit-square residues R for which that scan instead returns a directly
recognized root j. These are accounting sets, not supplied to the program;
`|J_N|<=n`. Write r for the number of distinct prime factors of N. The exact
one-word success probability on the continuing domain is

    sigma_N = [N-1-phi(N)+|U_N|+(2^r-2)|J_N|]/2^n.   (7.2)

There are `N-1-phi(N)` proper nonunit words, x=0 is the unique full outer gcd,
and `2^n-N` words are rejected before a gcd. Each R in J_N has `2^r` preimages;
exactly two fail the comparison with its returned j, as proved in §8. The
remaining unit words either give the direct proper gcd in U_N or fail. The
mixed-field root-completion term is zero by §5. Field-selection failures have
mass zero by §2. Formula (7.2) is not being offered as a substitute for a
useful-mass proof.

There is an exact evaluation on distinct semiprimes `N=pq` with `p,q>2n`.
For a unit x, the local sets `x=+/-j mod p` and `x=+/-j mod q` have 2n
distinct members on each side. Neither component in its set means failure.
If both components correspond to the **same** j, the inner scan returns j:
the two equal sign choices fail, and the two opposite sign choices split N.
CRT gives

    unit failures = (p-1-2n)(q-1-2n)+2n,
    sigma_N = (2n+1)(p+q-2-2n)/2^n.                 (7.3)

Different local j indices yield a proper gcd, including when an earlier row
has already returned. Both signs at both primes give 4n recognized-root
preimages, of which 2n succeed and 2n fail.
This is a symbolic count, not a tested example or an independence heuristic.
For balanced p,q tending to infinity it gives `sigma_N=Theta(n/sqrt(N))`.

With probability `(p-1-2n)(q-1-2n)/2^n`, bounded below by a positive constant
for large balanced semiprimes, all n rows are retained and no early factor
occurs. The literal program then makes `2^(n+1)` failed twisted-root calls.
Consequently its expected trial cost is `Omega(2^n)=Omega(N)`. Combining this
with (7.1), (7.3) and iid cold restarts gives expected split cost

    Omega(N^(3/2)/n) <= E T_split <= N^(3/2) poly(n)   (7.4)

on that family. The exponential factor in (7.1) is an actual cost of this
enumeration, not a lower bound on target search generally.

For any continuing composite N, let p be its smallest prime divisor. There
are `N/p-1` nonzero multiples of p below N, each with a proper gcd. Since
`p<=sqrt(N)` and `2^n<=2N`, this already gives `sigma_N=Omega(N^(-1/2))`.
Thus the literal program has the uninteresting general expected split bound
`N^(3/2) poly(n)`, without any target-success assumption. Applying it in a
factor tree, with primality and multiplicity handling, gives complete expected
bound `N_0^(3/2) poly(log N_0)` and polynomial working space. This success is
entirely paid ordinary gcd/root-recognition sampling; it is no mixed-field
relation-method achievement.

There is an immediate sound optimization with the **same** success law:
after the n gcd tests, check the real-sign certificate and return FAIL instead
of enumerating subsets. This costs only polynomial time per trial and gives
complete expected upper bound `N_0^(1/2) poly(log N_0)`. On balanced
semiprimes (7.3) requires `Theta(sqrt(N)/n)` trials, so even the lower bound
from one operation per trial has `N^(1/2-o(1))` scale. The fields can then be
deleted altogether without changing successes: the remaining operations are
`gcd(x,N)`, `gcd(j^2-x^2,N)`, and the outer comparison with a directly recognized
j. The optimized closure is a simple known search, not an improved root
constructor.

For iid trials of this fixed program, with fresh words and all cold work
charged, `E T_until_split=E T_trial/sigma_N`; cost and success need not be
independent within one trial. A fixed budget of k trials has exact success
`1-(1-sigma_N)^k` and uses kn random bits, with unused suffix bits on early
termination. Almost-sure completion and the expected bounds above do not
assert a polynomial worst-case time or a polynomial-size tape sufficient
for constant success. Restarting only the deterministic inner routine for
one fixed R repeats its same factor/root/failure output; it cannot turn a
mixed-target failure into a root.

## 8. Known root-fiber law checked at the actual interface

This section is a background audit, not the result. Write an odd continuing
N as `product_(i=1)^r p_i^e_i`. Squaring on its unit group has kernel of size
`2^r`: modulo each odd prime power, a root of unity is exactly +1 or -1.
Therefore each unit-square R has exactly `2^r` unit preimages in `[0,N-1]`.
The raw-word law gives each such preimage the same probability `2^(-n)`.

Fix R and any inner transcript, completion event and verified returned y
which depend only on N,R and independent fresh bits. Conditional on these,
x remains uniform on that fiber. Exactly two preimages are `x=+/-y mod N`.
Every other preimage gives a mixed sign across prime powers, and a proper
gcd. The useful probability is exactly `1-2^(1-r)`. Repeated prime factors
do not alter this count; a mixed gcd collects whole prime-power components.
Prime powers have r=1 and zero useful mass, which is why they were handled
by the paid preliminary branch. Even moduli were also handled first.

For a general finite independent inner tape, let a_R be its probability of
returning a proper factor and b_R its disjoint probability of returning a
verified unit root. The failure-inclusive one-word law would be

    (N-1-phi(N))/2^n
      + (2^r/2^n) sum_(R in unit squares)
            [a_R+b_R(1-2^(1-r))].                    (8.1)

Fresh randomness, acceptance and stopping restrictions are essential here.
Our actual routine has `b_R=1` exactly on J_N, from direct root recognition;
the contribution from the mixed-field construction is identically zero.
a_R is its ordered proper-gcd indicator. Thus (8.1) specializes to (7.2), not to
a conditional claim of efficient inversion. H027/Dixon already provide the
fiber reasoning, and the Rabin reduction is prior art.

## 9. Matched comparisons and disposition

Coppersmith's two/multiple-field NFS already uses separate algebraic and
character blocks, actual roots in the participating fields, and a common
modular image. Its reconstruction is a homogeneous square construction.
It does not make a prescribed mixed target reachable, and its smoothness-based
cold estimate near `L_N[1/3,1.902]` is heuristic. Stevenhagen's §§6–10 already
separate ideal parity, ideal classes, units, order denominators and extraction.
The present elementary quadratic test replaces a generic field-root procedure,
but changes neither those logical distinctions nor modular inversion cost.
[Coppersmith](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf),
[Stevenhagen](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

Lee–Venkatesan Theorem 2.1 proves square-congruence generation for their
randomized NFS law; Theorem 2.3's useful Blum-semiprime conclusion assumes
Conjecture 7.82. Section 7 and Remark 7.85 already cover the productive-character
issue and multiple fields. Neither their theorem nor conjecture transfers to
the arbitrary-R quadratic selector and paired stream here. This submission
does not dispute their law or propose another character-independence assumption.
[Primary v1, Theorems 2.1/2.3 and §7](https://arxiv.org/html/1805.08873v1).

Dixon's explicit random-square method has a proved subexponential expected
factoring bound and retains the root-fiber randomness in its proof. Even that
older rigorous complete algorithm is asymptotically better than the two power
bounds above; modern best constants are not needed to reject this realization.
Its Lemma 3 is the pertinent primary fiber argument.
[Dixon, §§2–3](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf).

For a simpler matched root-inversion comparison, the N,R-only algorithm that
tests `y=0,...,N-1` for `y^2=R mod N` always finds a root on this domain in
`O(N poly(n))` work and polynomial space. Together with the known fiber law
this is already a finite construction, not an oracle; it is not subexponential
in n. Elementary `phi(N)/N>=1/(r+1)>=1/(n+1)` follows by ordering distinct
prime factors and using `p_i>=i+1`, so its outer completion remains at most
an additional polynomial expected factor. It is a comparison only, not an
uncredited fallback in the mixed-field program. Trial division likewise gives
a familiar deterministic `sqrt(N) poly(n)` comparison to the pruned gcd search.

**Unsupported statement rejected:** these sign-paired relations can attain
one alpha-twisted square class and one untwisted class in the selected fields,
with adequate probability and retained NFS cost. Here attainability itself
is false, before smoothness, rank, roots, modular signs or restarts matter.

**Proposed disposition, pending review:** close the explicit positive-binomial
quadratic lift as a mixed-target speedup. The reusable scoped deduction is the
negative-real-embedding obstruction and its explicit paid instantiation. No
novelty is claimed for real signatures, norm positivity, field square roots,
two-field reconstruction or the root-inversion reduction.

**Next proof/test:** none selected for this realization. A larger cap, more
homogeneous nullity, repeated restarts at fixed R or a numerical search cannot
change (5.1). A changed field/element law would be new work and would need its
own paid selection and target construction; no universal impossibility is
claimed. Independent review of this submission belongs to the parent.

Only the assigned report and W003-twisted-* evidence were written. No sibling
draft, mathematical execution, solver implementation, Lean action, package
installation, shared-record edit, outside-project write, recursive delegation,
commit, publication or scheduler was used.
