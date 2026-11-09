# W006 batch collision review — accept the detector after duplicate removal

2026-10-08. Independent symbolic review of the task-supplied parent note
“W006 paid collision detector and a concentration threshold.”
**Disposition: REVISED; the repaired consumption algorithm and conditional
second-moment bound pass. Verified improvement over established factoring: NONE.**

The submitted first-full-gcd stopping rule does not find every useful collision
present in its lists. Deduplicating the first list and evaluating a formal
derivative at shared global values repairs this defect. One bounded descent
then suffices; no search through K² pairs is charged as K work. On two distinct
odd prime factors the repaired detector costs K poly(log N + log K) bit work
and finds a factor whenever any original cross-list pair has a proper norm gcd.
For independent local output laws with sign symmetry, K >= c_p^(-1/2) gives
success probability at least 1/11 conditional on acquiring the accepted lists.

This is an on-paper algorithm and probability/cost proof, not an implementation,
timing result, Lean theorem, or acceptance of a particular concentrating map.
The required gain is relative to the **complete cost per accepted output**.
The parent's squared-cost threshold is a comparison of modeled birthday
costs, not a necessary condition for factoring by other events or methods.

## 1. Scope and evidence boundary

The factoring promise throughout the recovery and end-to-end statements is

    N = p q,       3 <= p < q distinct primes,
    R = Z/NZ,      S_N = R[T]/(T²+1),       i = T mod (T²+1),
    H_N = {a+ib : a²+b² = 1 in R}.

Here n is bitlength(N), and every ring coordinate is a canonical n-bit residue.
CRT and split-field coordinates below are proof devices, never algorithm inputs.
The algorithm receives N and ordinary random bits, not p, q, group orders,
factor-dependent parameters, or a square root of -1.

Read: AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, current STATE, README and
SPECIFICATION; the W005 blindnorm disposition and its relevant sampler proof;
the W006 reflection disposition; and the provisional powered-blindnorm and
rational-map parent notes. Frozen local inputs and primary-source downloads
are in [W006-batch-review-sources](W006-batch-review-sources/), with an
[integrity manifest](W006-batch-review-sources/W006-batch-review-manifest.sha256).
STATE is a mutable coordinator checkpoint; its snapshot fixes the version
retained here, not the coordinator's subsequent state.

Task D's map audit, prime-graph evidence, execution status and partial report
were not inspected or awaited. No graph, candidate or numerical experiment
was run. This review makes no deduction from D's results or from the parent's
assertion that transitions have been saved. No shared file, registry, parent
note, solver, Lean source, commit or publication was changed. Only this report
and prefixed source snapshots were authored; no recursive delegation occurred.

## 2. Local collision identity: correct in both cases

For every odd prime ell let chi_ell = (-1|ell). Then

    |H_ell| = m_ell = ell - chi_ell.

If chi_ell = -1, S_ell is the field F_(ell²). Conjugation is the ell-power
Frobenius, and its norm has kernel of order ell+1. A difference has norm zero
if and only if the difference itself is zero.

If chi_ell = +1, the two roots of T²+1 identify S_ell with F_ell × F_ell,
with conjugation swapping factors. Norm-one elements are exactly
(t,t^(-1)), t in F_ell*. For two such elements,

    Norm((t,t^(-1)) - (s,s^(-1))) = -(t-s)²/(ts).

Since t and s are nonzero in a field, this vanishes exactly when t=s.
Thus, in either case,

    ell | Norm(x-y)  iff  x_ell = y_ell,       x,y in H_N.       (1)

Norm is multiplicative in the commutative algebra, so

    Norm(product_i (y-x_i)) = product_i Norm(y-x_i).

Modulo a prime this product vanishes exactly when at least one local match
occurs. No assertion that an arbitrary split-algebra zero-norm element is
zero is needed. It is the norm-one constraint on both endpoints that makes
(1) true.

For the stated squarefree semiprime, (1) also gives the crucial global fact

    gcd(N,Norm(x-y)) = N  iff  x = y in S_N.                   (2)

Every globally unequal pair therefore has norm gcd 1, p or q. This is the
property used in the repaired recovery, in addition to multiplicativity.

## 3. The submitted stopping rule has an existence-to-recovery gap

There are admissible lists with a useful pair that the original rule misses.
In CRT notation take a=(1,1), b=(1,-1) in H_p × H_q, and K>=2. Let every
x_i=a, put y_1=a and y_2=b. The first row has full aggregate gcd, and every
one of its K leaves has full gcd. The submitted rule terminates with failure.
But every pair (x_i,y_2) has proper gcd p. This is a symbolic family of lists;
no numerical test or factor-dependent input to the actual algorithm is used.
Such lists have positive probability even under uniform independent sampling.

This example refutes deterministic completeness of that stopping rule. It
does not prove that its average success probability is small. The parent has
not supplied a paid success proof including this loss, so its existence-only
second-moment argument cannot certify the original rule. Continuing with a
K-leaf scan at every full row would cost O(K²) in the worst case.

## 4. Actual repaired algorithm, including bounded recovery

Acquire two independent lists of K accepted outputs as specified in section 7.
All subsequent operations here are deterministic.

1. Sort canonical coordinate pairs in the x-list and retain one representative
   of each **global** value. Call the resulting set D and its size d<=K.
   Sort/merge queries with D, retaining their original indices, to mark for
   each y_j whether it is in D and, if so, its unique leaf index. This costs
   O(K log(2K)) comparisons on O(n+log K)-bit records. It makes no local test
   using an unknown prime. Retain all y occurrences.
2. Build the balanced monic product tree for

       P(X) = product_(a in D) (X-a),

   and a monic query tree for the y-list. Compute P and its formal derivative
   P'. Use remainder trees to evaluate both at all y_j. Repeated query points
   are permitted; interpolation is never used.
3. In the originally specified query order, form

       V_j = P(y_j)   if y_j is not in D,
       V_j = P'(y_j)  if y_j is in D.

   Compute g_j=gcd(N,Norm(V_j)). Skip g_j=1; return a proper g_j. At the first
   g_j=N, perform the single descent below and return its proper divisor.
   If all g_j=1, return NO_COLLISION for this trial.

The derivative identity is valid over every commutative ring:

    V_j = product_(a in D, a != y_j) (y_j-a).                 (3)

Indeed, if y_j=a_0 is in D, differentiating
P(X)=(X-a_0)Q(X) and evaluating at a_0 gives P'(a_0)=Q(a_0).
This uses no inverse and remains true when other a-a_0 are zero divisors.
Formal differentiation multiplies a coefficient by its integer index; it
does not divide by that index. Global deduplication is essential: differentiating
the original polynomial with repeated copies of a_0 would not remove them all.
An empty product, including the case D={y_j}, is 1.

For the full row y, consider a node A of the retained x-product tree with
polynomial P_A. Define its omitted-self value by

    V_A = P_A(y)   if the unique leaf y is not in A,
    V_A = P_A'(y)  if that leaf is in A.

Membership comes from the saved leaf index and the node's index interval.
These values obey V_A=V_left V_right, including nodes containing y.
At a current node with full norm gcd, evaluate the two child values by
Horner evaluation (of P_A or its derivative as appropriate) and compute
their norm gcds. Return a proper child gcd if one exists. Otherwise descend
into a child whose gcd is N, choosing the left one on a tie. There must be
such a child: two unit gcds cannot multiply to a full gcd.

The descent cannot end at a full-gcd leaf. The omitted self-leaf has value 1;
each other leaf has gcd 1, p or q by (2). Consequently it returns a proper
factor at or before leaf depth. There is no backtracking through other rows
or other branches.

The tree is balanced. Child degrees at one level sum to at most the degree
of the current node, and this degree at least halves up to rounding on the
chosen path. Thus all Horner/derivative evaluations together cost O(d) ring
operations, not O(d) per level or per query. There are at most
2 ceil(log2 d) additional gcds, with the d<=1 case requiring no full-gcd
descent. A sequential layout can scan stored levels in O(d log(2d)) coefficient
traffic if random access is unavailable; this stays within the bit envelope.
As an equally valid simpler recovery after (3), scan its at most d nonself
leaves once. That too is O(K) additional ring/gcd work and must succeed.

**Completeness for the original lists.** Any useful original pair is globally
unequal. Its x-value survives in D and its factor remains in (3) for that y.
The corresponding aggregate gcd is therefore nonunit. Every earlier nonunit
row either directly returns a proper factor or has a successful bounded
descent. Conversely, any nonunit product (3) contains a globally unequal leaf
with a nonunit, hence proper, norm gcd. Deduplication changes multiplicities,
not this existence event. It does not require the deduplicated list to be iid.

## 5. Monic trees really admit the claimed bit envelope

The ring S_N is commutative with identity and has the free R-basis 1,i. It is
not assumed to be a field, reduced for all N, or to contain FFT roots. The
following explicit construction justifies the bound independently of a field
polynomial library's interface.

Write two coefficient arrays as A+iB and C+iD. Their product is

    (AC-BD) + i(AD+BC).

Use four ordinary nonnegative integer convolutions, then reduce modulo N.
For arrays of length at most t, each convolution coefficient is at most
t(N-1)². A radix 2^b with

    b = 2n + ceil(log2(t+1)) + 1

prevents carries between coefficient slots. Packing and unpacking cost linear
work in the packed bit size; each integer operand has O(t(n+log(t+1))) bits.
Negative combinations are taken after unpacking, so no signed-digit ambiguity
arises. All stored polynomial coefficients are reduced modulo N at every step.
Fast integer multiplication therefore gives a quasi-linear polynomial
multiplication cost, with the coefficient reductions also charged. Schoolbook
integer coefficient reduction alone is sufficient for a K poly(n+log K) bound;
schoolbook polynomial multiplication is not.

Division by a monic polynomial needs no arbitrary coefficient inverse.
Reverse its coefficient order to obtain U(X) with U(0)=1. Start G=1 and double
the precision using

    G_new = G(2-U G) mod X^(2s),
    1-U G_new = (1-U G)² mod X^(2s).

This is a polynomial identity over S_N, not division by 2. Reversed dividend
times the truncated inverse gives the quotient; subtraction gives the remainder.
This works even when differences of evaluation nodes are nonunits or zero.
The remainder-tree divisors are monic even though remainders need not be.

For clarity, put w=n+ceil(log2(K+1))+O(1), and let M_Z(L) be a monotone
fast integer multiplication envelope with M_Z(L)/L nondecreasing. A deliberately
conservative multiplication envelope for length t<=O(K) arrays is

    M_S(t) = O(M_Z(t w) + t w²).

Newton doubling, balanced multiplication and remainder-tree sweeps give
O(M_S(K) log(2K)) bit work for a constant number of trees/evaluations. Add
O(K poly(n+log K)) for sorting, norms, K gcds, formal derivatives, the one
recovery, counters and final divisor verification. Hence

    T_det(K,N) = K poly(n+log K).                            (4)

Full stored coefficient trees use O(K n log(2K)) bits; multiplication scratch,
record indices and sorting add O(K(n+log K)) bits under a linear-space fast
integer multiplier. A conservative K poly(n+log K) space envelope is sufficient
as well. These are batch-space bounds, not the sampler's streaming-space bound.
Map setup, parameters, evaluation and workspace are additional.

This ring scope is directly supported by Bostan–Gaudry–Schost: Lemma 3 treats
(Z/NZ)[T]/P for monic P, and Lemma 4(4) gives bit-cost multipoint evaluation;
the appendix tracks product/remainder trees on tapes. The interpolation and
special progression algorithms have extra unit hypotheses, which are not
being imported here. [Primary paper, Lemmas 3–4 and appendix](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf).

## 6. Exact laws and a constant-probability birthday proof

Fix the entire local algebraic schedule before drawing fresh inputs. Assume
its successful domain is A_p × A_q under H_N=H_p × H_q and its output is
(F_p(h_p),F_q(h_q)) in H_p × H_q. Uniform accepted W005 inputs have independent
uniform CRT coordinates. Conditioning on h_p in A_p and h_q in A_q preserves
that product law. Independent raw tapes for every input then give iid samples
from mu=mu_p × mu_q, with the two lists mutually independent.

For ell=p,q write s_ell=|A_ell|>0, sigma_ell=s_ell/m_ell and
b_(ell,z)=|{h in A_ell:F_ell(h)=z}|. The **conditional accepted** quantities are

    mu_ell(z) = b_(ell,z)/s_ell,
    c_ell = sum_z mu_ell(z)²,
    t_ell = sum_z mu_ell(z)³.                                (5)

Only with full survival may the denominator in c_ell be m_ell². If fibers are
normalized by m_ell after discarding failed inputs, their squared sum instead
equals sigma_ell² c_ell. It must not be substituted for c_ell and then charged
for survival a second time.

If A_ell is invariant under h -> -h and F_ell(-h)=-F_ell(h), the output atoms
at z and -z have equal masses. There is no fixed point of negation on H_ell:
2z=0 would force z=0, whose norm is not 1. Thus

    max_z mu_ell(z) <= 1/2,       1/m_ell <= c_ell <= 1/2.     (6)

The same conclusion applies if this symmetry of the output law is established
by some other argument. In particular, input-map equivariance and output-law
invariance are different assertions; the birthday proof only needs the latter.
One also has, without requiring symmetry,

    c_ell² <= t_ell <= c_ell^(3/2).

The upper bound follows from max mu_ell <= sqrt(c_ell); the lower bound is
the variance inequality for mu_ell(X), X distributed as mu_ell. Symmetry also
gives t_ell <= c_ell/2.

**Independence qualification.** Sign symmetry alone does not imply CRT
independence. Nor does an arbitrary sign-invariant survival predicate: it
could couple the two local components. Global data-dependent branching or
conditioning on the absence of other early factor events requires a fresh
joint-law argument. A fixed componentwise algebraic schedule with unit-domain
survival has the needed product property. A public random schedule shared by
all samples is handled by conditioning on that schedule; do not substitute
averaged c-values into a conditional theorem without further analysis.

For one independent pair, the proper-collision probability is exactly

    rho = c_p(1-c_q) + c_q(1-c_p).                           (7)

Without CRT independence, the exact formula is c_p+c_q-2 c_N, where c_N is
the collision probability of the full joint output law. Factoring c_N into
c_p c_q requires the product-law hypothesis.

Here is a complete second-moment calculation under that hypothesis. Set

    I_ij = 1[x_i,p=y_j,p and x_i,q != y_j,q],
    Z = sum_(1<=i,j<=K) I_ij,
    a = c_p(1-c_q),       b = t_p(1-2c_q+t_q).

Then E Z=K²a. For two different edges sharing one endpoint, their joint
probability is b: condition on that endpoint and sum
mu_p(z)³ times sum_w mu_q(w)(1-mu_q(w))². This covers either orientation
of the common endpoint. Disjoint edges depend on disjoint independent samples.
Counting ordered pairs of edges gives the exact identity

    E Z² = K² a + 2K²(K-1)b + K²(K-1)² a².                  (8)

Since a>=c_p/2 and b<=t_p<=c_p^(3/2), with u=K sqrt(c_p),

    E Z² / (E Z)² <= 1 + 2/u² + 8/u.

Cauchy–Schwarz on Z and 1[Z>0] now gives

    Pr[Z>0] >= 1/(1+2/u²+8/u) >= 1/11  whenever u>=1.       (9)

All these useful pairs remain detectable after the deterministic deduplication
and omitted-self transformation. Section 4 therefore turns (9) into actual
factor success, not just existence. No asymptotic uniformity, Poisson model,
random functional graph, or unseen collision reporter is used.

One may exchange p and q. Let c_*=max(c_p,c_q). The sufficient accepted-list
size is ceil(c_*^(-1/2)). Conversely, (6)–(7) give

    c_* <= rho <= 2c_*,
    Pr[any useful cross-list pair] <= K² rho <= 2K² c_*.

Thus constant success by this pair-consumption event needs
K=Omega(c_*^(-1/2)) and is achieved at that scale. This is a tight **sample
scale for this event**, not a lower bound on map evaluation, early gcd
extraction, another factoring algorithm, or available shared computation.

## 7. Paid acquisition, exhaustion and the semiprime control

An invocation of the accepted capped W005 sampler returns a uniform h on its
certificate branch, a proper factor, or exhaustion. Denote its certificate
probability by r=C_B, not by 1. Let sigma=sigma_p sigma_q>0 be survival through
the specified componentwise map, conditional on such a certificate. A complete
pipeline attempt accepts an output with probability r sigma.

The actual driver returns any verified early factor immediately. Otherwise
it refills exhausted or rejected inputs using fresh independent attempts until
it has 2K accepted outputs, or reaches an explicitly chosen attempt cap.
It does not require every one of exactly 2K raw attempts to succeed: that
different rule would introduce an (r sigma)^(2K) loss.

For proof only, couple this driver to a virtual process which ignores early
factor returns. Sampler noncertificate branches and map domain failures restart
the input. If an optional factor test fires on an otherwise defined trajectory,
the virtual process ignores that test and continues the **same** trajectory;
it must not reject an input merely because that optional test succeeded.
That process produces iid accepted outputs with precisely the law in section 6;
the real process succeeds earlier whenever an ignored factor would have been
returned. There is no need to assume that the law conditioned on “no early
factors anywhere” remains a product law. The virtual continuation must be
specified and bounded; the fixed evaluator assumed here supplies it.

Let a pipeline attempt have finite mean bit work W, including the capped
sampler, map failures, denominator tests, raw bits and bookkeeping. If A_k
denotes its mean work per accepted output in that virtual process, the renewal
equation gives exactly

    A_k = W/(r sigma).

This does not assume cost and acceptance are independent. With W_s bounding
one sampler invocation and B_k bounding one full map evaluation conditional
on reaching it, a useful conservative bound is

    A_k <= (W_s + r B_k)/(r sigma)
         = (W_s/r + B_k)/sigma.                             (10)

Generating the two lists costs at most 2K A_k in expectation. The real driver
can only stop earlier on a factor. Setup and actual evaluation on rejected
inputs are charged; variable-time rejections can make (10) a loose upper bound.
With fresh trials and (9), repeated fixed-K trials have finite expected total
work O(K A_k+T_det(K,N)), with the constant success factor included. Correlation
between a trial's work and outcome does not invalidate the renewal equation.

For a genuinely bounded trial, suppose a computable lower bound s_0<=r sigma
is available. Cap the number of pipeline attempts at

    L = ceil(44K/s_0).

In the virtual process the expected number needed for 2K acceptances is
2K/(r sigma)<=2K/s_0. Markov's inequality bounds cap exhaustion by 1/22.
Subtracting this event from (9) yields actual success at least 1/22, including
all rejected attempts and all cap failures. This subtraction avoids asserting
unbiasedness after conditioning on completion before the cap. The worst-case
trial cost is L times the bounded attempt cost plus (4). An unknown sigma
cannot be used as advice to set L. With no positive survival theorem, the
transformed end-to-end factoring bound remains conditional.

**Uniform control.** Set F to the identity, so sigma=1 and c_ell=1/m_ell.
The W005 unit-pair sampler alone works for every odd N; its later norm-5R
wrapper is not needed to produce h. Alternatively gcd(N,5) may be checked
first if retaining that wrapper's original domain convention. For the present
semiprime promise its pair unit probability satisfies

    alpha = product_(ell=p,q) (1-1/ell)(1-chi_ell/ell)
          >= (2/3)^4 = 16/81.

The coordinate-entry probability of W005's capped sampler is at least
(15/16)², so already a certificate on its first pair attempt gives
r >= (15/16)²(16/81) > 1/8. Taking s_0=1/8 therefore gives a fully bounded
uniform trial using at most 352K sampler invocations and polynomial bit
work per invocation. For K>=sqrt(m_p), its actual success is at least 1/22.

An explicit N-only schedule resolves the unknown p. Double K from 1, doing
64 independent bounded trials at each size. Stop increasing at the first
power of two K_max with

    K_max² >= ceil(sqrt(N)) + 1;

then repeat 64-trial blocks at that size until a factor is returned. Integer
square-root arithmetic implements the cap without p. It satisfies
K_max>=sqrt(m_p) and K_max=O(N^(1/4)). Once K>=sqrt(m_p), failure of a block
is at most (21/22)^64 < 1/4. Work increases by at most its geometric K factor
times one common polynomial in n. Summing the resulting geometric tail proves

    expected bit work = O(sqrt(p) poly(log N)),
    worst-case working space <= N^(1/4) poly(log N).          (11)

The expectation in (11) includes acquisition, failures, recovery, repeats and
the unknown-factor schedule. It is a Las Vegas splitter under the promised
two-distinct-odd-prime domain, with unbounded possible repetition count. It is
not a deterministic time bound or a new complete all-composite factorization
theorem. The balanced-semiprime specialization is N^(1/4) polylog N, the
established birthday/product-tree scale.

Do not extend the recovery theorem by citing the sampler's prime-power law.
For example, in S_(p²), x=1 and y=1+ip are distinct norm-one elements, yet
Norm(y-x)=p²=0 modulo p². Thus a globally unequal leaf can have full gcd.
The decisive assertion (2) fails, so the descent and its completeness need
new reasoning there. Handling even N, prime powers, primality and recursive
complete factorization is outside (11), regardless of how cheap individual
prechecks might be.

## 8. What the concentration threshold establishes

For a fixed accepted-output law, the repaired consumption route has expected
work bounded on the scale

    T_F <= setup_F + O(A_k/sqrt(c_*)
                      + T_det(ceil(c_*^(-1/2)),N)).          (12)

Here setup_F means setup actually reused across trials; work that must be
repeated belongs in each trial's cost. For a fixed schedule with positive
survival, the expected-cost refill driver and geometric doubling of accepted
list sizes attain this scale, up to the stated polynomial logarithmic envelope,
without knowing c_p or c_q. The same N-only size cap is sufficient because
c_*>=1/m_p. A computable survival lower bound is needed for the separately
claimed bounded-attempt variant, not for the conditional finite-expectation
refill argument. This distinction does not supply survival for any proposed map.

Keep n+log K in the detector bound unless K is explicitly at the birthday
scale; there log K=O(n) because c_*>=1/m_p. Map parameters, depth counters,
their construction and any larger intermediate operands remain part of A_k
and setup_F. The identity control replaces c_* by 1/m_p and A_k by A_0.

If one adopts the common linear-in-K, polylogarithmic-overhead model, let
A_eff,k and A_eff,0 include the respective accepted-input costs and the
per-output detector charge. Neglecting a setup term only when it is dominated
or explicitly amortized, the modeled cost ratio is

    (A_eff,k/A_eff,0) / sqrt(m_p c_*).

The break-even comparison is therefore

    m_p c_* > (A_eff,k/A_eff,0)².                            (13)

When these are the specified normalized costs of the model, (13) is its
break-even inequality; constant-factor equivalences alone locate that boundary
only up to constants. Strict asymptotic improvement requires
the ratio to tend to zero, with logarithmic factors accounted for. Comparing
two unspecified big-O envelopes does not by itself prove an actual speedup,
nor does failure of (13) prove that every implementation loses.

The parent's display using c_p is a sufficient orientation-specific comparison;
the detector can exploit whichever prime has larger collision energy. Its
shorthand C_k/(sigma_p sigma_q) is appropriate only after including the sampler,
all gcd/inverse work and the identity's cost in the chosen normalization.
In an idealized unit-cost normalization it should at least behave as
(1+C_k)/(sigma_p sigma_q), with a further nonzero detector term. Setting C_0=0
must not give zero cost for uniform sampling. Formula (10), in bits, avoids
this ambiguity.

For C_k=Theta(k) dominating all other charges, no sharing, and the same cost
units, a p-oriented compression gain m_p c_p merely Theta(k) fails to pay for
that orientation at large k: its cost ratio grows like sqrt(k), even at full
survival. The other prime could still provide a larger c_*. A gain
beyond k² is needed for an asymptotic advantage in this particular model;
survival loss multiplies the required gain by 1/(sigma_p sigma_q)². These are
comparisons with the uniform birthday control, not established factoring
benchmarks overall and not impossibility statements.

There is also a precise reason not to promote the cost criterion to necessity.
A rejected input can already yield a proper denominator gcd; an intermediate
state can yield a direct factor; a different map evaluator can share work;
and a better established factoring method can avoid this event. Those events
need their own charged stopping laws. They must not be added as independent
successes to (9). For genuinely shared evaluations replace K A_k in (12) by
the proved total batch acquisition/evaluation cost before making any comparison.

## 9. Primary prior art and the remaining computational obligation

Bostan–Gaudry–Schost's 2007 paper explicitly develops effective finite rings,
multipoint evaluation and gcd descent, and describes Strassen's factoring
construction from a product polynomial and block evaluations. Its Lemma 12
finds a nonunit by product-tree descent; a nonunit may still have full gcd,
which is why this report separately proves (2)–(3). Their stronger specialized
factorial results are not being asserted for arbitrary random points.
[Bostan–Gaudry–Schost, sections 1–2, 5 and appendix](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf).

Brent's 1980 paper, sections 5 and 7, gives product batching of Pollard-type
gcd tests and backtracking after a full aggregate gcd. Its polynomial-orbit
birthday runtime discussion explicitly uses a random-function assumption.
Here the probability argument instead uses independently sampled finite-group
points, at the cost of batch storage and polynomial arithmetic. The known
collision/product/backtracking ideas are prior art; neither the norm-one
coordinates nor the duplicate repair is claimed novel.
[Brent, An improved Monte Carlo factorization algorithm](https://maths-people.anu.edu.au/~brent/pd/rpb051i.pdf).

The two primary PDFs and their text extractions are retained. The focused
read scope was BGS printed pages 1777–1784, 1790–1792 and 1802–1803, and
Brent's relevant discussion on printed pages 180–183. Strassen and Pollard's
original papers were not independently retrieved: their history here is
attributed through the inspected primary follow-up papers. No exhaustive
priority search or current-best factoring comparison was attempted. Two web
opens of Bernstein's multapps endpoint returned internal errors, as did one
scaledmod endpoint; neither was relied upon. Search-result snippets and
secondary explanations do not support any accepted theorem here.

The constructive bottleneck that remains is **paid distribution improvement**:
supply an N-only evaluable schedule with the required local product law and
sign symmetry, positive quantified survival, and collision second moments
large enough relative to its full acquisition/evaluation cost. Alternatively,
prove an actual batch evaluator that lowers that cost, or give a separately
priced direct-extraction law. Degree growth, reduced image size, a functional
graph picture and inexpensive syntax for a rational map do not supply those
proofs.

No new experiment is selected or authorized by this review. A future use of
already frozen graph records could count surviving fibers, normalize as in
(5), and compare (12)–(13); that would be labeled post hoc and would leave
the screen's original primary criterion unchanged. Acceptance of any specific
map or its screen remains entirely with the separate review and coordinator.
