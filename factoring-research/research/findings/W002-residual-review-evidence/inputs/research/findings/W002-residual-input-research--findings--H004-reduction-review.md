# H004 — Independent reduction and leaf-cost review

Date: 2026-10-07 America/Los_Angeles. Scope: the assigned H004 reduction,
correctness, uniform bit cost, and restricted implementations. No conjecture is
assumed true. **Verified algorithmic improvement: NONE.**

**Disposition: the conditional reduction is correct, with the qualifications
below; it is implicit in the existing integer-factorization framework, not a new
factoring algorithm.** The useful change is an implementation interface: resolve
only the part of a leaf that meets the current divisor. No efficient construction
with a sufficiently cheap implementation of that interface has been established.

Instructions and evidence read: `AGENTS.md`, `README.md`,
`docs/SPECIFICATION.md`, `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`,
`research/STATE.md`, `research/hypotheses/H004.md`, and the completed
`research/hypotheses/W001-baselines.md`. This task owns only this report. No
shared harness, Lean, checkpoint, other report, or task registry was changed.

## 1. Primary-source comparison

Source checked directly: [Umans–Wang, §5.1, Theorem 5.2 and proof](https://arxiv.org/html/2511.10851#S5.SS1).
Its parameter `n` is our `R`, not the input bit length. Its hypotheses require
every integer at most R to divide the **aggregate product**, interval products in
soft-O(log(d) R^gamma) time, and full leaf prime factors in soft-O(R^gamma) time.
The conclusion is soft-O(N^(gamma/2) log(k)). The proof starts with the product
gcd, collects small prime divisors, and strips their multiplicities from N.

[Conjecture 5.1 and Theorem 5.5](https://arxiv.org/html/2511.10851#S5)
add prefactoring and state the conditional exponent max(alpha,beta)/2.
[Lemma 6.2](https://arxiv.org/html/2511.10851#S6) already studies prime-only
arithmetic-progression coverage; [§7](https://arxiv.org/html/2511.10851#S7)
already discusses short addition sequences. The conjectures use an
infinitely-many-scales quantifier. Lemmas 5.3–5.4 print d <= R, while Theorem
5.2 requires d <= N; the interface below explicitly requires the latter.

**Review inference.** The proof below isolates what that argument actually
needs. Coverage of each composite by one difference was already unnecessary in
Theorem 5.2; prime-power coverage in its aggregate product is also unnecessary
for recovering prime support. Replacing complete leaf prefactoring with a
costed gcd-factor routine is a valid further interface weakening, immediately
compatible with the same proof. This source comparison supports “implicit
specialization,” not a priority claim or a claim of a new exponent. It does not
establish that every promising implementation of the weaker interface is known.

## 2. Exact conditional proposition

Write n = floor(log2 N)+1, R = floor(sqrt(N)), and assume N >= 2. Complexity is
deterministic bit-machine time for one fixed finite collection of programs.
For each N suppose the following algorithms and guarantees are supplied.

1. **Uniform construction.** `Gen(N)` constructs a finite descriptor D and an
   integer k >= 1 for nonzero signed integers A_1,...,A_k. For every prime
   p <= R, some A_i is divisible by p. Its complete time is C_gen(N), including
   search, parameter selection, description writing, tables and any coverage
   checks it performs. Only N and uniformly computed public parameters are
   inputs. A uniform mathematical proof of coverage can replace runtime coverage
   testing; unproved coverage cannot. There is no supplied factorization or
   size-dependent advice.
2. **Interval products.** `Prod(D,a,b,d)` returns
   product(A_i, a <= i <= b) modulo d for every valid interval and 2 <= d <= N.
   Denote its bit cost by P_N(d,[a,b]). Descriptor access, decoding, arithmetic,
   intermediate widths, scratch storage traffic and output are included.
3. **Leaf resolution.** `Leaf(D,i,d)` returns exactly the distinct prime
   divisors of gcd(d,|A_i|), at cost L_N(d,i), for 2 <= d <= N. This is a real
   finite algorithm with a proved bound, not an arbitrary function or oracle.
   Its cost includes producing the list and obtaining any auxiliary data.
   In fact the reduction below calls it only when d divides A_i, so proving it
   on that restricted domain is enough. Factoring A_i outside that gcd is
   unnecessary.

Then N can be fully factored, with multiplicities, in the cost in §4.
Neither squarefreeness nor an initially proper gcd is necessary. The statement
remains valid for prime N; it does not need a composite-input promise.

All bounds are conditional on **implementations** of these programs. Their
mere availability without quantified bit costs implies no complexity gain.
The proof never queries an unimplemented leaf oracle.

### Algorithm

Compute R by an integer square-root algorithm, run Gen, and set

    g = gcd(N, Prod(D,1,k,N)).

If g > 1, call `Visit(g,[1,k])`:

    Visit(d,[a,b]):                 invariant: d > 1 and d divides product A[a:b]
        if a == b:
            return Leaf(D,a,d)
        c = floor((a+b)/2)
        u = gcd(d, Prod(D,a,c,d))
        if u == 1: return Visit(d,[c+1,b])
        if u == d: return Visit(d,[a,c])
        return Visit(u,[a,c]) concatenated with Visit(d/u,[c+1,b])

Otherwise the returned list is empty. Remove duplicate primes in the list.
For each remaining p, divide a mutable copy m of the **original N** by p until
p no longer divides it, recording the exponent. If m > 1, output m with
exponent one. Return the resulting prime/exponent list.

For a checked implementation, use deterministic primality tests on reported
primes and the final remainder; check completeness at each leaf by dividing its
d by the reported primes to exhaustion. These checks and final reconstruction
are charged in §4. They detect a faulty Leaf implementation; they do not repair
an incomplete cover. No probable-prime test is substituted for a proof.

### Proof

Let Q_I be the integer product of the leaves in interval I. Q_I is used for
reasoning only; the algorithm need not construct it. Signs are immaterial to
divisibility. Initially g divides both N and Q_[1,k]. Every prime p <= R
dividing N divides Q_[1,k], hence divides g, irrespective of its multiplicity
in Q_[1,k].

Suppose d divides Q_L Q_U at an internal node and set u = gcd(d,Q_L).
For each prime p, put e = v_p(d), x = v_p(Q_L), y = v_p(Q_U). Then

    v_p(u) = min(e,x),
    v_p(d/u) = max(e-x,0) <= y.

Consequently u divides Q_L, d/u divides Q_U, and the product of the nontrivial
child divisors is exactly d. Their prime supports need not be disjoint.
This proves the invariant even when prime powers are split between children.
The index interval strictly shrinks on every call, including u = d and u = 1,
so its height is at most ceil(log2 k). At a leaf, d divides A_i and therefore
gcd(d,A_i) = d. The leaf lists together contain exactly the prime support of g.
In particular they contain every prime divisor of N at most R.

After repeatedly dividing the original N by this support, the remaining m is a
divisor of N with no prime divisor at most R. If m were composite, it would
have at least two prime factors greater than R, counting multiplicity. Their
product is at least (R+1)^2 > N, impossible. Thus m is 1 or a prime, and that
prime has multiplicity one. Primes greater than R already found by Leaf cause
no difficulty: they have simply been removed earlier. This proves full
factorization, including multiplicities. For N = 2 or 3, a cover with A_1 = 1
is sufficient and the same remainder argument applies. QED.

### Edge cases that must not be simplified away

- **Insufficient prime powers:** N = 16, R = 4, A = (2,3) is a valid prime
  cover. Here g = 2, whereas N/g = 8 is composite. Treating N/g as the final
  prime is wrong; dividing all occurrences of 2 from original N gives 2^4.
- **Overlapping prime supports:** N = 12, A = (2,6) gives g = 12 and children
  2 and 6. Their common prime 2 is allowed; deduplicate before extracting
  exponents from original N.
- **Root or child gcd equals N/d:** N = 6, A = (6) leaves the whole composite
  for Leaf. With several leaves an equality branch shortens the interval, not
  necessarily the integer. This is termination, not evidence that Leaf is easy.
- **Uncovered large prime:** N = 15, A = (2,3) finds 3 and leaves prime 5.
  For prime N = 17 the same cover gives g = 1 and leaves 17.
- **Zero differences:** zero is excluded. Dropping zero terms from a cross
  product requires a costed ordering/filtering implementation; substituting
  zero leaves makes the gcd equal d and transfers the work to Leaf.

## 3. What the weakening does and does not buy

The N = 16 example proves a strict logical weakening of the aggregate-coverage
hypothesis: 4 need not divide the aggregate product. For a second distinction,
A = (2,3,4,5) covers every integer through 6 in its aggregate product although
no individual leaf is divisible by 6. Do not conflate prime coverage, aggregate
integer coverage, and coverage of each integer by one leaf.

The new leaf interface can avoid decomposing enormous factors of A_i that are
coprime to d. It is thus meaningful as an implementation target. Nevertheless,
for an unrestricted leaf A = d, resolving gcd(d,A) is exactly full factoring
of d. Computing that gcd or keeping its residue small does not resolve it.
Actual useful savings require an additional, explicitly exploitable promise on
the constructed leaves or on their intersections with d.

There is no analogous transfer to polynomial distinct-degree factorization:
composite irreducible degrees must be covered too. Divisibility by all prime
degrees separately does not imply divisibility by their products or powers.

## 4. Full bit-cost recurrence

Let w(d) be the bit length of d >= 2, h = ceil(log2 k), and
eta = 1 + ceil(log2(k+1)). Let G(w) and D(w) upper-bound gcd and exact/remainder
division on w-bit operands, including their ordinary arithmetic overhead.
Let I_sqrt(n) be the cost of integer square root. Use any explicit finite
algorithms; schoolbook bounds suffice for this reduction.

For nonempty interval I with midpoint children I_L,I_U, define the actual
recursive cost T_N(d,I), excluding the final validation/deduplication phase.
There are no calls on d = 1. For singleton I = {i},

    T_N(d,{i}) <= L_N(d,i) + O(w(d)+eta).

Otherwise put u = gcd(d,Q_I_L). The complete recurrence is

    T_N(d,I) <= P_N(d,I_L) + G(w(d)) + D(w(d)) + O(w(d)+eta)
                + [u>1] T_N(u,I_L)
                + [d/u>1] T_N(d/u,I_U).

The division charge is a safe upper bound also for the two trivial-gcd
branches. Any retained caches must either be included in C_gen or charged on
their first construction. This recurrence does not grant free random access
to a large descriptor: access costs belong in P_N and L_N.

Summing over the actual recursion tree gives

    C_total(N) <= O(n) + I_sqrt(n) + C_gen(N)
                  + P_N(N,[1,k]) + G(n)
                  + sum_internal_v {
                      P_N(d_v,I_v,L) + G(w_v) + D(w_v) + O(w_v+eta)
                    }
                  + sum_leaf_v { L_N(d_v,i_v) + O(w_v+eta) }
                  + C_check/output(N).

Here `I_v,L` denotes the left child interval, not a new primitive. If g = 1,
the two sums are empty. This formula charges the root product and all
preprocessing, including work on prime inputs.

Let Pr(n) bound a chosen deterministic primality algorithm on at most n bits
(for example the AKS ingredient identified in the project specification).
A deliberately conservative final bound is

    C_check/output(N)
       = O(n D(n) + (n+1) Pr(n) + n^2 log(n+1)).

To justify it, all nontrivial leaf divisors multiply to g, hence their total
number of prime factors counted with multiplicity is at most log2 g < n.
The same bounds the number of list entries before deduplication. At most O(n)
successful and unsuccessful divisions suffice to validate leaf lists and strip
the original N. At most n+1 primality checks suffice, with duplicates retained
in this upper bound. Comparison sorting, control, writing exponents, and
reconstructing N fit the remaining conservative polynomial term. The contract
asks for actual prime factors, not merely factors labeled “prime”; any optional
certificate generation beyond deterministic testing needs its own added cost.

### Solving the recurrence without counting k leaves

At any fixed depth, the product of the active d_v divides g. Thus

    sum_v log2(d_v) <= log2(g),
    sum_v w(d_v) <= 2 log2(g) < 2n,
    number of active nodes <= log2(g) < n.

The same width bound applies to the leaves together, even when their depths
differ. There are at most n nontrivial leaves and O(n(h+1)) visited nodes. This
is why there is no obligatory k-fold leaf factoring term. It also explains why
testing every leaf independently against the unchanged N is the wrong cost
analysis: overlapping prime hits could visit almost every leaf.

For example, if for all relevant intervals/divisors

    P_N(d,I) <= a_N w(d),
    L_N(d,i) <= b_N w(d),
    G(w)+D(w) <= c_n w   for 2 <= w <= n,

then the bound is

    C_gen(N) + I_sqrt(n) + C_check/output(N)
      + O(n ((h+1)(a_N+c_n+eta) + b_N)).                 (1)

This is an explicit majorant, so no unsupported additivity of soft-O notation
or integer bit lengths is needed. If the available bounds are instead uniform
P_* and L_*, the always-valid, less sharp majorant is

    O(n)+I_sqrt(n)+C_gen(N)+P_*+G(n)+C_check/output(N)
      + O(n h (P_*+G(n)+D(n)+n+eta)
          + n (L_*+n+eta)).                            (2)

If k = R^O(1) and the interval and leaf costs are at most
w(d) R^gamma times polynomial factors in n, (1) gives
C_gen(N) + N^(gamma/2) poly(log N). This is polynomial in the input length
only if construction and all remaining terms are too. In particular, a
fixed positive gamma remains exponential in n.

To improve the deterministic **power** N^(1/5) baseline recorded in W001,
the maximum power of R among construction, products, and leaf work must be
strictly below 2/5, with the index-depth costs also included. The aspiration
gamma = 1/3 would give exponent 1/6 only after these conditions are proved.
It is not an established parameter choice or a comparison against heuristic NFS.

Memory is also charged: construction stores its descriptor; depth-first traversal
uses at most O(h(n+eta)) bits for a simple stack, plus collected output and the
peak live workspaces of the three primitives. No polynomial-space conclusion
follows if their workspaces are not bounded. Time includes their storage traffic.

## 5. Concrete leaf implementations, and precise obstructions

### A. Known prime factors plus a bounded residual

Here is a genuine sufficient promise, rather than a renamed factoring oracle.
For each queried i, an algorithm supplies certified primes p_1,...,p_t and
guarantees

    |A_i| = (product_j p_j^e_j) C_i,       1 <= |C_i| <= B_i.

Let K_N(i) charge production/reading of these data and their primality evidence.
Compute g_i = gcd(d,A_i) by a singleton product query, strip all powers of the
listed primes from g_i, then trial-divide the remaining h_i to completion.
After stripping, h_i divides C_i, even if C_i also contained listed primes.
Trial division stops once the trial divisor squared exceeds the current
remainder, at which point that remainder is prime. It tests ordinary integers;
there is no uncharged sieve or supplied factorization of C_i.

With D(w) as above, one safe leaf bound is

    P_N(d,{i}) + G(w) + K_N(i)
      + O((t+w+sqrt(min(d,B_i))) D(w))
      + output/control costs.                         (3)

At the actual recursion leaves g_i = d is already known, so the first two terms
can be omitted. This implementation is noncircular. If B_i = R^delta, its
residual trial work is R^(delta/2) times polynomial logarithms, rather than
factoring a potentially exp(R^alpha)-sized A_i. For a 1/6 target this particular
implementation needs delta <= 2/3, cheap K_N(i), and cheap products/construction.
A promise that the remaining h_i is a prime power is another tractable case:
try integer roots for exponents up to w and apply deterministic primality
testing. Such a promise must be proved for the actual family.

This is a sufficient upper bound, not a lower bound on better methods of
factoring h_i. An arbitrary unknown cofactor, or a cofactor that is merely
shortly described, supplies none of these guarantees.

### B. A complete executable sanity example reaches the old scale

Take A_i = i for 1 <= i <= R. Gen writes only this rule and R. Leaf is ordinary
trial division of gcd(d,i) <= R, costing O(sqrt(R) D(w)) up to indexing costs.
No factorization oracle or factor advice is used.

For an interval of length r, let m = ceil(sqrt(r)). Form the degree-m monic
polynomial

    F(X) = product_{j=0}^{m-1} (a+X+j)  over Z/dZ.

Evaluate F at 0,m,2m,... for the complete blocks and multiply the outputs and
the fewer than m trailing terms. Product trees and multipoint evaluation by
monic remainder trees cost soft-O(sqrt(r)) coefficient operations; monicity
avoids division by nonunits even when d is composite. Fast integer/polynomial
multiplication gives a bit bound soft-O(sqrt(r) w), with index handling added.
Thus the whole procedure has the familiar N^(1/4) times polynomial logarithms
scale. This example establishes that the interfaces can be realized without
circularity; it is not a new improvement. The fast product method here is a
mathematical implementation description, not newly benchmarked project code.

### C. Explicit expansion has an unconditional output-size obstruction

Define theta(R) = sum_{p <= R, p prime} ln p. Prime coverage implies the exact
inequality

    sum_i ln(max(1,|A_i|)) >= theta(R),                 (4)

because the primorial divides the nonzero integer product of the A_i. The
classical Chebyshev estimate theta(R) = Theta(R) makes this an Omega(R)-bit
output lower bound for an implementation that writes every leaf in binary.
Writing the prime-factor lists for **all** leaves has the same obstruction:
every prime <= R must appear at least once, with total label length Omega(R).
Repeating labels only increases that cost. These statements do not assume
coverage of composites or prime powers.

Consequently a construction that explicitly allocates/enumerates every prime
and stores all of those assignments is already Omega(R) = Omega(sqrt(N))
in the project's cold-input model. It cannot justify an N^(1/6) or improved
N^(1/5) bound by subsequently reporting cheap queries. A lazy compressed
assignment algorithm is outside this restricted obstruction and needs its own
analysis; there is no general lower bound here on compressed construction.

For cross differences with |S|,|T| <= R^beta and magnitude at most exp(O(R^alpha)),
(4) still forces alpha+2 beta >= 1 asymptotically. Prime-only coverage does not
remove that capacity constraint. Separately, explicitly writing Theta(R^beta)
coordinates of actual width Theta(R^alpha) costs Theta(R^(alpha+beta)).
Upper bounds on their widths alone do not prove this latter lower bound; it
applies when a proposed implementation really writes coordinates of that size.

### D. Gcd descent alone cannot implement an unrestricted leaf

Consider a restricted leaf resolver whose only way to split d is by gcds with
products of its available leaf values, using nonnegative exponents; it may
divide off any already certified primes. If every available value is divisible
by d and no prime divisor has been supplied, every nonempty such product has
gcd d, and the empty product has gcd 1. No proper divisor is ever exposed.
This is an exact obstruction for that resolver, not a lower bound on factoring.

For a concrete covered instance, N = 6 and A = (6) already exhibit the problem.
More generally, put A_1 = N followed by the integers 2,...,R. This is a uniform
nonzero prime cover specified without hidden factors. Because A_1 is first,
the recursion keeps taking its left branch with d = N until that leaf. A claim
that arbitrary leaf gcds can then be resolved merely by another gcd descent
has silently assumed full factoring of N. Later leaves need not even be
queried by this recursion. Other algorithms could use them, but their costs
would have to be analyzed separately.

The counterexample does not contradict §2, which explicitly requires a real
Leaf algorithm. It refutes deriving cheap Leaf from coverage, short notation,
or interval products alone by this restricted descent argument.

## 6. Uniformity and limits of this review

- An existential cover at infinitely many R supplies neither a finite
  construction nor suitably dense usable scales. To pad arbitrary inputs,
  one needs a costed way to find a usable R' >= floor(sqrt(N)) with a proved
  growth bound. R' = R^(1+o(1)) preserves a fixed exponent; uncontrolled gaps
  do not. This obligation is additional to algebraic correctness.
- The modulus domain is all d <= N, including d much greater than R. Modular
  arithmetic on an enormous A_i is not free because its final residue is small.
  Short addition descriptions must be generated and evaluated within P_N.
- A factorization proof for the output and a worst-case time bound are separate
  obligations. Finite tests below establish neither a construction theorem nor
  an asymptotic gain. No Lean theorem or machine refinement was produced.
- A randomized construction or leaf routine needs its own per-input success
  and restart/amplification accounting; (1) is a deterministic statement.
- The initial W001 deterministic/algebraic proposal reports were not present
  under those names during this review. No claims from unfinished reports were
  inferred. The completed W001 baseline is consistent with this disposition.

## 7. Bounded arithmetic validation

Preregistered scope before executing the check: no construction search and no
benchmark. Check the valuation-partition identity for x,y in [1,32] and
d in [1,128] whenever d divides xy. Then check N in [2,1024] using three
explicit covers: the primes through R; those primes packed into three signed
products with an extra duplicate factor 2 when applicable; and N prepended
to the first cover. Use trial division as an explicitly slow leaf implementation
and an independent reference factorization, checking invariants at every node.
Also check the seven named cases listed with the results. Reject on the first
incorrect factorization or failed invariant. Cap execution at 60 seconds;
write no scratch files. This tests the reduction's arithmetic, not the existence
of fast P_N or Leaf.

Result: **all assertions passed**, using an inline Python standard-library
script under `timeout 60s`, with no scratch files. The partition sweep checked
9,520 qualifying triples. The factorization sweep checked 3,069 range cases
plus seven named cases, totaling 3,076; it visited 13,038 nodes, including
6,696 equality branches, 1,019 unit branches and 1,296 proper splits. There
were 257 cases with duplicate prime entries across leaves and 1,464 prime
remainders. Every visited divisor divided its interval product; all leaf
divisors multiplied to g; every level satisfied the stated width bound.

The seven exact outputs were:

    N    leaves             g    terminal leaf divisors    factorization   remainder
    16   [2,3]              2    [2]                       2^4             1
    12   [2,6]             12    [2,6]                     2^2 * 3         1
     6   [6]                6    [6]                       2 * 3           1
    15   [2,3]              3    [3]                       3 * 5           5
    17   [2,3]              1    []                        17              17
    49   [2,3,5,7]          7    [7]                       7^2             1
    60   [-6,1,35]         30    [6,5]                     2^2 * 3 * 5     1

For reproducibility, the packed cover assigns the ascending primes through R
cyclically to three buckets initially equal to 1; negate buckets 0 and 2,
and append 2 when R >= 2. The first cover is `[1]` when R < 2. The third cover
is `[N]` followed by the ascending primes through R. Products in this check
are explicitly multiplied modulo d. Leaf trial division tests successive
integers from 2, dividing their powers out and stopping when the next divisor
squared exceeds the residual. The independent reference uses a sieve through
1024 and divides out its ascending primes. All seven named cases are additional
to the range sweep. This is arithmetic validation of the displayed algorithm;
the slow test implementations are not evidence for its proposed fast costs.

## 8. One decisive next step

Require **one concrete compressed family** to instantiate the known-factors-plus-
residual interface in §5A. The next submission must provide a uniform
`Leaf(D,i,d)` program and prove, for every possible visited leaf, its known-factor
generation cost and residual bound (for a 1/6 trial-division target,
B_i <= R^(2/3+o(1))). Combine those bounds with the family's actual Gen and Prod
costs using (1), without pre-expanding all prime assignments. A family requiring
such expansion is already rejected by §5C; an uncontrolled composite residual
fails this particular implementation target. Either outcome is decisive for
that family. Passing this test would justify a new implementation review,
not immediate acceptance of a faster factoring theorem.
