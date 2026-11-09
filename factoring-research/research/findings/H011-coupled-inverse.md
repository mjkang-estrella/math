# H011: exact inverse patches with costed lattice reporting

Date: 2026-10-08. Revised research round following W001 Card 1 and the full
H006 independent review. **Verified new factoring improvement: NONE.**

**Disposition: reject the explicit affine-residue lattice decomposition for
the requested exponent.** It gives a deterministic, exact interval reporter
with bit cost

    O(R^(5/2) s^3 + Z s^4),     R=2^s,

where Z is its number of reported ordered pairs. The full balanced box forces
this implementation to visit Theta(R^(5/2)) residue classes, even when its
output is empty. An exact second-difference identity explains why one cannot
simply move its affine terminal query to shallower residue classes. This is a
precise obstruction to the selected construction, not a general lower bound
for inverse reporting, early-stop factoring, or factoring itself.

The per-patch query below is executable and preserves coupling exactly. There
is no inverse-interval oracle, nonlinear integer-programming oracle, hidden
factor input, factorization of shifted integers, or uncharged table. Its
Euclidean recurrence is implemented in [H011-inverse-audit.py](H011-inverse-audit.py).
The finite run audits correctness only; it does not infer an exponent.

I read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, W001 Card 1, and all 429 lines of
H006-independent-review.md. The current user brief overrides the stale STATE
description of H006 as pending. H005 and the frozen H006 finite threshold remain
inconclusive; the separate H006 full-tree obstruction is taken as the closed
prior route. No H010 circuit-width or H008 resultant work is duplicated. All
authored files are this report or adjacent H011-inverse-* files.

## 1. Target and output size

Let s>=2, R=2^s, M=R^5, and N be odd with N=Theta(R^6). Inputs I and J are
inclusive integer intervals contained in [R^3/2,R^3-1]; empty intervals are
allowed. Report every ordered odd pair (p,q) in I x J with

    pq = N (mod M).

Then test the ordinary integer equality pq=N to retain actual factors. The
public intervals are input bounds, not advice obtained from factorization.
The constant case s=1 can be handled by direct enumeration. This report solves
only the stated balanced-box reporting problem; it does not supply an
all-composite factoring algorithm.

Write n0=N mod M. Every reported product is n0+kM with 0<=k<R, and a product
that actually occurs is at least R^6/4 and less than R^6. Therefore

    Z <= sum(0<=k<R) tau(n0+kM) = R^(1+o(1)).

Here tau counts positive divisors; each divisor gives at most one ordered
pair with that first coordinate. The elementary uniform estimate
tau(u)<=C_epsilon*u^epsilon suffices: for large prime factors use
e+1<=2^e<=p^(epsilon e), and absorb the finitely many smaller primes into
C_epsilon. This establishes only an output bound. The algorithm never obtains
the factorization of any n0+kM.

## 2. Exact affine threshold, including the power-of-two endpoint

Put m=5s. For any r>=1 and any odd a, set D=2^r and consider the modular
function on integer suffixes

    f_a(x) = N*(a+Dx)^(-1) (mod 2^m).

All denominators here are odd. Subtract the three fractions over a common
denominator to obtain the exact identity in the modular ring:

    f_a(x+2)-2*f_a(x+1)+f_a(x)
      = 2*N*D^2 / ((a+Dx)(a+D(x+1))(a+D(x+2))) (mod 2^m).       (1)

Since N and the denominator are odd, the second difference is zero modulo
2^m if and only if 2r+1>=m. When 2r+1<m its residue has precisely that
2-adic valuation. Thus the sharp threshold for an affine formula valid at
every integer x is

    r_* = ceil((m-1)/2) = floor(5s/2).

At this threshold all first differences agree, so induction gives

    f_a(x) = v_a + delta_a*x (mod M),
    v_a = N*a^(-1) mod M,
    delta_a = (N*(a+D)^(-1)-v_a) mod M.                         (2)

It is important to use this secant slope. For odd m, D^2=M/2, so simply
discarding the quadratic term in the Taylor series is wrong. The extra factor
2 in (1) makes the secant formula exact nonetheless. Equivalently, the
quadratic term can be absorbed into the linear term because x^2-x is even.
The audit tests both parities of s and the immediately preceding depth.

The difference delta_a is divisible by D, as is clear from

    delta_a = -N*D / (a*(a+D)) (mod M).

Every patch requires just two ordinary modular inverses, two modular products,
a subtraction, and exact divisions. No factor of N is used.

## 3. A lattice query with an explicit implementation

Fix r=r_*, D=2^r, H=M/D, and enumerate every odd a in [1,D-1]. Define

    b = v_a mod D,
    c = (v_a-b)/D,
    h = delta_a/D,
    p = a+D*x,       q = b+D*y.

Equation (2) is equivalent to

    y = c+h*x (mod H).                                        (3)

This is the affine lattice

    (0,c) + Z*(1,h) + Z*(0,H),

of determinant H. Compute the suffix box using integer ceilings/floors:

    X0 = ceil((I_lo-a)/D),    X1 = floor((I_hi-a)/D),
    Y0 = ceil((J_lo-b)/D),    Y1 = floor((J_hi-b)/D).

Skip an empty coordinate interval. Since every q is in [0,M), a nonempty
Y interval lies in [0,H-1]. For each x there is at most one possible y.
Consequently the number of points with x in [L,U] is exactly

    C(L,U) = F(U-L+1,H,h,c+h*L-Y0)
             - F(U-L+1,H,h,c+h*L-Y1-1),                        (4)

where

    F(n,m,a,b) = sum(0<=i<n) floor((a*i+b)/m).

To check (4), write a particular h*x+c as H*t+u, with 0<=u<H. The difference
floor((H*t+u-Y0)/H)-floor((H*t+u-Y1-1)/H) is precisely the indicator of
Y0<=u<=Y1. There is no approximate count or probabilistic pruning.

Here is the complete floor-sum query, including signed arguments. If n=0,
return zero. Use Euclidean division

    a=q_a*m+a', b=q_b*m+b',     0<=a',b'<m.

Add q_a*n*(n-1)/2+q_b*n to the answer. If a'=0, stop. Otherwise set

    t=floor((a'*(n-1)+b')/m).

If t=0, the remaining answer is zero; otherwise use

    F(n,m,a',b') = t*n - F(t,a',m,m-b'+a'-1).                 (5)

For a proof, count each horizontal level j=1,...,t. Its first contributing
index is ceil((m*j-b')/a'), so its contribution is
n-ceil((m*j-b')/a'). Summing and replacing ceilings by floors gives (5).
After normalization, successive moduli follow the Euclidean algorithm;
there are O(log m) recursive steps. This is the actual arithmetic underlying
the lattice query, not a unit-cost lattice-enumeration assumption.

For reporting, evaluate (4) at the root [X0,X1]. Discard a zero count. At a
positive singleton, compute y=(c+h*x) mod H and emit (a+D*x,b+D*y). At a
positive nonsingleton, bisect, count the left child by (4), and obtain the
right count by subtracting from the parent. Recurse on positive children.
The implementation also visits immediately discarded zero children; this
does not change the bound. It verifies bounds and the original product
congruence at every emitted point.

Correctness follows from (1)--(5), disjoint residue classes for p, and disjoint
integer bisections. Each permissible pair is emitted exactly once. Actual
factor acceptance uses the additional exact product comparison; congruence
alone is not acceptance. Small modulus factorization and base-case factoring
are both absent. A singleton uses only modular multiplication and comparison.

## 4. Complete cost and the obstruction

All values have O(s) bits: N has O(s) bits, modular values are at most M,
suffix endpoints are at most R^3, and even unreduced intermediate products
have only a constant multiple of s bits. Using schoolbook arithmetic is
sufficient for the following conservative bit bounds:

- Two extended-Euclidean inverses and the rest of one patch's setup cost
  O(s^3). Generating the D/2 residues is charged.
- Each floor-sum query costs O(s^3): O(s) Euclidean steps, each with a fixed
  number of O(s)-bit divisions, multiplications, and additions.
- A patch containing z_a points has O(1+z_a*s) reporting nodes/queries.
  At each depth, distinct positive nodes contain disjoint reported points;
  depth is O(s). Empty patches still cost their setup and root count.
- Emitting all pairs and testing pq=N costs O(Z*s^2), included below.

Thus

    T <= O(D*s^3 + Z*s^4)
      = O(R^(5/2)*s^3 + Z*s^4).                              (6)

Together with Z=R^(1+o(1)), the first term dominates asymptotically. A streaming
depth-first implementation needs O(s^2) working bits for the query/search
stacks plus arithmetic workspace. Stored output would add O(Z*s) bits. The
audit deliberately stores output and reference lists; its memory behavior is
not the streaming bound.

The patch count is unavoidable for **this explicit implementation**. In the
full box I=J=[2^(3s-1),2^(3s)-1], the interval cardinality is 2^(3s-1), a
multiple of D for every s>=2. Therefore every odd a and its odd b have
nonempty coordinate intervals. All

    D/2 = 2^(floor(5s/2)-1) = Theta(R^(5/2))

root queries are reached, for every odd N. In particular, a small or empty
answer does not save those visits. This is a uniform implementation lower
bound, not an inference from sampled residues.

Original Card 1 patches do not add another factor R to (6). A patch modulo R
has D/R refinements modulo D; the R/2 original patches together have D/2
terminal classes. Conversely, describing only the work within one original
patch would omit that full factor R/2.

For K supplied balanced boxes at this same scale, running the construction
separately costs O(K*D*s^3 + Z_total*s^4), charging repeated outputs as well.
Even K=1 already fails the requested threshold. Public clipping can empty
some classes but supplies no uniform bound with exponent below 6/5. This
analysis is not extended silently to the original all-input dyadic boxes:
unbalanced intervals require their own coverage, output, and cost analysis.

There is also a local obstruction to a tempting repair. At any r<r_*, (1)
is nonzero for **every** a and x. No single affine formula modulo M can agree
with f_a at three consecutive suffixes. Therefore a partition of the whole
graph at such a residue depth into contiguous affine suffix segments has
segments of at most two integers. Covering all odd p in the full interval
this way needs at least R^3/8 such segments. Refining residues until (2)
is exact instead gives the Theta(R^(5/2)) class cost above.

This last statement deliberately concerns full-graph affine segments. It does
not exclude skipping classes with a new coupled certificate, grouping
nonconsecutive suffixes, nonlinear lattice constructions, or computing a
batch of queries without materializing its classes. It does not apply a
general integer-programming lower bound, and it gives no early-stop lower
bound after a factor has already been found.

## 5. Primary-source checks and comparison boundary

This is a focused check of directly relevant prior art, not a survey or a
novelty claim. The original PDFs and their retrieval hashes are preserved in
[H011-inverse-sources.json](H011-inverse-sources.json).

**Small roots and known low bits.** Cohn--Heninger, *Ideal forms of
Coppersmith's theorem and Guruswami--Sudan list decoding*, Theorem 1.1 and its
Section 3 proof, give the unknown-divisor bound |x|<=N^(beta^2/d) for a monic
degree-d polynomial with gcd(f(x),N)>=N^beta. They attribute this form to
Coppersmith/Howgrave-Graham/May. To apply it to known low bits p=a+2^r*x,
use the monic polynomial x+a*(2^r)^(-1) modulo odd N. For balanced p, beta is
1/2 up to O(1/s), so the root allowance is R^(3/2+o(1)), while the unknown
suffix has scale R^3/2^r. Thus roughly 3s/2 known low bits suffice; fixed
positive exponent slack avoids boundary constants. Guessing them costs
R^(3/2+epsilon) polynomial-time calls for fixed epsilon>0, already above
R^(6/5). Applying that enumeration separately to the O(R) shifted products
would cost R^(5/2+epsilon) times polynomial factors. This application is an
inference from the stated theorem; it supplies no free unknown bits or
shallower coupled query. [Primary paper](https://arxiv.org/pdf/1008.1284).

**Existing modular-hyperbola factoring.** Di Mauro's *Canonical form of
modular hyperbolas with an application to integer factorization*, Section 4
and Algorithm 1, use quadratic-residue targets modulo products of odd primes,
enumerating targets and their square roots before a further search. The
paper explicitly defers its full complexity analysis and reports a roughly
n^(1/3) running-time scale. It does not establish an output-sensitive reporter
for arbitrary boxes modulo R^5. Its existence prevents presenting modular
hyperbolas themselves as a new factoring mechanism; its target-generation
work cannot be imported as a free operation here.
[Primary paper](https://arxiv.org/pdf/2001.09814).

**Existing costed lattice factoring.** Harvey--Hittmeir's *A log-log speedup
for deterministic integer factorisation*, Lemma 3.1 and Proposition 3.3,
explicitly cost rank-two lattice reduction and use it to construct useful
linear forms inside a larger collision algorithm. Theorem 1.1 proves the
N^(1/5)-scale deterministic reference with logarithmic factors. A small
lattice query is therefore established machinery, not the missing discovery.
For N=Theta(R^6), its reference exponent is 6/5; (6) instead has exponent
5/2, or 5/12 in N. Indeed, fully charging this known factorization routine
for each n0+kM gives a simple reporting baseline of
R^(11/5)*poly(log R), plus R^(1+o(1)) divisor-output work. This is expensive
but still asymptotically better than the selected construction. It is a
comparison, not a factorization subroutine hidden inside our reporter.
[Primary paper](https://arxiv.org/pdf/2105.11105).

Even an eventual fixed exponent below 1/5 in N would remain asymptotically
slower than heuristic GNFS. A balanced-box result would additionally need
an all-input reduction before making a general factoring claim.

## 6. Frozen finite correctness audit

Before running, I froze the exact source and
[protocol](H011-inverse-protocol.json). This was one finite run, with a
50-second cooperative cap including case construction, a 55-second outer
TERM deadline, and a 2-second kill grace: at most 57 seconds. No rerun,
post-selection, new packages, or shared harness changes were used.

The complete [case manifest](H011-inverse-cases.json) was written before
attempts. Line-buffered [events](H011-inverse-events.jsonl) preserve starts
and outcomes; the [result](H011-inverse-results.json) retains every status.
The source/protocol freeze event precedes all attempts. A mismatch would
reject correctness and stop, preserving later cases as unstarted; a deadline
would yield an incomplete audit. Finite acceptance of a complexity exponent
was expressly excluded.

There were 61 registered cases:

- One exhaustive signed floor-sum block: 208,845 comparisons over
  n=0..8, m=1..17, a=-17..17, b=-19..19.
- Twelve affine-threshold blocks for s=2,3,4,5 and each public input
  N=R^6/4+1, 5R^6/16+1, 3R^6/8-1. Both r_*-1 and r_* were checked for
  every odd residue at that depth: 11,880 second-difference comparisons.
- Forty-eight reporting cases: the same twelve N values, each with the full
  balanced box, its explicitly defined Card 1 clipping, a singleton p
  interval, and an empty interval. Each output list was compared with
  exhaustive inverse enumeration performed only after reporting completed.

**All 61 passed; zero failed, timed out, or remained unstarted.** The recorded
time through the end of case execution was about 0.371 seconds, before final
result serialization. It includes checks and reference work and is not a
factoring timing. The reference inspected 31,301 candidate
p values. Across reporting cases the reporter visited 23,760 patch iterations,
made 11,083 count queries, and emitted 16 pairs, all retained in the results.
There were no actual factor pairs in this selected corpus. All positive
modular outputs occurred in full-box cases; the clipped and singleton cases
had empty answers. Thus the finite run checks positive modular reports,
empty queries, and the exact arithmetic, but does not test positive clipped
outputs or provide a successful factoring-performance demonstration.

For the full boxes, the class counts per input were exactly 16, 64, 512, and
2,048 for s=2,3,4,5. Small outputs at those sizes are not evidence of efficient
reporting. The rejection of the target exponent rests on the analytic count
D/2 and identity (1), independently of these observations.

Frozen SHA-256 values:

    source   4e37b4be8b46b7e258b0fc135a360a2e559c37d3218697523097b187cf98da8e
    protocol ea6f387fdf3ecf3ba43b61deb39a67d03a8a626f3aa684150b39f44224092f3b
    cases    f90a06f216b3d0f07a7e4648b59bf46bf59f4f497fcef5b56a92635d54eaf0c1
    events   a3b58e7b893c193c5072fdef8c4593848ecf17e368635f04cbba03355462fb14
    results  4ead494ba8e8d2280798505bd59e67e1f70c8ffbc10ce9af04aa35b5df519e36

No shared-code/Lean build was run: the only executable change is the owned
scratch audit, and the user restricts writes to H011 artifacts. The audit
does not import the laboratory package or produce a bytecode cache. No Lean
theorem, semantic refinement, or independent review is claimed.

## 7. Remaining bottleneck and a useful reopening threshold

The missing step is **constructing and excluding groups of exact inverse
branches before spending one query per affine class**. Faster inverses or a
faster per-lattice floor sum cannot remove the number of those classes.

To beat the specified deterministic reference using explicitly processed
classes at depth r=alpha*s, polynomial per-class work would need alpha<6/5
and total output/other work R^(6/5-delta) for some fixed delta>0. At those
depths the second difference (1) survives; ordinary Taylor truncation modulo
R^5 needs at least degree four. Merely naming its powers as new variables
reintroduces the unsupported nonlinear coupling from the old route.
More generally, R^gamma work per class and R^eta boxes require
alpha+gamma+eta<6/5 before even counting other work.

A concrete reopening obligation is an exact algorithm that batches the root
counts (4) over sets of residues a without computing every a-dependent
inverse/slope separately, or another equally explicit coupled query at
r<(6/5-delta)s. It must bound all empty-group work and reporting across the
entire box. Relative to the present D classes, reaching that target requires
an exponent saving greater than 13/10, not just a logarithmic improvement.
No such transition or bound is provided here. A benchmark of a guessed batch
oracle, or a further survey without that primitive, would not resolve it.

The costed affine construction and its sharp threshold are suitable for
coordinator review as a negative result. Current verified improvement remains
**NONE**; there is no polynomial-factoring or general hardness claim.
