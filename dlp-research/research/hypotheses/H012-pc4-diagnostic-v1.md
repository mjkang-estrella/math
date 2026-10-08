# PC4 single-node diagnostic protocol v1 (not authorized to run yet)

2026-10-08. Native Astra proposer /root/h006_structured_relation_ideas supplied
this exact schedule, no computation or edit. Root records it pending independent
cost/prior-art and mathematical screening. It is an implementation/cost diagnostic,
NOT an ECDLP solver, asymptotic test, representative-size series or yield estimate.
No guarantee that even setup fits. See H012-pc4-v1.md for the actual hypothesis.

## One global budget and deterministic setup

From the first setup operation: <=1,000,000 instrumented events and <=60 seconds
wall time, including fixtures, failed search and replay. Discovery stops at900,000
events, reserving100,000 for independent certificate replay. No warmup, resets,
alternate seeds, resumed runs or hidden setup. Setup-only failure is a result.

Search c=1,2,..., p=2310c+1. Exact primality trial division tests2 then odd d>=3
while d*d<=p. Charge all failed candidates/divisors. For each prime construct a
root array indexed by Fp, initially nonsquare; populate y^2 for0<=y<=(p-1)/2
using successive-square first differences and uniqueness checks. Charge allocation,
initialization, accesses and updates. Search A=1,...,p-1 then C=1,...,p-1,
lexicographically. Reject 4A^3+27C^2=0. Count full group order exactly via
q=1+sum_x #{y:y^2=x^3+Ax+C}, using that array and cubic finite differences:
F=C, dF=A+1, ddF=6; after each x update F+=dF, dF+=ddF, ddF+=6 modulo p.
Reject even/composite q and q=p; use the same primality test. First accepted
curve wins. Order is verified by enumeration, not inferred from a single point.

G is first finite point in increasing x with stored least nonnegative y. Verify
G!=O and [q]G=O by paid affine arithmetic, exceptional branches and Euclidean
inversion. For each B_i=(2,3,5,7,11), try h=2,3,... until
beta_i=h^((p-1)/B_i)!=1 by charged binary powering. Since B_i prime, this
certifies its order. Shifts u_i=i-1; never tune them to point counts or target.

## Fixed unfiltered target, not a uniform-random claim

Public deterministic stream: s0=123456789,
s_(j+1)=(6364136223846793005*s_j+1442695040888963407) mod2^64.
kappa=1+s1 mod(q-1), a=s2 modq, b=1+s3 mod(q-1).
Pay for Q=[kappa]G and R=[a]G+[b]Q. If R=O report DEGENERATE_TARGET, no retry.
Do not condition setup/target on decomposition or closure behavior. This stream
is reproducible data, not uniform sampling or a cryptographically hidden secret.
The solver interface receives only p,A,C,r=x(R), shifts and domain constants:
no seed, kappa,a,b,G,Q or scalar labels. This guards against accidental use of
the planted scalar; it is not a real secrecy guarantee.

## Fixtures and root system

After accepted setup, same ledger and schedule:
1. Input x^2-x must saturate without constant; basis rows evaluate0 at x=0.
2. With x>y>z, inputs x^2-y,x^2-z,y-z-1 must produce independently replayed1.
   Audit products of the new linear remainder with ALL three variables queued.
Fixtures prove only elementary implementation behavior. Failure/exhaustion stops.

Only full-arity root chart; no branching, other charts, retries or witness search.
Variable order (18): z1;z2,t2;z3,t3,v3;z4,t4,v4,w4;z5,t5,v5,w5,h5;U1,U2,U3.
Original quadratic gates (15), in order:

    1-z1^2;
    t2-z2^2, 1-t2*z2;
    t3-z3^2, v3-t3^2, 1-v3*z3;
    t4-z4^2, v4-t4*z4, w4-v4^2, 1-w4*z4;
    t5-z5^2, v5-t5^2, w5-v5*z5, h5-w5^2, 1-h5*z5.

Append S3(u1+z1,u2+z2,U1), S3(U1,u3+z3,U2),
S3(U2,u4+z4,U3), S3(U3,u5+z5,r). Build from the explicit13-term S3 template
in the parent card, with degree0/1/2 binomial substitution lists and merges.
Charge every generated term, even later cancelled. No S6, resultants, preliminary
symbolic expansion or dense7315-column allocation. 7315 is capacity only.

## Sparse closure and independent replay

Monomial key is (total degree, base5 exponent code) in the frozen graded lex
order. Degree<=4 prevents exponent overflow on allowed multiplication. Polynomial
representation: descending sorted nonzero coefficient/key lists. Pivots: sorted
index with explicit binary search. Sparse subtraction: two-pointer list merge.
All comparisons, reads, insertions, shifts, copies and allocations are charged.

FIFO starts with19 originals. Reduce against normalized existing pivots, discard
zero, normalize a nonzero remainder by charged Euclid. Constant triggers replay.
Otherwise insert; if ACTUAL degree<=3 queue every variable times this row, ordered
by variable index. Products are lazy(row ID,variable ID) references; charge when
materialized. New low-degree cancellations receive all products. Queue saturation
without1 is SATURATED_UNKNOWN, not satisfiable or empty.

Derivation DAG records inputs, scalar multiplication, variable multiplication
and addition/subtraction; charge every coefficient/reference. Replay walks only
ancestors of proposed constant in increasing node-ID order, using a SEPARATE
implementation with explicit exponent tuples and direct tuple comparisons.
Regenerate originals from the frozen template. Verify each permitted operation
and final polynomial exactly1; do not trust discovered row caches. Charge ancestor
discovery, arithmetic, references, allocations and release bookkeeping. Budget
failure during replay leaves an UNVERIFIED candidate, never a usable certificate.

## Ledger, terminal statuses and decision limits

One event per explicitly instrumented integer arithmetic/division/remainder/bit
operation/comparison; logical cell read/write/allocation/initialization; queue,
stack, iterator/control step; symbolic-key comparison/coefficient step. Field
operations expand to constituent integer operations. Powering/inversion are not
unit cost. No uninstrumented bulk sort, merge, copy or enumeration. This is an
abstract-operation ledger, NOT interpreter instructions or a bit-cost model;
timer/allocator/interpreter internals are covered by wall time. Deadline interrupts
without finishing a phase. Record peak logical cells and peak process memory.

Exactly one status: SETUP_BUDGET, SETUP_TIMEOUT, FIXTURE_FAILURE, FIXTURE_BUDGET,
DEGENERATE_TARGET, ROOT_BUDGET, ROOT_TIMEOUT, SATURATED_UNKNOWN,
CONSTANT_FOUND_REPLAY_INCOMPLETE, EMPTY_CERTIFIED. A timeout during fixtures must
be explicitly distinguished in the phase/detail even if grouped as fixture cap.
Include reached parameters, failed candidates, cumulative phase costs, processed
and pending queue requests, independent rows by actual degree, coefficient
updates, certificate size, memory peak and elapsed time. Reporting overhead is
bounded and separate from continued discovery; no post-cap computation of results.

A replay certifies only ONE raw node. Saturation means only this procedure did
not refute it; a cap hit identifies only a concrete bottleneck. None gives a
root-density estimate, coset pruning rate, rational witness extraction, rank,
full-query yield or an ECDLP advantage. Small unequal B_i are not the asymptotic
balanced family. Independent cost review must assess whether this limited
information justifies even a small implementation before root authorizes it.
