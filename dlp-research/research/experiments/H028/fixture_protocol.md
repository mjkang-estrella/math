# H028 fixture discovery protocol v1

2026-10-08. Frozen before implementation/execution. This admits ONE bounded
public synthetic fixture discovery run only after independent source review.
It does not admit a matched solver run, tuning, retries or a larger budget.
Purpose: supply certified larger inputs for the named archive-free coefficient
key comparison; not a new point-counting or ECDLP algorithm.

Primary method: Hasse-interval BSGS as described in Schoof, Counting points on
elliptic curves over finite fields, §2 (1995),
https://www.mat.uniroma2.it/~schoof/ctg.pdf . Astra read §2; root independently
read the source. Native Sol checked the specific finite certificate logic below.
This is a reject-only discovery specialization, not a general group-order engine.

## Exact immutable procedure

Visit e=20,25,30 in that order. For each, test at most4096 candidates
p=2^e+3+4t, t=0,...,4095, selecting the first prime. Trial division is explicit,
charged and exact; no probable-prime-only acceptance. If no prime is found,
mark that size exhausted and continue without extending its candidate limit.

For this p, visit b=1,...,64, curve y²=x³+x+b. Reject if4+27b²=0 modp.
No other curve coefficient or twist search is allowed. For each nonsingular
curve scan x=0,...,63 in order, computing rhs and y=rhs^((p+1)/4) modp by
charged binary exponentiation. Take first y!=0 with y²=rhs. If none, rejectcurve.
Verify G=(x,y) lies on the curve. This gives G!=O with no rational2-torsion.

Set L=isqrt(4p), not2*isqrt(p), and B=ceil_sqrt(2L+1). Implement integer
square roots by charged binary-search loops, not an unexpanded builtin. Validate
the integer root bounds explicitly. Compute R=[p+1+L]G and D=[B]G with ordinary complete
affine double-and-add, handling infinity/inverse/tangent cases. Generate babies
jG,0<=j<B, storing full point coordinates and j. Sort lexicographically with
an explicit total infinity sentinel order, then j as tiebreaker, using charged
merge sort (not a hidden builtin). Use charged lower-bound binary search.

For i=0,...,floor(2L/B), search R-iD in the baby array. If matches exist choose
the SMALLEST matching j. Only accept a collision if u=iB+j<=2L. Continue rows
when u is out of range. At the first valid collision, set q=p+1+L-u and stop
this curve's BSGS search. If none, rejectcurve and record it as implementation/
coverage evidence requiring review; never fabricate an order or silently retry.

The candidate q is an annihilator, not yet a group-order certificate. Accept
this curve only after independently computing/checking ALL:
- exact primality of q by charged trial division;
- q!=p, q>3, G!=O and the curve nonsingular;
- [q]G=O by a fresh charged scalar multiplication;
- p+1-L<=q<=p+1+L and2q>p+1+L.

A composite first annihilator rejects the curve; no factoring, alternate point
or alternative collision search follows. Stop at the first accepted curve for
each size. If64 curves exhausted, that size is inconclusive, not a no-curve
or cryptanalytic result. Do not continue unboundedly to fill all three sizes.

Proof of certificate: prime q and nonidentity G with qG=O give order(G)=q.
Lagrange gives q|#E. Hasse bounds #E<=p+1+L<2q, so #E=q. The integer Hasse
interval and primality already exclude tiny parameters here. Ordinary full-prime
order with q!=p avoids anomalous and supersingular cases at these odd large p.
Nonzero a,b excludes j=0,1728 geometric automorphisms, but NOT all endomorphism
optimizations or all special structure. Taking first successful b at a=1 is NOT
representative random-curve sampling or a frozen hard asymptotic family.

## Resource and evidence contract

One global100,000,000 abstract modular-RAM event budget,55s internal deadline,
60s external guard. This exceeds the initial loop default and is justified IN
ADVANCE by up to192 attempted curves, each with roughlyO(p^1/4) additions plus
expanded inversions, sorts, powers and exact primality tests. Around2^30 the
baby width is about363; completion is not guaranteed by this sizing argument.
All failures, rejected curves and failed prime/point candidates count. No cap
reset between sizes. Events use the existing explicit bounded-word convention,
not binary-tape steps or calibrated CPU/GPU work. Field inverse/power loops,
scalar operations, sorting, comparison, lookup, array access and allocation must
be instrumented; reuse controlled source support if appropriate, without
executing/importing it before the reviewed one-run command.

Retain source/protocol/support hashes, timestamps, global and phase counters,
all attempt summaries, accepted public certificates, exit status and partial
active state on internal failure/cap. Do not serialize discovery baby tables as
solver advice. Release each temporary table after its curve; report peak payload
and modeled allocation separately from Python allocator bytes. The later solver
must receive only public curve/G/q parameters and independently validate them.
Retain discovery work in the total research ledger separately from public-input
per-solve costs; never smuggle discovery tables into either candidate or baseline.

No module import, warmup, selftest, trial instance or execution during writing.
Independent static source review precedes the sole command:

    timeout --signal=TERM --kill-after=2s 60s python3 -B research/experiments/H028/fixture_probe.py --execute > research/experiments/H028/fixture_results.json

External truncation, missing JSON or cap exhaustion is inconclusive and retained.
No automatic second run. Code corrections after evidence require a NEW reviewed
protocol/round and preserve the original failure. No wallet/third-party targets.
