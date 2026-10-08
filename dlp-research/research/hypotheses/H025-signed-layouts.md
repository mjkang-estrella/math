# H025 explicit signed layouts — proposals pending independent review

2026-10-08. Native Sol proposal, no numerical run. Verified gain NONE. Root
raised the modular-division issue; the proposer supplied the chart argument
below in response. It remains to be independently reviewed. These are fixed
public arithmetic progressions, not a new exponent or a claimed novel technique.

For group order prime q, label points P_i(j)=b_i Q+(c_i+j*s_i)G.
M=floor(sqrt(q/2)). All floors/square roots are exact integer operations.

## A: quadratic shifts and Sidon coefficients

q>17. D=floor(q/17), b=(0,1,3,7), s=(1,M,−(M+1),M+2),
c_i=D*b_i² modq. Grow nonnegative index intervals, cyclic family order.
Intended gain: separate collision channels whose origins coincide without shifts.

For sign epsilon, let e=b_i−epsilon*b_l, Delta=epsilon*b_l²−b_i²,
v=epsilon*r*s_l−j*s_i. Candidate k obeys

    k/q=Delta*D/(e*q)+v/(e*q)+h/e

for an integer h. Its limiting origin belongs to all residue charts
{Delta/(17e)+h/e mod1:0<=h<|e|}; ordinary real division is insufficient.
The proposer lists sign-convention-independent positive fingerprints
1,3,7,4,8,10 modulo17 and nonbaby negative fingerprints11,2,16. Distinct
fingerprints and invertible denominators are claimed to separate limiting
origin sets, with two baby signs intentionally sharing origins. Finite distance
from a chart is at most(|Delta|+|v|)/(|e|q). Within-channel injectivity also
requires stride-gcd/wrap conditions. Proposed short-prefix coverage12L²−3L
is NOT accepted without review. Neither short separation nor that formula
establishes a gain near the critical sqrt(q) prefixes or controls late holes.

## B: four nonzero giants and centered prefixes

q>=73. D=floor(q/73), b=(1,2,4,8),
s=(M,−(M+1),M+2,−(M+3)), c_i=D*b_i² modq.
Same chart argument with73. Proposed fingerprints: positive3,5,9,6,10,12;
negative26,18,64,52,36,31. Grow centered intervals by alternating positive
and negative frontier blocks so candidate patches retain fixed centers.
Same-family negative candidates remain linear. Extra frontiers are paid;
critical-prefix coverage and tail benefit are unsupported.

## Exact wrapper proposed for both

h=max(1,floor(log2(q)/16)), k=ell=h, block B=h*(2h+1).
Emit complete contiguous H019-style blocks in family order0,1,2,3; charge
and inspect only at block completion. A advances its positive frontier.
B starts with the centered interval of length B, then whole-family rounds
alternately append B positive and B negative indices, with two center arrays
per family. Pay stride points, offsets, starting centers, advances and exceptions.
For odd B, initial centered indices are−(B−1)/2 through(B−1)/2;
for general B freeze floor-centered endpoints before implementation.

Cap main at the largest whole-block count <=3ceil(sqrt(q)). On failure clear
the main table with paid work, then use signed two-family fallback b=(0,1),
c=(0,0), s=(1,−ceil(sqrt(2q))) through index ceil(ceil(sqrt(2q))/2),
INCLUDING zero and completed-block overshoot. No main/fallback cross-pairs.
All nonzero signed denominators recover k exactly; include direct infinity,
useful same-family negative matches and verification on the original curve.
Peak memory=max(main cap,fallback records)+actual support/scratch/frontiers.
Equal asymptotic memory order alone is not a finite equal-memory claim.

## Proposed bounded integer-only gate (not yet admitted)

Two candidates and actual GWZ control b=(0,1,2),c=0,s=(1,M,−(M+1)).
Primes73,509; identical block rule/cap/fallback. Enumerate signed candidate
scalars and first discoveries; sum B*(q−covered_before)/q at completed blocks.
Retain discovery bitmap across fallback solely for probability accounting;
cleared main records are not compared against fallback records.

Claimed conservative envelope20853 candidate updates over six combinations,
40 RAM events/update plus50000 setup/loop/clear events =884120. This is a
proposal, not a certified bound; concrete code and guards must be reviewed.
One global1M-event/60s cap, exhaustion inconclusive. A declared5% finite key
saving needs E_candidate<=.95E_GWZ on BOTH primes including fallback. Passing
requires larger independent validation and complete EC arithmetic/memory costs.
Failing does not by itself disprove an asymptotic family; these tiny primes
may be dominated by setup, rounding and tails. Do not claim a hardness change.

Known prior art: GWZ section3.1 and AppendixB; multi-giant schedules and
optimized shifts are known. Original H025 Grok independent ideation stays live.

Root review objection before any run: alternating one-sided B-sized frontier
blocks does not hold the interval midpoint fixed after EACH inspected block.
The midpoint returns only after both frontier extensions; intermediate drift
and family-order effects must be paid/enumerated. Proposed general initial
interval:−floor(B/2)..ceil(B/2)−1. Independent review pending.
