# H024 detected-reversal finite-block screen v1

Frozen before execution, 2026-10-08. Root implementation; independent code
review required before first run. This is a finite necessary-condition screen,
NOT an ECDLP solver, hardware benchmark, asymptotic experiment or full-work win.

Fixtures (p,A,B,q,G), reused without search:
(59,28,27,73,(34,35)); (101,2,31,103,(0,43));
(251,1,4,271,(0,2)); (8191,1,5,8053,(0,789)).
Recertify primes, nonsingularity, generator equation and qG=O. Hasse with q
prime and q>4sqrt(p) then identifies full order q. All setup is counted.
Generate Q=17G once; the walk does not read17. Generate all eight labels before
walking: unsigned LCG r=7 xor p xor q; r=(1664525r+1013904223) mod2^32;
a=(r xor(r>>16)) modq, b=1. Construct aG+Q; do not replace duplicates/exceptions.

Canonical reflection is P→G−P, choosing the smaller shifted abscissa.
Maintain μ=(y+h)/(x−g),u=min(x(P)−g,x(P−G)−g), labels a,b.
Regular μ'=−μ+2h/u,z=μ'²−3g−u. Accept when z<=u.
When z>u, discard this candidate and double the OLD canonical P instead.
Canonicalize the doubled point and its doubled labels. No branch hash or RNG.
For this tiny diagnostic use a linear exact-key history scan (no hash index,
no cross-trajectory table); charge all scans. This implements the same
successor and exact repetition test without unnecessary hash machinery.

Stop each trajectory at first repeated μ, exceptional point, or32 transitions.
Known exceptions O,G,−G,2G,G/2 are checked against the current full point;
recover from labels when b nonzero and verify kG=Q, otherwise record fruitless.
On repetition use both label pairs, verify any nonzero-denominator candidate.
All attempts, exceptions, failed/fruitless terminations and reference checks
are charged. No warmup, reseeding, tuning, dropped start or cap reset.

N counts attempted regular transitions; D counts reversals. At S/M=.8,
the optimistic same-useful-hit-law10% arithmetic gate is D/N<21/620.
A fixture has at most256 transitions. Stop it permanently at D=9:
9/256>21/620 even if every remaining possible trial avoided escape.
Finish the other frozen fixtures. Also report the exact observed finite-block
ratio and terminations; a block that completes with620D>=21N rejects the
strict gate. N=0 is inconclusive. Passing is only not-rejected. This does NOT
exclude improved stopping constants, other schedules or large-parameter gains.

Independent full-affine operations verify every transition and canonical
labels. Diagnostic labels may be checked by paid aG+bQ computations.
No inverse-log table. The five known exception points are paid public scalar
multiples, not a table of challenge answers. History stores at most33 states.

One global60-second/1M-event guard, no continuation on cap. Reuse H018 Meter,
Field and prime_trial only. Their bounded-word modular-RAM convention charges
field/integer/bit ops, comparisons, loops, dynamic array accesses and trace
fields. Powers/inverses are expanded. Fixed tuple/register accesses, assignments,
Python allocation/dispatch, counters/timers, source hashes and JSON encoding are
administrative. Their wall time is included, but this is not bytecode/bit cost.
Extra reference computations and scalar label checks are counted separately;
the probe runtime does not instantiate the ideal batched kernel arithmetic.
No claim every phase fits the cap; a cap exit is explicitly inconclusive.
Retain protocol and source hashes with output; review before execution.

Implementation note: full-affine canonical reconstruction is repeated and
charged in the reference phase; this diagnostic intentionally does not realize
the optimized batch kernel. All partial fixture/trajectory records are retained
on a cap exit. No per-transition500-event reservation is asserted: paid scalar
label rechecks can exceed it, and only the hard global cap is guaranteed.

If the cap interrupts a transition, pending_transition=true distinguishes its
incremented attempt count from a completed decision. Any cap or correctness
error marks the overall run inconclusive; no ratio from an incomplete fixture
is promoted to a passed/rejected result. Previously completed finite blocks
remain recorded as such.
