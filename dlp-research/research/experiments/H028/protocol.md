# H028 provisional-key diagnostic v1 — frozen before execution

2026-10-08. Root protocol integrating Sol's bounded diagnostic design and
Opus r2's independent check, plus the now independently proved uniform fibre
bound. Correctness/finite-accounting diagnostic only; NO performance or
asymptotic experiment. Implementation and independent code review precede run.
No curve selection, warmup, parameter retuning or cap continuation.

## Fixed inputs and sampling

H024 fixtures (p,A,B,q,G), in this order:
(59,28,27,73,(34,35)); (101,2,31,103,(0,43));
(251,1,4,271,(0,2)); (8191,1,5,8053,(0,789)).
Recertify p,q primes, q!=p, nonsingularity, generator equation, qG=O,
Hasse interval and q>4sqrt(p), which identify full prime order. No curve search.

Reference Q=17G; candidate matching must not read17.
Fixed seeds7,19,43; state=seed xor p xor q, update
r=(1664525r+1013904223) mod2^32, output=r xor(r>>16).
Derive s=1+output mod(q-1), shift=nextoutput modq; construct G'=sG,Q'=Q+shiftG.
All setup charged. These deterministic cases are NOT iid uniform samples.
The independent-uniform s/shift expectation is a separate mathematical result.

## Exact fibres and coefficient verification

Obtain hG by binary Miller's first-coefficient chain divided by q in Fp.
Enumerate all q group elements with ordinary additions, propagating h by its
addition-defect law. Retain diagnostic point/index/h evidence, never supply it
as free candidate advice. Check each point's equation and final return to O.
Explicit tangent, inverse and identity dispatch, hO=0.

Count raw nonidentity c(a), signed nonidentity d(min(h,-h)), c0,M2,S2.
Check sum c=sum d=q-1, oddness for every pair P,-P, even signed fibre sizes,
S2=2M2-c0² and2(q-1)<=S2<=6(q-1).
At each nonidentity T compute the exact residual-quadratic discriminant from
H028-uniform-fibre-bound.md and its quadratic character using paid binary
powering. Check M2=2(q-1)+sum chi(Delta_T). This tests the implementation;
the proved bound does not require these computations in a solver.

Independent binary Miller chains at indices1,2,3,4,17,q-2,q-1,floor(q/2),
(q+1)/2 must equal propagated h, including final vertical coefficient0.
Do not call the propagation routine inside the reference Miller computation.

For G on each of the FIRST TWO fixtures, additionally construct the entire
rational Miller numerator/denominator in Fp[x,y]/(y²-x³-Ax-B) via explicit
polynomial products and actual line/vertical factors. Read its first normalized
Laurent coefficient using x=z^-2+O(z²), y=-z^-3+O(z).
This is an independent algebraic representation, not c_n slope accumulation.
Check pole orderq and first coefficientq*hG. All polynomial arithmetic/arrays
charged. No symbolic full-function construction on q271 or8053.

Addition-law spot checks: for each fixture, fixed64 index pairs
(i,j)=(t modq,(t*t+17) modq), t=0,...,63, with explicit extra pairs
(0,0),(0,1),(1,0),(1,q-1),(1,1),(q-1,q-1).
Compute group sum by independent affine operation and check stored h relation.
These are finite correctness checks, not all-pairs verification.

## Frozen paired-prefix grid and reconstruction

k=ell=2,W=5,blockB=10,D=(13,15,24,127).
H019 center indices2+5j,j=0,1, advancing10T. Emit each block in ascending index
order. Alternate full baby and giant blocks, rounding full H019 coverage caps
upward. Full list sizes10,10,20,70 on each side; baby index0 dispatched.
Thus nonzero babies I=(9,9,19,69), giants J=(10,10,20,70).
Nominal side-pair totals P=(8,8,16,56) across both lists.

Keep actual full centers/offsets with h, but generate regular side h only from
shared slopes; don't read the diagnostic table to obtain h or target answers.
Reconstruct side x from immutable historical(xC,hC), offset(xJ,hJ) and signed
hSide via lambda=hC±hJ-hSide, x=lambda²-xC-xJ. OneS and four additions/subtractions
plus sign/access costs. Centeroutput x needsnoS. Explicit exception dispatch.
Validate all generated h and reconstructed x against paid affine reference
operations; segregate those reference costs from candidate generation.

Keep every signed bucket record and all descriptors; actual giantO and baby0
handled BEFORE scans. Cache reconstructed x once per record, charge space.
For a raw match compare exact x, then verify first genuine signed recovery
k'=jD±i, k=s*k'-shift against originalQ. Try bothsigns ifh0.
Continue remaininggrid for diagnosticcounts after firstsuccess; no timing/stopping
claim. Also force independent correctness cases for Q'=O, giantO, C=±J,
tangency and zero-key handling; if no nonidentity h0 exists report absence,
do not manufacture a point or silently skip identity semantics.

## Ledgers, gate and limits

Separate certification, enumeration, binaryMiller, polynomialMiller,
addition-law/reference, candidate setup/generation, reconstruction, matching,
verification phases. Store exact total and phase/category counts.

Reportrho exactrational, false/rawpaircounts, cachedreconstructioncountR,
and theoretical fullcap Efalse=2IJ(rho-1)/q<=4IJ/q.
Fixedseedcounts are observations, not estimates of the uniform expectation.
Regular block generation margin2P*S must be adjusted for actual exceptions.
Report symbolicextra setup/Miller/addition/canonical/archive/matching/verification
charges. At most an explicitly optimistic field projection S/M=.8,I/M=8,A/M=0;
RAM/label/lookup work separate. No wallclockorcompleteworkwin from that projection.
Finite headroom loss rejects only that configuration, not the larger-size idea.
Do not treat a sufficient false-match-cost upper bound as a necessary lower bound.
Later matched fullsolver testing needs representative largerparameters/seeds,
identical recordformats/stopping rules and fullmemory/setupwork.

## Global guard and review changes

ONE preregistered10,000,000-event cap,55-second internal work limit,60-second
external guard; no reset, warmuporcontinuation. This increases Sol's unexecuted
3M draft reservation BEFORE ANY RUN to include the independent polynomial
representation and all-point discriminant checks. Opus's unexpanded1M estimate
and all-points binary/all-pairs suggestions were not statically justified and
are not adopted. This10M is a hard reservation, not a certified worst-case ceiling.
Caps give inconclusive partial output, not a pass/failure extrapolation.

Reuse H018 Meter/Field/prime_trial with capconstants set for this probe before
creating the meter. Expand inverses/powers,scalarmultiplication,polynomials,
loop/index arithmetic,comparisons,dynamicarrayaccesses,records. Inherited
bounded-word modularRAM operations are abstractprimitives, NOT bitcomplexity,
Pythonbytecode, hardwaremeasurements or fullsource validation. Register
assignments/fixedrecordfields, instrumentation/timer/hash/JSONadministration
remain administrative but their walltime is included.

Root implementation: key_probe.py, output initial_results.json. Attach fixture
and case records before work, pending-operationmarkers, partialcounters/errors,
protocol/source/dependencyhashes. Interrupted enumeration gives no exactrho
verdict; completedfibres remain separatelyavailable iflatergridinterrupted.
Correctness failure rejects literal implementation/contract pending diagnosis;
no silent repair-and-rerun. Code review required before firstexecution.

Exact eventualcommand from projectdirectory:
timeout --signal=TERM --kill-after=2s 60s python3 -B research/experiments/H028/key_probe.py --execute > research/experiments/H028/initial_results.json

No execution occurred while this protocol was written.
