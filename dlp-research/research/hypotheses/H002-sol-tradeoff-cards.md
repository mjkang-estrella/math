# H002 independent non-learning tradeoff cards (unverified)

Native Sol `/root/h002_tradeoff_ideas` completed four independent cards without
reading other proposal reports, editing files or running experiments. No verified
improvement. Same preprocessing, memory, external storage, target count, workers
and communication must be granted to the strongest applicable baseline.

## T1. Select endpoint reservoirs by bounded-time attraction coverage

Fix a common executable walk F(X)=X+[s(X)]G. Generate tame candidate chains from
known scalars, retain endpoint labels, and use independent uniform known-scalar
probes to estimate which endpoints are reached within deadline L. Deterministic
greedy coverage selects at most M endpoints, counting overlap and every discarded
probe/chain. Online start at Q+[a]G, track jump sum, and at stored endpoint βG
recover d=β−a−sum mod q, then verify.

Potential gain: material constants in online success per addition, never a new
preprocessing exponent. The conventional reservoir heuristic has success about
ML²/q and construction scale ML in its suitable regime. Total across K targets
is P+KT; even conventional sqrt(qM)+K*sqrt(q/M), optimized in M, has square-root
bulk scaling. Single-target construction is likely fatal. Store endpoint labels,
jump data, selection metadata and peak construction space; charge cycles,
duplicates, all probes, failed chains, lookups, communication and verification.

Prior art: [Bernstein–Lange](https://cr.yp.to/elliptic/cuberoot-20120812.pdf),
[non-uniform preprocessing](https://www.iacr.org/archive/asiacrypt2013/82700321/82700321.pdf),
[Rotem–Segev2022](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITC.2022.12).
Known chain/start/hash selection already exists. Only the deadline-specific
independently measured UNION of attraction basins is proposed as a distinction;
novelty unknown, likely overlap. Unsupported assumption: useful heterogeneity
can be estimated cheaply enough to repay selection over an explicit K.
Falsifier: random-map held-out hitting-time comparison at equal TOTAL construction
budget and advice size, then compare against bulk collision reuse. No run started.

## T2. Buffered reconstructible internal-checkpoint collision streams

Workers carry X=aG+bQ and emit exact point keys, segment IDs and offsets at every
point or a declared checkpoint schedule. Store segment seed/start labels; partition
records into sequential external runs and incrementally join equal keys. Replay
two collided segments to recover labels; when b2−b1 is nonzero recover
d=(a1−a2)/(b2−b1) mod q and verify. Sampled checkpoints do not automatically
inherit distinguished-point suffix coalescence.

Potential gain: constants if removing distinguished-point tail work exceeds all
extra I/O, sorting, buffering, communication and replay. No exponent gain. Store
O(N) emitted records externally, RAM buffers and seeds; charge every pass, key,
fingerprint false match if used, degenerate collision and verification. Match an
optimized DP baseline allowed adaptive density, packed storage, buffered endpoints,
the same hardware/resources and external BSGS/grumpy giants alternatives.

Prior art: [van Oorschot–Wiener report](https://carleton.ca/scs/research/scs-technical-reports/technical-reports-1994/tr-249-parallel-collision-search-with-application-to-hash-functions-and-discrete-logarithms/),
[Trimoska–Ionica–Dequen](https://doi.org/10.46586/tches.v2021.i2.254-274),
[artifact](https://github.com/mtrimoska/PCS), [grumpy giants](https://eprint.iacr.org/2012/294.pdf).
Novelty unknown; possible contribution is a demonstrated full-cost crossover,
not a faster isolated hash table. Falsifier: explicit cost inequality optimized
over both density/schedule/batches; require measured curve/I/O costs before any
hardware claim. No curve campaign justified without a plausible crossover.

## T3. Dynamic retirement of multi-target components with lazy scalar labels

For targets Q_i=d_iG include tame vertex Q_0=O. Use one ADD-ONLY transition
F(X)=X+s(X)G independent of target; archived points are X=Q_i+aG. A collision
gives d_i−d_j=a_j−a_i. Weighted union-find records these offsets. After merging
components, stop launching redundant labels, preserve every old curve record,
and interpret offsets lazily through current component potentials. Allocate
new chains among representatives with low archived collision mass. Joining the
tame component reveals all its logs; recover ALL targets and verify each.

Potential gain: constants from fewer redundant within-component collisions and
less wasted work on isolated targets. This is MULTI-TARGET ONLY, no demonstrated
single-target improvement and no new bulk exponent. Shared add-only mixing/cycles
need inspection. Count endpoints, potentials, component metadata, cancellation
delay, relabel queries, failed chains and all K verifications. Target-dependent
transitions would invalidate the stated shared-suffix reasoning.

Prior art: [Fouque–Joux–Mavromati2014](https://www.iacr.org/archive/asiacrypt2014/88730171/88730171.pdf)
already uses scalar-difference graphs and anchored components; that is NOT novel.
[Earlier sequential reuse discussion](https://www.iacr.org/archive/asiacrypt2013/82700321/82700321.pdf)
also belongs in the baseline. Only adaptive retirement/balanced allocation with
retained trajectories and lazy offsets is proposed, novelty unresolved.

Unsupported assumption: useful cross-component collisions improve enough to
beat existing static graphs AND sequential reuse after scheduling overhead.
Cheapest falsifier: exact random-map trajectories with explicit labels and fixed
record budgets, increasing K/seeds, compare work to recover ALL targets, include
outstanding-worker delay. Simulation labels must not become a solver oracle.
Sol ranks this first for testability, but coordinator has not accepted its novelty
or experiment protocol. Coordinate EC validation remains needed after any pass.

## T4. Exact polynomial-gcd joins for BSGS coordinates

Babies B_i=iG, giant batches H_j=Q−jMG. Exclude/handle identity separately.
Construct A(Z)=product(Z−x(B_i)) and C(Z)=product(Z−x(H_j)). Their gcd gives
matching x-coordinates. Traverse stored/recomputed product trees to recover
indices, check signs, return d=jM±i mod q and verify. Duplicate roots/signs and
index recovery count; root polynomial alone does not identify scalar indices.

Potential gain: constants only if sequential polynomial work beats the best
external hash/sort equality join. Point generation M+q/M remains conventional.
Charge multiplication/gcd, affine normalization, coefficient/intermediate storage,
all tree levels (possibly MlogM), disk passes/recomputation, communication and
verification. Multi-target polynomial reuse only with identical baby reuse for
the baseline. Prior [optimized EC BSGS](https://eprint.iacr.org/2015/605.pdf),
[grumpy giants](https://eprint.iacr.org/2012/294.pdf); polynomial set-intersection
overlap likely, novelty unknown. Unsupported assumption: cheaper actual full join
at a relevant RAM/storage ratio. Falsifier: synthetic exact coordinate-array joins
including recovery/all passes; stop if polynomial method loses before EC costs.
No benchmark started. T2/T4 require a credible crossover before implementation.

All cards are hypotheses, not discoveries. Root prioritizes single-target hardness
separately from amortized/resource-specific gains. A useful negative result can
reject the proposed implementation without excluding other coordinate algorithms.
