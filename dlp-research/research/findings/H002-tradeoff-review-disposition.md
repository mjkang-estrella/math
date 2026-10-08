# H002 tradeoff review: corrected comparators and remaining gaps

Native Astra reviewed T1/T2/T4; Grok independently reviewed T3 under task
`ecdloop-h002-components-review-20261008-r1` (raw report retained). No experiment,
solver implementation, Lean extension, or accepted ECDLP improvement follows.

T1: optimize capped expected hitting cost divided by success probability, not
basin coverage alone. [Bernstein–Lange §3.2](https://www.iacr.org/archive/asiacrypt2013/82700321/82700321.pdf)
already selects starts/steps/hash and discards chains. Independent uniform probes
estimating individual basin p≈L²/q to relative error epsilon cost roughly
q/(epsilon²L)≈sqrt(qM)/epsilon² in the proposed regime: a method-specific gate,
not a universal lower bound. Give the comparator all selection trajectories.
Benefit for K targets must exceed extra preprocessing. No selector supplied.

T2: periodic checkpoints on merged trajectories can have different phases and
never match. State-based checkpoints become distinguished points. Compare an
adaptive buffered dense-DP implementation with the same memory, external storage,
I/O and replay budget; no gain from comparing only against an unbuffered baseline.
[Parallel collision search](https://people.scs.carleton.ca/~paulv/papers/JoC97.pdf)
and [memory refinements](https://doi.org/10.46586/tches.v2021.i2.254-274) are relevant.

T4: exact product-polynomial/gcd joins are a conventional algorithmic tool,
overlapping Opus O4. Small batches may reread a degree-M polynomial once per
batch, about M*ceil(J/b) traffic, plus product-tree storage/recomputation. Charge
index/sign recovery and arithmetic. [Bostan–Schost](https://cs.uwaterloo.ca/~eschost/publications/BostanSchost.pdf)
does not establish a free EC solver crossover. Resource-specific constants remain
possible, but no complete measured win exists and no exponent improvement is shown.

T3: immutable (origin,a) records and correctly oriented weighted union-find are
sound for a shared full-point add-only walk: collisions give d_i−d_j=a_j−a_i.
Same-component collisions add no independent scalar equation. A single mutable
potential without record epochs is insufficient. Full verification is required.
Known difference graphs (Fouque–Joux–Mavromati) and sequential reuse of every
solved target's trajectories (Kuhn–Struik) are mandatory comparators. Solving only
a giant component is not solving all K. Multi-target wins do not change the
single-target exponent. These references are reported by Grok; its exact theorem
regimes/constants still need direct verification before using them quantitatively.

Do NOT adopt Grok's unproved blanket dominance conclusion: satellite archives
may have different useful merge behavior, and no coupling proof shows sequential
reuse dominates every finite allocation/memory/parallel regime. Likewise an
arbitrary implementation has no established Theta(sqrt(Kq)) upper bound merely
because the generic optimum has this order. Record only no supported gain and a
stronger required comparator. Generic bounds constrain this generic mechanism,
not all coordinate-aware approaches.

The raw random-map pilot is NOT accepted as written. It counts480k walk steps as
480k total events, omitting permutation/setup, union-find, records and verification;
8k steps versus sqrt(2*65537*32)≈2048 ideal bulk is not a checked success budget.
Every arm must use the same bounded observation model, retain censored failures
in its comparison, and predeclare a paired uncertainty rule. Dropping censored
trials before mean comparison can bias conclusions. No numerical outcome exists.
Given multi-target-only scope and no clear advantage over sequential reuse,
T3 is lower priority than main-problem A1/V1 gates; retain rather than build
months of simulation/proof infrastructure around it.
