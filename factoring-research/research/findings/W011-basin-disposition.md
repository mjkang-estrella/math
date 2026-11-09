# W011 frozen-family basin screen — parent disposition

2026-10-08. REJECTED for the preregistered finite window. No improved
factoring complexity bound or measured candidate runtime is established.

The parent read the [full report](W011-basin-screen-report.md), reviewed
the graph, chart, exact stopping-count and deadline code, independently
verified all 20 delivery hashes and nine frozen-input hashes, and
recomputed all 850 depth formulas and exact qualification comparisons
from the retained histograms. These were retained-data checks, not new
field enumerations or another candidate run.

The single main diagnostic completed in 9.446882 seconds, including
prime setup and durable output, under its 60-second cap. All 80 parameter
records were clean; all five cubic controls and 850 depth slots completed.
There were no omitted failures, chart factors, timeouts or unstarted cases.
The fixed p=5,q=7,a=2 correctness instance was separate and passed.

The required count was 8/16 qualifying parameters on EACH primary pair:

| Field pair | Qualifying parameters | Best optimistic normalized cost |
|---|---:|---:|
| p=8209, q=8219 | 0/16 | 1.179258 |
| p=32771, q=32779 | 0/16 | 8.382451 |

The registered threshold was at most 0.25. Every fixed depth is preserved,
and even the oracle choice of the best depth fails. The normalized cost
omits gcds and several setup/bit costs; correcting those would not rescue
this failure. The hidden factors were used only for the graph census and
oracle depth comparison, never presented as executable factoring inputs.

The retained data distinguish the local causes. At the first primary
pair, a sampled local map has eventual basin fraction 0.778901 but needs
up to 200 iterations to reach every basin point. The best joint case,
seed 13 at depth 64, has success probability 0.464065 and expected
48.582959 updates, still too expensive. At the second primary pair,
the largest eventual target basins among the 16 samples are only
0.014830 of F_p and 0.007688 of F_q. Both small supply and arrival cost
matter. These selected descriptive extrema do not imply a trend or
an asymptotic growth law.

Accept the finite rejection; do not extend this run, tune its parameters,
or treat it as a theorem rejecting every member of the family. The
independent symbolic review A remains live and must be consumed even
though this pilot failed. Frozen mathematical identities remain distinct
from finite performance evidence.

The shared ./scripts/check.sh was run by the parent after delivery:
all 12 Python tests, the Lean source screen and the seven-job pinned
Lean build passed. The diagnostic is not installed in the shared solver;
there is no new Lean complexity theorem.

## Constructive consequence

The failed assumption was that preserving two superattracting known
targets would supply broad, quickly reached rational basins at low cost.
Two colors fix masking, and freezing the map fixes training cost, but
neither supplies fast useful absorption. Merely trying more coefficients
does not remove this bottleneck.

A separate [implicit-discriminant calculation](W011-implicit-discriminant.md)
changes the computation to a compact scalar over an exponentially large
implicit polynomial. Its exact critical-orbit identity also exposes its
limitation: the random-target selector has only O(k) distinct chances.
This parent derivation is not independently reviewed or a new algorithm.

Keep two materially different constructive questions: obtain paid useful
concentration without replaying a growing circuit, and compute a compact
scalar product while preserving its many distinct root opportunities.
W010 prices the first branch's detector; W008 specifies the second
branch's root set and current cost barrier. No new numerical experiment
is selected by this disposition. A new branch needs an actual changed
computation and a preregistered falsifier, not larger runs of this pilot.
