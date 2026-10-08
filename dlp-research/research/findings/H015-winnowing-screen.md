# H015 sliding-window reports: scoped mean-delay screen

2026-10-08. Native Astra /root/h006_structured_relation_ideas proposed and
analysed this operation; root independently derived the synchronized result and
checked the asynchronous lower bound. Paper finding, no experiment or Lean claim.
Verified complete-solver improvement: NONE.

## Operation and comparator

Keep a fixed point-only EC walk, hash each point to a rank, maintain the minimum
over the last w positions, and report whenever its selected position changes.
Choose the rightmost minimum on ties. A monotone deque implements this with
amortized constant queue work per point, worst-case w retained entries. Store a
replay locator with each selected rank; actual point and scalar-label recovery
still require paid replay and verification. Fingerprint equality alone is not
an EC relation. Existing cycle escapes/restarts reset the window and cost work.

This uses known [winnowing](https://sschleimer.warwick.ac.uk/Maths/winnowing.pdf),
not a new fingerprint algorithm. Its independent continuous-rank stationary
report density is theta=2/(w+1): among w+1 consecutive ranks the minimum must be
at either endpoint for the selected position to change. The proposed benefit is
bounded report gaps instead of geometric gaps. Compare distinguished points at
the SAME density. Seeded replay, hashed endpoints, negation handling and batching
already belong to the [BLS baseline](https://cryptojedi.org/papers/negation-20110102.pdf).

## Exact ideal-rank paper calculations

Assume full warm incoming windows, distinct positions before merging, independent
continuous ranks independent of the specified merge event, and an uninterrupted
common suffix. These assumptions are not established for every actual EC walk.

Synchronized walkers with independent incoming histories have 2w-t distinct
positions in their two windows after t shared points, 0<=t<=w. Their selected
minima agree exactly when the minimum of this union is among the t shared points.
Thus P(D>t)=1-t/(2w-t). Once selected minima agree they cannot separate: old
unshared positions expire before that selected shared position. Change-only
reporting detects the first such agreement; a previously reported shared point
cannot disappear from one synchronized window and later become the other's
minimum. With D measured in post-merge points,

    E D = sum(t=0..w-1) 2*(w-t)/(2w-t)
        = 2*w*(1-(H_(2w)-H_w)) ~ 0.6137*w.

Matched Bernoulli distinguished points have mean (w+1)/2 ~ 0.5*w. The
synchronized mean is equal at w=1 and greater for w>1: its survival probability
is at least 1-t/w, with strict inequality for 0<t<w.

For an older trail whose entire future report set is already stored, consider
the fresh trail's full warm window. Before its selected minimum is post-merge,
it cannot report ANY point in the common suffix. At time t<=w its window has t
shared positions, so this event has probability t/w. Once true it remains true
until all incoming history expires. The first possible shared report T obeys

    E T = sum(t=0..w-1) (1-t/w) = (w+1)/2,
    D >= T.

This grants the older trail more information than a real online server has,
yet supplies no mean-delay gain in this warm independent-rank model. It does
not resolve cold starts, conditioned hashes, finite epochs or restart policies.

## Whole-work consequence and disposition

Queue work, worst-case walker storage, changed inversion-batch size, replay,
communication, record storage and exact collision verification remain paid.
Continuing indefinitely after reports can make replay much longer than a normal
distinguished-point segment. Epochs limit replay but pay starts and boundaries.
The scoped mean-delay saving is nonpositive BEFORE these costs. Park the named
mean-delay motivation; no engine or numerical trial. A different truncation or
failure-tail proposal must supply its complete paid schedule and a saving that
overcomes this screen. No universal walk-reporting lower bound is claimed.

Root read the primary winnowing PDF and BLS PDF with web open on2026-10-08.
The collision-delay formulas above are our conditional derivations, not results
attributed to the document-fingerprinting paper. No new theorem enters Audit.

## Separate arithmetic card: literal integer-tile map

The same proposer supplied an exact, but currently unattractive, integer mapping.
For sixteen 256-bit products with 32 base256 digits, use A_(i,t)=a_i[t] and
B^(k)_(t,j)=b_j[k-t] when the index lies in[0,31], otherwise0. Diagonal entries
of A*B^(k), k=0..62, give the sixteen convolution coefficients. Each accumulator
is <=32*255^2<2^31; carry propagation and modular reduction remain necessary.

Literal dense evaluation costs63*16*32*16/16=32256 byte MACs per product, versus
1024 useful digit products:31.5 times padding. Explicit B construction emits2016
bytes per product; storing all 32-bit output tiles emits4032 bytes per product.
These are costs of THIS literal schedule, not unavoidable bounds for optimized
packing or hardware. Extraction, packing, reduction, transfers and synchronization
remain unpaid in those figures. No device instruction schedule or measurement
establishes a win. Park; AI peak FLOPS cannot validate it. A materially different
exact map needs a real instruction/storage schedule against a competent modular
kernel before a hardware benchmark could be informative.
