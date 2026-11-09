# H001 — Fermat's favorable-family scaling trap

Status: preregistered diagnostic, known algorithm, no novelty claim.

## Question and mechanism

How strongly do close-factor and square inputs mislead a finite scaling screen
for Fermat's difference-of-squares method? For odd N = pq, write
N = a² − b² with a = (p + q)/2 and b = (q − p)/2. Fermat scans a starting at
ceil(sqrt(N)). On a semiprime with odd factors, the number of a values tested is
(p + q)/2 − ceil(sqrt(N)) + 1. This is an algebraic observation, not a new algorithm.

Baseline: trial division and Pollard rho under identical limits. No claim that
these Python baselines represent optimized NFS or real cryptographic workloads.

## Prediction before measurement

Fermat should be excellent on squares and nearby factors. Separated balanced
factors and especially tiny-factor unbalanced products should show larger work
or censoring as bit length grows. Rho should expose the dependence on the smaller
prime. No universal speed ordering is assumed from one tiny corpus.

## Decisive screen

Run configs/smoke.json. Reject using good close/square results as evidence for
general polynomial factoring if same-size separated or unbalanced composites
show materially larger work or failures within the fixed budget. Inspect raw
rows; do not regress only successful trials. These finite outcomes diagnose an
experimental trap, not an asymptotic lower bound. A failure to observe the contrast
means the screen is inconclusive, not that Fermat is polynomial.

## Costs and scope

All scan arithmetic, gcds, RNG draws, and rho restarts use the event meter.
Control flow and native operation costs are not proved by those counts.
No free square-root-of-N-mod-N oracle or factors are available to solvers.
Generation and verifier know factors; solvers receive only N and independent RNG.

## Follow-up if useful

The sum-of-factors scan formula identifies the missing primitive: locating useful
congruent squares without a long scan. H002 investigates one concrete candidate
mechanism and prices relation generation, dependencies, and gcd extraction.
An independent seed suite is available in configs/holdout.json; once examined,
it is development evidence and must not be called blind evaluation.

