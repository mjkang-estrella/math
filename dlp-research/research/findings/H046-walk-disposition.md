# H046 lazy walks: corrected labels and finite costs, no test admitted

2026-10-09 UTC. Status: reviewed paper screen; three proposals parked, not
impossibility results. Best supported ECDLP exponent remains 1/2; verified
complete-work improvement **NONE**. Raw evidence: H046-geometry-grok-raw.md.

## Mechanisms and recovery

Card 1 always translates a canonical point W=aG+bQ, and conditionally compares
its abscissa with that of 2W. Card 2 conditionally compares W+G with W+Q.
Card 3 translates and then doubles if the translated abscissa is odd. The
coordinate gates define concrete regular transitions once canonical signs,
ties, infinity, tangent and inverse-point dispatch are fixed. The proposed
history-dependent escapes are a separate unresolved part of the full solver.

If kappa(Q)=sigma0 Q, initialization is (a,b)=(0,sigma0), not always (0,1).
Handle Q=O directly. All labels are residues modulo the odd prime q. Equal
canonical points give (b_t-b_s)k=a_s-a_t; recover only when the actual
coefficient difference is nonzero, then verify kG=Q. If noncanonical signed
points are retained instead, use the corresponding signed difference.

For Cards 1/3, b_t=sigma_t 2^(v_t) modulo q, with v_t counting SELECTED
doublings. Equal counts with opposite signs can give useful collisions;
different counts can be null through the signed order of 2 modulo q. The raw
fold-count null test is false. Canonical pure-G translations likewise have
b=+/-b0, not a constant b: their self-collisions are not automatically null.
Card 2's signed affine updates are otherwise valid. Escape steps, discarded
outputs and label reconstruction must be specified and charged.

For Card 1, evaluating the doubling fallback and selecting it are different
events. Neither frequency is proved to be one half. Repeated translated
branches can still contain fruitless two-cycles: with the same increment J,
if A=-W-J is selected canonically and the next gate again selects translation,
the next point and labels return to W. A parity or low-x gate alone does not
prove these cycles are absent.

## A finite arithmetic invoice, not a lower bound

M, S and I denote field multiplication, square and inversion prices. The
nonexceptional short-Weierstrass affine formulas use I+2M+S for addition and
I+2M+2S for doubling, before ordinary additions and small constants. These
formulas were checked directly in the [Explicit-Formulas Database](https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html).

Batch inversion of K nonzero denominators uses I+3(K-1)M. Thus a batch of
doublings costs K(5M+2S)+(I-3M). This is a finite identity for that algorithm,
not a claim I=3M or a model of hardware throughput.

For K walkers, the first addition batch determines the F fallback evaluations.
When F>0, a second batch is needed for the submitted lazy circuit. An eager
full-output implementation has the following arithmetic:

| Card | M coefficient | S coefficient | Inversion remainder |
| --- | ---: | ---: | --- |
| 1 or 3 | 5(K+F) | K+2F | 2(I-3M) |
| 2 | 5(K+F) | K+F | 2(I-3M) |

For F=0 there is one remainder. Preinverting potential fallbacks in advance
instead charges unused denominators; it does not silently remove their cost.
Cards 1/2 need only x to choose an output, so they may retain slopes and defer
the rejected ordinate/sign computation. This reduces their M coefficient to
5K+4F, with the same square counts and paid scratch. Card 3 needs the translated
ordinate for its next doubling. The eager invoice is therefore not a minimum
gate price, and cannot justify a false negative against a better implementation.
All these invoices omit, and must later add, field additions/constants,
comparisons, exceptional dispatch, labels, lookup, memory and reconstruction.

## Why the submitted falsifier is not admitted

- A DP table plus an eight-entry ring cannot census every earlier repeat.
  Such a census needs a paid dictionary or replay algorithm. A solver needs
  its DP predicate, endpoint records, lookup/confirmation, replay, restarts and
  null handling. DP frequency must be evaluated on its actual biased paths.
- A ring/history/label-triggered escape changes the state beyond the point.
  Two visits to the same point with different histories can diverge. Endpoint
  coincidences remain valid equations, but interior meetings need not coalesce
  under the submitted DP detector. Freeze augmented state or prove an adequate
  alternative detector; do not assume point autonomy through an escape.
- Match peak bits including K walkers, 8K history records, fallback scratch,
  jumps and endpoints. The raw 0.19 sqrt(q) boundary was a conditional field-cost
  crossover, not a universal memory threshold. Arbitrary r scalar multiples
  also do not have O(r) setup additions without an explicit cheap construction.
- Specify what seeds randomize. A fixed Q and fixed rules are not independent
  trials; Card 2 has no supplied random parameter. Compare the same measured
  capped statistic and success rate on actual matched controls. Eight candidate
  medians cannot be compared with a heuristic baseline expectation. A failure
  at a cap is censored failure, not a completed solve; price a restart policy.
- A marginal image-concentration parameter lambda does not establish dependent
  trajectory hitting times, useful coefficients or DP delays. The displayed
  lambda-versus-price threshold is only a conditional random-sampling heuristic,
  not a theorem about any of these walks.

[Miller–Venkatesan](https://arxiv.org/pdf/math/0603727), equation (1.1),
Proposition 3.2 and its surrounding discussion, concerns the original
random-partition Pollard graph. Its mixing/collision analysis does not transfer
automatically to these coordinate-dependent compositions or history escapes.
Collision and nondegenerate scalar recovery are separate obligations. The raw
reference to a relevant "Proposition 2" was inaccurate.

## Review and next decision

Proposer: Grok4.7, task
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h046-noncanonical-geometry-grok-20261009-r1`.
Independent mathematics: native Astra /root/h007_additive_relations, completed.
Independent cost/prior art: native Sol /root/h034_c4_implementation, completed;
EFD and Miller–Venkatesan freshly read. Root checked labels, batch arithmetic,
source scope and statistical objections, and alone integrated this record.

No experiment executed, no seeds/results fabricated, H034 consumed cap unchanged.
No Lean claim or Audit addition: these are paper calculations. Validation and
exact check command are recorded in STATE. Next potentially decisive evidence
is a corrected autonomous/replayable solver with matched finite memory and a
credible useful-stopping premise. A dearer gate could still win; the current
report does not demonstrate that premise or justify its proposed census.
