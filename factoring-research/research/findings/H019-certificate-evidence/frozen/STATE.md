# Factoring research checkpoint

Updated: 2026-10-08.

- User focus: **factoring experiments + focused Lean specifications**.
- User authorizes ongoing algorithm research and T3 child agents.
- Research goal: **ACTIVE**. No pause or completion has been requested.
- Verified new algorithmic complexity improvement: **NONE**.
- Environment: complete; Python diagnostics and pinned Lean checks run.
- Best formally checked result: correctness of the exhaustive reference splitter.
  The polynomial-time goals are specifications relative to an abstract machine,
  not existence proofs.
- No recurring schedule, publication, or commits are authorized by this loop.

## Resume here

Three T3 children are active in the latest round:

| Task | Registry | Exclusive output |
|---|---|---|
| H019 frozen exact root-certificate experiment | tasks-H019.json | findings/H019-root-certificate-screen.md |
| H020 discrete linear-tail supply analysis | tasks-H020.json | findings/H020-linear-tail-supply.md |
| H021 exact structured logarithm-lattice generator | tasks-H021.json | findings/H021-structured-lattice-generator.md |

Await automatic completion notifications; use task_status when consuming a
result or revalidating liveness, without a polling loop. Do not duplicate live
work. Follow RESEARCH_TEAM.md for new independent rounds, supplying full prior
context and unresolved objections. The parent owns shared code and checkpoints.

Next action: consume the H019, H020 and H021 handoffs. H016's integer and restricted
good-prime ideal processing, H017's conditional quadratic population theorem
and exact certificate, and H018's fixed-r model derivation all passed independent
review. H018's two local statement fixes were applied with the original report
preserved. Their dispositions below state the accepted scopes; none is a full
factoring improvement.

H019 is preregistered: five controls and four public odd inputs at 4096, 16384,
65536 and 262144 bits, seed 1919, fixed root proposals and exact independent
verification. Its continuation criterion requires both largest cases to obtain
verified count certificates and every control to behave correctly. Preserve
timeouts, unknowns and unstarted cases. Do not tune precision, seeds, input
sizes, root methods or the criterion after outcomes. A single valid count
certificate remains evidence even if the overall criterion is inconclusive.
No semiprime promise or relation-supply frequency estimate follows.

H020 separately asks whether exact discrete geometry also defeats the simpler
linear candidate's optimistic 1.90 envelope. It must keep uniformity, root
cusps, all-input scope and actual useful supply distinct. Any new substantive
theorem or empirical claim requires independent review before acceptance.

H021 is a separate constructive branch from the retained lattice lead. A
single-sum dynamic program may solve the original diagonal-plus-rank-one
integer objective exactly at polynomial rounding scale. It must price
coefficient magnitudes, exponent outputs, low-energy enumeration or sampling,
log precision and cancellation. Exact optimization alone proves no useful
smoothness, rank or factoring gain. This round is analytic; no experiment
or tensor package is authorized. Do not duplicate any of these live tasks.

The parent verified the H016 and H017 review manifests (22 and 21 file checks).
For H018, 12 of 13 current files match; the reviewed report is preserved exactly
in H018-submitted-draft.md and both requested corrections are documented.
Latest ./scripts/check.sh passed 12 Python tests, source screen, Lean build and
axiom audit before this document-only checkpoint. Run it after H019's code
handoff; do not rerun or overwrite frozen experiments.

## Completed broad wave W001

All seven tasks completed and their results were consumed. Exact handles and
completed states are in tasks-W001.json. Six reports supply 24 mechanism cards;
the seventh is a primary-literature baseline ledger.

Read [the synthesis](findings/W001-synthesis.md) for the full disposition table,
shortlist and next branches. A report's mathematical derivation is not
automatically an independently accepted theorem. No candidate has yet supplied
a new end-to-end complexity bound.

The baseline ledger separates heuristic GNFS (including the better cited
Coppersmith constant), rigorous randomized complete factoring, deterministic
N^(1/5)-scale methods, special families and quantum algorithms. Conditional
N^(1/6) deterministic ambitions do not beat heuristic GNFS asymptotically and
are not polynomial in input bit length.

## H003: explicit factor-sum residue sets closed

The independent review accepts the exact local cardinality and uniform
M^(1-o(1)) full-output bound. The known two-list continuation costs
N^(1/4-o(1)) in the stated balanced non-close regime. This is a representation
obstruction, not a factoring or implicit-query lower bound.

[Disposition](findings/H003-disposition.md),
[review](findings/H003-independent-review.md),
[frozen evidence](experiments/H003/result.json).
tasks-H003.json is complete. Reopen only for a new costed implicit primitive.

## H004: reduction retained, tested cover rejected

Both tasks completed; tasks-H004.json records them. The prime-cover reduction
with costed interval products and executable leaf factoring is correct and
implicit in the source framework. Multiplicities must be stripped from original
N. No cheap cover/leaf implementation follows from the reduction itself.

The power-shift cover failed all 14 nominal cases. Its preregistered exponent
repair succeeded only at m=2; all other 339 exponents failed. All 360 cases and
missed primes are retained. Do not expand the shift grid merely to fit examples.

[Disposition](findings/H004-disposition.md),
[reduction review](findings/H004-reduction-review.md),
[construction/evidence links](hypotheses/H004-prime-cover-construction.md).
The frozen preregistration, source and result hashes were rechecked and match.

## H005–H006: small exhaustive-tree relaxation closed

H005 degree-two diagnostic passed its registered finite threshold, but all
intervals contained at most two integers. The parent therefore classified it
inconclusive and strengthened the question; no performance claim was accepted.

H006 uses degree five and constructs valid tangent/secant relaxation witnesses,
expanding only a certified subtree. All 20 registered instances completed.
At K=36 the median visited count is 22,337 and median tree fraction 0.17046.
The rejection threshold was 0.5, so the frozen outcome remains **inconclusive**.
There are many spurious feasible points; their finite counts do not establish
an asymptotic or early-stop factoring lower bound. Failures to certify a node
are unknown, not proofs of infeasibility.

[H005 finding](findings/H005-quadratic-screen.md),
[H006 finding](findings/H006-certified-subtree.md),
[H006 frozen evidence](experiments/H006/result.json).
Source and protocol hashes were rechecked and match. The H006 independent
review completed, replayed all 20 inputs and validated 53,108 certificates.
Its separate mathematical derivation gives Theta(R³) full-tree nodes, uniformly
for the diagnostic boxes and on a broad range of actual clipped boxes. The
coordinator checked the counting and reachability arguments and closed the
proposed R*poly(K) exhaustive-tree route. This is not a Lean theorem or an
early-stop factoring lower bound. Keep the frozen experiment inconclusive.

[Review](findings/H006-independent-review.md),
[disposition](findings/H006-disposition.md). tasks-H006.json is complete.
H011 completed the revised inverse-interval reporting question below;
few possible outputs do not imply cheap enumeration.

## H007–H011: subsequent focused work

H007 completed a concrete scalar-normalized transfer-block construction and
33 exact checks. The coordinator accepted its restricted pole/nonunit
obstructions and cost accounting, with the factor-or-action scope clarified.
Its fast factor-return branch has known N^(1/4) scale; the different series
Newton revision retains dense index-sized storage. Close these fast-extractor
claims; a different coefficient algorithm remains open.
[Disposition](findings/H007-disposition.md); tasks-H007.json is complete.

H008's independent review accepts at most one normalized primitive irreducible
quadratic per embedding when 72*epsilon*H^4<1. The thin-window parameters
eventually satisfy this threshold. The d-row bound does not apply to all
reducibles: they can introduce many new bounded-height linear factors. The
review retains exact common-factor parity conditions, including odd dependency
cosets. Close the thin-root irreducible-population claim, not global resultants
or factoring. [Disposition](findings/H008-disposition.md),
[review](findings/H008-independent-review.md). tasks-H008.json is complete.

H009 is the parent's reduced-ring ECM audit. All 12 configurations completed;
all 684 later stages met the density threshold, rejecting sparse collapse on
the frozen sample. A characteristic-zero generic-density derivation is recorded
as awaiting independent review, not a universal finite-ring lower bound. It
does not establish a faster batch evaluator or a factoring performance claim.
[Finding](findings/H009-reduced-ring.md), [evidence](experiments/H009/result.json).

H010 completed and rejected its frozen dense-bucket cap at N=143, a=35, k=2:
an 11-variable bucket exceeds cap 10; its output factor has only 10 variables.
All 688 statuses remain: 2 completed, 1 rejected, 685 unstarted. The exact
network/cancellation audits passed. This is a finite representation/order
failure, not an asymptotic width lower bound. This case has only 16 input pairs
and can be computed cheaply by conditioning; general conditioning costs 4^k.
Reserve the route until a new large-prefix primitive is supplied.
[Disposition](findings/H010-disposition.md); tasks-H010.json is complete.

H011 supplies a correct affine-lattice reporter but forces Theta(R^(5/2))
explicit classes in the full box. Its sharp second-difference identity prevents
moving the affine formula to shallower classes. The full cost misses the
R^(6/5) target; small output size does not pay for root queries. All 61 frozen
arithmetic cases passed, with 16 modular outputs but no actual factor pairs.
This is a restricted implementation obstruction, not a factoring lower bound.
[Disposition](findings/H011-disposition.md); tasks-H011.json is complete.

## H012–H021: current follow-up mechanisms

H012 implements exact Gauss-generated reciprocal certificates and whole-cell
envelopes, independently cross-checked by quadratic inequalities. All 96 frozen
cases completed with full covers. At 64/128/256 bits, median selected interval
counts were 2/2/4 out of 11/22/43 cells. The finite continuation criterion passed;
the fixed K multiplier 16 may merely buy constant-factor reuse. No semiprime
promise, matched factoring benchmark, or asymptotic cover bound is asserted.
Source/protocol/result hashes are preserved and verified.
[Finding](findings/H012-certificate-reuse.md),
[evidence](experiments/H012/result.json). The first independent review completed:
9,727 certificates, 314,101 coverage decisions, Gauss reconstruction, optimal
cover counts and all registered edge cases passed. All six original/audit
artifact hashes match. The finite result remains a pass of its original screen.

That [review](findings/H012-independent-review.md) also derives a new
Omega(phi(m)*n) full-range per-residue cover obstruction for infinitely many
actual semiprimes under the exact modulus rule, affecting a positive fraction
of unit residues. Axis certificates really have broad low-scale coverage;
the proof instead counts hard residue/scale pairs in an interior band. This
new proof has **passed a second independent review**, including the unit-slope
average, uniform error terms, Brun–Titchmarsh transfer and exact input scope.
The original short-interval source supports constant 4; no repair is needed.
Close the stated full-real-range per-residue compression premise. It does not
bound cross-residue sharing, integer-only coverage, adaptive search, distinct
modular values or factoring generally. [Disposition](findings/H012-disposition.md),
[second review](findings/H012-obstruction-review.md); tasks-H012.json is complete.

The separate [Lean note](findings/H012-formal-invariant.md) records five checked
algebraic theorems: integer evaluation, quotient existence under coprimality,
recovery, its converse for nonzero p, and a nonzero recovery polynomial. These
formalize existing algebra; they neither refine Python nor bound cover/search
cost. The quotient premise is not an arbitrary modular exponent collision.

H013's count poly(d)*(H³*N^(-6/(5d²))+H²), eta=2/5 full-scan model rejection,
and full-height resultant-1 example passed independent review. The coordinator
also checked the reviewer's analytic extension: all eta in [0,1] are excluded
at c<=2 in the same conditional population/smoothness relaxation. Close that
full-scan model. This is not a smooth-survivor or factoring lower bound.
[Disposition](findings/H013-disposition.md),
[review](findings/H013-independent-review.md); tasks-H013.json is complete.

H014 tests a concrete changed generator: coefficient lines
g=a*(X-1)²+beta*X+gamma, exact univariate resultants, real-root isolation of
the two threshold polynomials, and enumeration of accepted integers only.
The proposer supplied a mathematical construction and exact stdlib prototype
at H²*poly(n)+S_all*poly(n), including candidates later rejected by filters.
Its single preregistered validation passed all 47 cases in 3.09 seconds, with
0 failures, timeouts or unstarted cases. These are finite correctness checks,
not density evidence; the six recorded output hashes match. The construction,
explicit polynomial bit envelope, boundary handling and model inequalities are
now accepted after independent review. The review's additional arithmetic/access
ledger supports the conservative Z^30 finite-multitape realization, not a
CPython runtime theorem or Lean refinement. [Report](findings/H014-resultant-enumerator.md),
[evidence](findings/H014-enumerator-results.json),
[disposition](findings/H014-disposition.md); tasks-H014.json is complete.

Under the unchanged joint-smoothness model, eta=.4 still requires
c>=(1024/135)^(1/3), worse than the cited GNFS constants even with the changed
enumeration. At eta=.1, a0=.765, b0=.945, delta=2.1 give upper-population
exponent s=18491/9800 and a strict optimistic envelope 1.89. This is an
inequality witness only: neither actual useful supply nor the assumed joint
law, rank, square roots or proper splitting is established. Naive S*B trial
division raises its sufficient cost envelope to about 2.832; that is not a
lower bound on all smoothness algorithms. H016 separately evaluates batching.

H015 is a distinct parent screen of geometric batching for the deterministic
certificate collision stage. Whole-cell envelope bounds give |u|,|t|=O(sqrt(m)).
A fixed (u,t,v mod m²) family serves only O(sqrt(m)) unit residues. A proposed
stronger extension counts distinct t even after arbitrary u/v merging, then
uses giant-exponent bands near Nt to show exponentially many short runs or
large padding at the actual stride m². Both arguments **passed independent
review** with explicit thresholds and the sharper bridging cutoff
1+ceil((N-98H)/m²). Close polynomially many short literal-exponent runs under
the stated common-whole-cell obligation. They concern literal grouping, not
equal modular values after order identifications, other strides, or every
product algorithm; collectively processing many short runs remains open.
[Initial bound](findings/H015-geometric-family-bound.md),
[short-run extension](findings/H015-short-block-extension.md).
No finite experiment or new Lean proof was needed for these derivations.
[Disposition](findings/H015-disposition.md),
[review](findings/H015-independent-review.md); tasks-H015.json is complete.

H016's [construction](findings/H016-batch-smoothness.md) and
[independent review](findings/H016-independent-review.md) are complete.
Full integer prime-exponent recovery costs (B+S)*poly(n) under polynomial
scalar, payload, log B and log S widths. Restricted good-prime ideal
labels/valuations cost expected S*poly(n), or deterministic (B²+S)*poly(n)
with paid root-table joins. Sampling includes both independently uniform
coefficients of aX+b. Memory is working scratch; retained outputs are additional.
Discarding norms meeting disc(f) has unquantified supply loss. Characters,
rank, square roots and proper splitting remain distinct.
[Disposition](findings/H016-disposition.md); tasks-H016.json is complete.

H017's [conditional supply derivation](findings/H017-resultant-tail-supply.md)
passed [independent review](findings/H017-independent-review.md). Separated
normalized root triples control quadratic coefficients. An exact integer
inequality using certified rational root disks bounds primitive irreducible
tail members by (h_*-1)(2h_*-1)²+k. Under its stated uniform geometry, the
worst permitted large-root fraction gives primitive exponent <=1.521508,
below the modeled required 1.881197; reducibles separately have exponent
<=1.53. These are conditional counts, not an all-input geometry or randomized
field-selection escape theorem. The reviewer passed 30/30 preregistered
arithmetic checks; no root-geometry sample was run in H017.
[Disposition](findings/H017-disposition.md); tasks-H017.json is complete.

H018's [corrected derivation](findings/H018-degree-envelope.md) passed
[independent review](findings/H018-independent-review.md). Its fixed-r
upper-population relaxation has exact optimum
c_*³=64(r-1)[(r+1)+(r-1)eta]/(9r²), increasing in r. The linear r=2,
eta=.8 witness a=1,b=.95,delta=1.4 gives optimistic envelope 1.90.
This is no useful-supply theorem or algorithmic bound. A stronger uniform
homogeneity-based lattice count would close that apparent advantage, but
the count remains unproved. The parent corrected the exact 1.90 comparison
and specified the unfloored real threshold, retaining the original reviewed
bytes in H018-submitted-draft.md. No implementation, experiment or new Lean
theorem. [Disposition](findings/H018-disposition.md); tasks-H018.json complete.

H019's [frozen protocol](hypotheses/H019.md) tests the accepted quadratic
certificate with d-2 certified bounded-root disks and a Rouché dominance
count for the remaining two roots. Approximate roots are proposals only.
One bounded run with exact independent verification is assigned in
tasks-H019.json. Its finite continuation criterion is fixed before outcomes;
no candidate enumeration, factor advice or smoothness-density fitting.

H020's [question](hypotheses/H020.md) seeks a discrete linear-tail supply
theorem for H018's simpler witness, with explicit degree dependence and
N-only certificate conditions. It is a separate analytic task, not an
assumed extension of the quadratic result. tasks-H020.json is live.

H021's [question](hypotheses/H021.md) activates the separate structured-lattice
lead from the [literature follow-up](findings/2026-10-08-literature-followup.md).
The parent rechecked the original one-row logarithm-lattice objective and the
distinction from the paper's reduced-basis binary and perturbed tensor domains.
The proposed exact DP is pseudo-polynomial in numerical coefficients; it can
only give polynomial-in-bit-length work under explicit magnitude bounds.
H021 must construct and cost it, then identify the remaining useful-relation
question and precision tradeoff. tasks-H021.json is live; no experiment run.
Numerical resource fits and GPU implementation gains remain separate from
new complexity bounds.

## Initial environment diagnostic H001

[Finding](findings/H001-initial.md): 156 attempts, including 126 composite
attempts with 122 verified successes and four Fermat event-budget failures.
The remaining 30 attempts were prime/0/1 controls outside the promise. Two seeds
are repeated trials, not extra distinct inputs. Favorable square/close-family
measurements provide no general complexity evidence.

Durable archive:
[H001-initial-run/report.md](findings/H001-initial-run/report.md), raw JSONL,
configuration, exact corpus, hypothesis/source snapshots and hashes. Original
research/runs scratch is not the durable archive. The default algorithms remain
the known trial-division, Fermat and rho baselines.

H002 remains an unregistered broad square-relation placeholder, not a solver.
The public holdout config is not blind evaluation and has not been used here.

## Validation and remaining obligations

Latest ./scripts/check.sh passed all 12 Python tests, the source screen and the
pinned Lean build, including Factoring.Certificates. The new algebraic proofs
use standard propext, Classical.choice and Quot.sound as printed in Audit.lean;
there are no new user axioms or unchecked proof escapes. Closed reference
examples remain kernel checked. No new research mechanism is installed in the
shared solver, and no new complexity proof is asserted.

Still needed for a major result: executable useful primitive, matched baseline,
all-input correctness, uniform complete bit cost, success probability where
needed, and independent critical review. Machine-model refinement is required
before a formal complexity claim, but should not become an infrastructure
project in the absence of a surviving algorithm.

The original blog's polynomial factoring prediction and P=BQP conjecture are
separate. Failed representations do not disprove either existential claim, and
a fast factoring algorithm alone would not establish P=BQP.
