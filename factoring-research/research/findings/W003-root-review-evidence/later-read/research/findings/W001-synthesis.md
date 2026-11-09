# W001 synthesis and rolling shortlist

Verified new factoring complexity improvement: **NONE**. All six mechanism
reports and the baseline report are complete and their T3 results were consumed.
The 24 cards are a search pool, not 24 validated algorithms. Parent decisions
below preserve the difference between rejection of a concrete construction and
a lower bound on every possible implementation.

## Comparison rules

The [baseline ledger](../hypotheses/W001-baselines.md) separates heuristic
general NFS, rigorous randomized complete factoring, deterministic worst-case
bounds, special families and quantum algorithms. It includes the lower
Coppersmith heuristic NFS constant; ordinary GNFS's 1.923 is not automatically
the best comparison. A deterministic power improvement from N^(1/5) toward
N^(1/6) remains exponential in bit length and does not beat heuristic GNFS
asymptotically. A fast square-congruence generator does not automatically give
a rigorous complete factorer.

## Dispositions across the pool

| Lens / card | Decision | Decisive issue or required new step |
|---|---|---|
| Relations A: forced square ideals | Reject isotropic implementation; reserve shape question | Determinant/coordinate growth cancels the removed norm divisor. |
| Relations B: coprime residual basis | Defer practical study | Same-list square dependencies are preserved, not created; wider admission and matrix costs decide usefulness. |
| Relations C: small-resultant higher-degree elements | H008/H013 stated models closed; H014 primitive accepted | H016 processing, H017 conditional supply obstruction and H018 degree model passed review; H019 finite certificate and H020 count accepted; H021/H024 generation, H025 residual density, H023 scoped geometry/models and H026 exact smooth-supply obstruction accepted. H027/H028 scoped deductions accepted after local repairs. Neither submission supplies a new speedup. |
| Relations D: local parity blocks | Reject generic post-filter | Relation-density loss offsets matrix partition savings. |
| Deterministic A: reuse interval certificates | H012 finite pass retained; scoped cover premise closed | The actual-semiprime Omega(phi(m)*n) per-residue cover obstruction passed its second review. |
| Deterministic B: reverse product tree | Original rejected; H015 simple batching premise closed | Reviewed literal-exponent runs require many groups or large padding; this is not a lower bound for all shared computation. |
| Deterministic C: p² certificate lattice | Reject as specified | Even optimistic determinant balancing retains exponent 1/5. |
| Deterministic D: factorial shift cover | Original construction rejected; H029 changed cover accepted | N=323 is an exact coverage counterexample; leaf separation also missing. H029's input-dependent cover/leaf routine passed review; H030's exact-cubic representation obstruction is accepted and closes that realization. |
| Lifting 1: inverse Taylor patches | H006 relaxation and H011 affine reporter closed | Full-tree Theta(R³) and affine-class Theta(R^(5/2)) costs respectively; a grouped coupled query is still missing. |
| Lifting 2: carry-state merging | Reject carry-only merging | Equal current carry does not imply equal continuation constraints. |
| Lifting 3: unknown residue blocks | Reject simple repackaging | Change of variables restores the same uncertainty; needs an independent useful relation. |
| Lifting 4: 2-adic logarithms | Defer | Linearized multiplication leaves difficult interval preimages and charged decoding. |
| Orders A: raw-bit recurrences | Reject universal n² cutoff | 59/60 registered pairs contradict it; order-multiple reduction remains conditional. |
| Orders B: random-sign sparse Fourier sampling | Reject sparse representation | Aligned diagnostic has broadly spread spectral mass; mixture identity supplies no sampler. |
| Orders C: direct marginal contraction | H010 finite cap failed; reserve | 11-variable bucket exceeds cap 10; 685 cases unstarted. Not an optimal-width or asymptotic lower bound. |
| Orders D: sparse order products | Reject sparse expansion | Before a component order, the polynomial's coefficients are all nonzero there. |
| Algebra A: composite Hasse coefficient | H007 restricted extractor closed | Scoped identity remains; normalized blocks and dense Newton series give no improved extraction cost. |
| Algebra B: quadratic quotient norm/rank | Reject generic success claim | Exact component probabilities do not supply the hoped-for generic amplification. |
| Algebra C: class-group square collisions | Reject uniform birthday version | Needs a new constructible bias after group/relation costs. |
| Algebra D: N+1 norm-one torus | Retain control only | Known p+1-type special-family behavior; no general improvement. |
| Dynamics 1: power-image compression | Retain control only | Exponent-menu acquisition and smoothness constrain it to known special-family behavior. |
| Dynamics 2: shifted-square layers | Reject direct evaluator | Collision gain is purchased by more layer evaluations. |
| Dynamics 3: small-degree isogeny stripping | Reject | Cannot strip rough prime-order components; isogenous curves do not supply fresh curve orders. |
| Dynamics 4: batch ECM coefficient evaluation | H009 sparse-collapse screen rejected | Reduced states stayed dense in all registered later stages; a different final-product algorithm is missing. |

These are decisions from the reports and named subsequent reviews, not an
independent proof audit of every subsidiary lemma. Source reports:
[relations](../hypotheses/W001-relations.md),
[deterministic](../hypotheses/W001-deterministic.md),
[lifting](../hypotheses/W001-lifting.md),
[orders](../hypotheses/W001-orders.md),
[algebra](../hypotheses/W001-algebra.md),
[dynamics](../hypotheses/W001-dynamics.md).

## Selected work

1. **H027: scoped deductions accepted after repairs.** Independent review
   accepted the algebra and literal-output cost obstruction; six clarifications
   and a paid sequential join proof are adopted. No actual useful-yield theorem
   or new survivor. Its proposed next question reaches the existing character
   gap, recorded in the [prior-art check](H027-root-entropy-prior-art.md).
   See [disposition](H027-disposition.md); tasks-H027.json is complete.
2. **H028: scoped polynomial-sharing results accepted.** The known model
   optimum and square-map claims passed review; attempted indices, rejected
   rows and expected-work quantifiers are repaired. No new survivor.
   See [disposition](H028-disposition.md); tasks-H028.json is complete.
3. **H030: exact-block realization closed after review.** Its finite procedure
   costs M^(1/3)*poly(log M); the accepted outer-root obstruction forces
   Omega(M^(1/3)) explicit blocks. The degree/exception consequence requires
   separately materialized dense lists through actual degrees. Three
   cost/notation clarifications are adopted, with no algebraic repair. No
   fast RootProduct or general lower bound is supplied. See
   [disposition](H030-disposition.md); tasks-H030.json is complete.
4. **H031: scoped trial accepted and speedup claim closed after review.**
   The paired-field procedure takes at most two actual roots. Its accepted
   exact success identity includes nonsquare failures but has no positive
   uniform useful-mass bound. L_N[1/3,3+o(1)] is a conservative per-trial upper
   bound, not a successful factoring-time result. Denominator-cleared reduction,
   execution order, variable-size root costs and prior-art distribution scope
   are completed in the corrected report. See [disposition](H031-disposition.md);
   tasks-H031.json is complete and the original submission is preserved.
5. **H026: exact smooth-supply question closed.** Independent review accepted
   the exp(o(ell)) qualifying-input count and balanced-semiprime denominator.
   Most members of that ensemble have no base-smooth residual in their entire
   nonempty low-energy set. This needs no smoothness heuristic; changed bases,
   energies, weight alignment and post-LLL/TN domains remain outside its scope.
   See [disposition](H026-disposition.md).
6. **H023: geometry question closed.** The clustered irreducible family and
   geometry-free H022 counterexample passed review. Its conditional collection
   constants and [binomial comparator](H023-intake.md) describe special-form
   models, with no full factoring improvement.
   See [disposition](H023-disposition.md).
7. **H024/H025: low-energy lattice scope accepted.** The sharper feasible
   cutoff, exact population count and model-qualified optimization costs are
   accepted. The fixed-power small-residual density theorem is accepted,
   with no conclusion for every o(N) window or for smoothness at larger
   residuals. See [H024](H024-disposition.md) and [H025](H025-disposition.md).
8. **H022: conditional model closure accepted.** Its c³=32(1+gamma)/9
   infimum retains explicit geometry, adaptive-yield, expected-work and
   norm-mesh assumptions. See [disposition](H022-disposition.md).
9. **W002: all three scoped reviews and dispositions complete.** Factor-specific
   paired residual products, charged N-dependent relation generation and a
   direct ECM batch-output recurrence each receive one independent researcher.
   The [frozen brief](../hypotheses/W002.md) requires an actual computation and
   full cost, or a scoped closure of the selected realization. Symbolic and
   primary-source work only; no numerical experiment or implementation is
   authorized in this wave. Handles and full prompts are in
   [tasks-W002.json](../tasks-W002.json). Lens A has submitted its e<8K reduction,
   zero-row recovery and concrete interval-envelope search. The latter returns
   known N_0^(1/4) scale, failing the target. Its 557-line independent review
   passed without algebraic repairs; 48 review inputs and 63 delivery entries
   verify. The scoped reductions and factor-or-UNIT program are accepted; its
   dense execution is closed as a speedup. See
   [disposition](W002-residual-disposition.md).
   Lens B's adaptive CFRAC/coprime-base realization supplies a for-every-cap
   period-one failure and finite-list basis extractor, with no complete
   factoring bound. Its 693-line review passed after an exact, narrowed H026
   pair-support proof and a full sequential-access schedule; 69 review snapshots
   and 78 delivery entries verify. See [disposition](W002-adaptive-disposition.md).
   Lens C gives an explicit Ward tensor with
   exponential state, paid extraction and success identities without a useful-
   mass bound. Its 612-line review passed with five domain/access/comparison/
   provenance corrections; 46 review snapshots and 58 delivery entries verify.
   See [disposition](W002-ecm-disposition.md). Original submissions remain
   preserved with historical provisional labels. No experiment or Lean change
   follows, and none supplies a new complete factoring improvement.
10. **W003: Lens A accepted and closed; Lens B and parent-gate reviews live.** The
    [frozen brief](../hypotheses/W003.md) tests actual mixed square-class
    construction from N,R=x^2 mod N without seeing x. The quadratic-lift
    submission has a reviewed real-sign obstruction to both orientations and
    explicit costs/successes of its remaining gcd branches; see
    [Lens A disposition](W003-twisted-disposition.md). Its 667-line review,
    66 input snapshots and 72 delivery entries verify. The single terminology
    correction preserves all quantitative formulas and original evidence.
    The source submission gives a
    Dixon-scale integer twist coupling, with claimed complete expected
    L_N[1/2,3sqrt(2)] cost, and norm/involution/recovery deductions; see
    [Lens B intake](W003-root-priorart-intake.md). Neither supplies a new
    improvement. The coordinator consumed all 511/572 report lines and
    verified 29/19 frozen inputs and 32/54 delivery entries respectively,
    plus 23 Lens B source identities. Originals and submitted snapshots
    are preserved. Lens B remains under independent review. A separate new
    review checks the [parent norm gate](W003-normgate.md), a provisional
    totally positive quadratic generator with an explicit relative norm
    certificate and a paid power-cost construction. Faster modular norm
    costs and rational-row target supply remain unproved in that gate.
    Neither Lens B nor the parent note is accepted yet. See
    [handles](../tasks-W003.json). No numerical experiment or Lean work is selected.

H019's finite implementation and one degree-52 upper-count certificate passed
independent review: nine archived outcomes and all 115 research disks verified.
Its original 1-pass/3-unknown screen remains inconclusive under the unchanged
criterion. See [its disposition](H019-disposition.md).

H020's exact weighted primitive count and scoped exponent <=9/5 passed
independent review without corrections. No experiment or all-input geometry
claim follows. See [its disposition](H020-disposition.md).

H016's integer (B+S)*poly(n) full-exponent construction and restricted
good-prime ideal costs passed review. Sampling, sorted table access, working
memory and unquantified bad-prime supply loss remain explicit.
See [its disposition](H016-disposition.md).
H017's reviewed theorem is conditional on certified root geometry; 30/30
exact-arithmetic checks establish no geometry frequency.
See [its disposition](H017-disposition.md).
H018's original reviewed report is preserved; exact comparison and real
threshold wording were corrected. See [its disposition](H018-disposition.md).

H014's H²*poly(n)+S_all*poly(n) primitive and its bit-cost construction passed
independent review. Its 47/47 finite screen is correctness evidence; eta=.4 is
closed within the stated model and eta=.1 remains only an optimistic 1.89
window. See [its disposition](H014-disposition.md). Useful supply, joint
smoothness, rank and complete factor extraction remain separate obligations.

H012's full-cover obstruction and H015's two restricted batching counts have
passed their independent reviews. See [H012's disposition](H012-disposition.md)
and [H015's disposition](H015-disposition.md) for exact scopes and reopeners.

H013 is complete: its independent review accepts the count and original model
rejection. The coordinator checked the reviewer's threshold-tuning extension,
which excludes all eta in [0,1] at c<=2 within that same full-scan model.
See [its disposition](H013-disposition.md); changed generators remain separate.

H007's normalized transfer route is closed after coordinator review; the dense
series-Newton revision is a correctness reference. H009's reduced-ring screen
rejects sparse-collapse on its sample. Neither is a new factoring speedup.

H027–H031 reviews and coordinator updates are complete; original submissions
remain preserved. H031's reviewed adjacent-rotation trial falls short of its
improvement target. No new experiment, implementation or speedup follows. The parent's
[full-source ECM check](ECM-priorart-li2006-note.md) finds cyclic parameter
reduction already described by Li, with multiplicative curve/scalar-length cost
and explicit success assumptions. It supplies no new final-product primitive.
W002's three scoped dispositions are complete, with all six task handles
terminal. No numerical test has been selected. W003's positive-binomial
construction is accepted at its scoped failure/cost statements and closed as
a speedup. Await the separate Lens B and new parent norm-gate reviews before
adopting their deductions; the parent revision supplies no mixed-target law.

The [CM source gate](CM-priorart-gate.md) identifies scalar-N anomalous-curve
factoring and symbolic class-ring arithmetic as existing special-purpose prior
art. Direct modular class-polynomial construction is also known. A new route
would need paid N-only discriminant selection and useful-factor guarantees;
this check supplies neither and selects no new experiment.

H003 is closed in [its disposition](H003-disposition.md). H004's reduction is
retained but its tested construction is closed in
[its disposition](H004-disposition.md). Neither becomes a speedup by adding a
free implicit-query, cover-construction, or leaf-factorization oracle.
H008, H010 and H011 now have separate coordinator dispositions preserving the
narrow scopes of their rejections. In particular H010's k=2 case is easy by
direct conditioning, despite the chosen dense-bucket representation's failure.

## Next branch if the selected primitives fail

Prefer a materially different mechanism to a larger parameter sweep of a failed
one. W002 tests three such constructive directions; none supplies a new
factoring complexity improvement. An ECM norm recurrence must compute all required correlations;
the ordinary reduced-ring recurrence does not provide the sought saving.
Certificate interval reuse would need a concrete change escaping its reviewed
representation bounds; residual-basis processing is primarily practical.
Do not silently change the user's asymptotic objective to optimize small cases.

Lean now also checks the existing reciprocal-certificate algebra, including
quotient existence and recovery. It does not assume a short cover or refine
the Python experiment. Theorem count is not an algorithmic objective.
