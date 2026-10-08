# H018 sparse-recurrence diagnostic admission record

Status: independent static review completed; root authorized ONE numerical
execution under the amended freeze. No measurement existed at authorization;
no verified ECDLP improvement. This is a specific
bounded falsifier, not a growing benchmark programme or generic infrastructure.

Proposer/implementer: native Astra `/root/h007_additive_relations`.
Independent protocol reviewer: native Sol `/root/h010_early_dependencies`.
Root owns shared integration and execution decisions. Initial protocol is
hypotheses/H018-bm-probe-v1.md; implementation ownership is solely
experiments/H018/bm_probe.py. No off-ledger curve search or numerical self-test.

## What could this test change?

The H017 Factory proposal assumes that a cheap public Fq-valued coordinate
feature has sparse dependence on the unknown scalar. Geometric sampling
converts this exact hypothesis into a linear-recurrence condition. A prefix
of minimal recurrence degree at least64 rules out fewer than64 nonzero powers
for that feature on the admitted curve/generator. This tests all exponent
sets of that bounded size, unlike the earlier individual character probes.
It does not establish an asymptotic lower bound, randomness or solver cost.
Failure to reach64 is unresolved, not a global sparsity discovery.

The original three-curve T128 proposal had no defensible complete ledger.
The reviewed preflight proposes one paid fixture near q8192, threshold64 and
at most128 shared samples. Its paper reservation945320 events is conditional
on an implementation audit, not measured fit. All failed fixture and primitive-
element searches are charged, and exhaustion is inconclusive. This is worth
one bounded admission review despite no positive sparsity mechanism; there is
no automatic escalation, feature sweep or decoder implementation.

## Root mathematical checks before implementation

The proposed interval [8011,8373] contains all Hasse-allowed group orders for
p8191. After certifying nonsingularity, p and q prime, an affine nonzero G,
and [q]G=O, Lagrange plus2q>8373 forces full order q. No full scalar inverse
table or uncharged point count is needed. Correct point formulas and the paid
verification are still implementation obligations, not assumed observations.
Independent Sol review caught admission of q=p=8191; root excluded this
known anomalous family BEFORE implementation execution and informed the writer.
It also required distinguishing finite recurrence length L from polynomial
degree, and accounting for shifted BM writes through index128. Both corrections
are now explicit in the protocol; the original optimistic storage wording is
not an accepted implementation bound.
Sol also noted that b=2 has rational2-torsion (-1,0), so its full group cannot
have odd prime order. Root froze a charged x=-1 root check before point/order
search; this avoids known wasted scalar tests without changing the candidate
family or maximum search count. No numerical observation motivated the filter.

The primitive-root criterion requires complete factorization of q-1 and tests
for every distinct prime divisor. The bounded search may fail; no successful
fixture or small primitive root is presumed. The four proposed curves and
candidate orders cannot be reordered after observing feature outputs.

The feature parities give useful interpretation checks. On nonzero points,
centered x and kappa are even under P↦-P, while centered y and the centered
coordinate-field formal parameter -x/y are odd. Thus their unique scalar-
field polynomial expansions on Fq* use respectively even or odd exponents.
Proof: substitute -n and compare unique degree≤q-2 expansions, using q odd.
This limits support to (q-1)/2 possible exponents, far above64; it neither
predicts low complexity nor invalidates the bounded exclusion. Full odd prime
order excludes y=0 in the sampled nonzero orbit; O still has a declared value.

The prefix-to-global implication is one-way. A full sequence recurrence fits
every prefix, so a correctly computed prefix minimum is a lower bound for
global complexity. Over Fq, X^(q-1)-1 splits with distinct roots; the global
minimal recurrence counts the nonzero monomials in the unique scalar-field
expansion. An implementation must compute the finite-prefix minimum rather
than merely exhibit a recurrence or infer a minimum from a plausible trace.

## Sources and independent-review gates

Root inspected the [Explicit-Formulas Database Jacobian page](https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html).
Its coordinates use x=X/Z², y=Y/Z³ and it gives general short-Weierstrass
formulas. Published M/S counts omit some operations in this protocol's RAM
ledger; additions, constants, comparisons and exceptional branches must still
be charged. The frozen curve has a=1, so specialized a=0 or a=-3 formulas
cannot be imported. No runtime is inferred from those operation counts.

The event convention is explicitly bounded-word modular RAM, not H014's
separate arithmetic/reduction convention or machine instructions. Report the
difference; do not compare totals as hardware speed or change units silently.
Root requested independent review of per-step64-event, scalar1840-event and
BM400000-event ceilings, copying and trace costs, controls and cap enforcement.
Numerical execution awaits the concrete implementation and this review.

Implementation is now present, still unexecuted. Root inspected the source:
general-a formulas retain Z^4, scalar multiplication skips redundant leading-bit
work, q=p and the rational2-torsion prefilter are explicit, and BM stores L
separately with129-slot connection buffers and committed-update traces.
These source observations do not substitute for independent code/cost review.
A requested NEW native gpt-6.1-sol static code reviewer failed to spawn with
`agent thread limit reached`; that model did not run. Root will reuse an
existing native reviewer after its distinct current review completes, rather
than pretend the nominal active-slot capacity guarantees another thread.

NEW Sol static code review independently confirmed root/writer's feature
bound33665 and derived a controls bound34394. It corrected the BM core bound
399425 to399426 for the extra outer-loop comparison. Root explicitly amended
feature/control reservations from30000/25000 to35000 each, total960320, BEFORE
any numerical run. This consumes15000 of the original reserve; the global cap,
event unit, parameter set and stopping rule stay fixed. No hidden work or
unobserved performance estimate is substituted for these static counts.

Sol's final static review returned GO, including selection/primitive-phase
margins and interrupted-update status. Root accepted one execution. The reviewer
noted final stdout transport is not interruptibly limited internally; root froze
an external `timeout --signal=KILL 60s` guard. Timeout/partial JSON is inconclusive.
Source AST parse passed without import/execution. All preflight work was static;
there was no fixture discovery, numerical warmup or control run before the one
authorized diagnostic. Actual command/result/hash will be recorded separately.

Root suggested a separate paid character-table/finite-difference point counter;
the proposer instead froze the Hasse certificate route above. The alternative
was not run and is not a fallback that may be activated after failure.
