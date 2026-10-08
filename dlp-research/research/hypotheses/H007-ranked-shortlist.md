# H007 synthesis: concrete solver questions, no demonstrated improvement

Independent initial lenses: Claude structured relations, T3 Sol symmetry,
native Astra lattice/carries and additive methods, native Sol fullcost.
Grok collision geometry remains live. Prior-art/fullcost review: T3 Astra;
GRR correctness: native Astra encoding_review. No numerical pilot authorized.

## 1. Corrected GRR-v1 relation solving

Mechanism: explicit quadratic Riemann-Roch norm and symmetric root-squaring
chain, followed by paid rational-root extraction and group verification.
Frozen m5 system and exception policy: H007-grr-v1.md. Restricted to
B=2^k dividing p-1; not a secp256k1 construction or arbitrary-prime extension.
Potential barrier overcome: bounded coordinate decomposition without materializing
all tuples. Under actual useful yield sigma, relation collection costs about
(B/sigma)*C plus setup and dependency solving. At B=q^(1/5) and constant sigma,
need C=B^tau with tau<3/2 for a strict exponent margin, with other work below
sqrt(q). Low degree does not establish that. Memory is actual elimination
matrix/circuit size, not just the count of symbolic equations.

Symmetry, known-log/signed relation recovery and subgroup chains are established
prior art (PKM, Joux-Vitse, Faugere et al., APS); novelty of this exact combination
is unverified. The unsupported assumption is cheap solving INCLUDING empty
targets, rational filtering and rejected exceptions, plus sufficient useful yield.
Next decisive step: freeze an actual solver/order and charged finite family
before a small instrumented algebraic screen. The raw broad F4 campaign has no
demonstrated cap fit. Finite slopes cannot prove an asymptotic exponent.

## 2. Random known-log dictionary, divisor membership without expansion

Mechanism: H(T)=product(T-x(a_iG)); unknown monic quarticF. Impose F|H and
the symmetric summation constraint for R=Q+uG. Extract four roots/signs, recover
k directly from paid known labels. This avoids factor-base linear algebra,
but that saving and symmetric coordinates are known principles.

At B=q^(1/5), adequate coverage gives total setup+(q/B^4)*C(B).
Need setup belowB^(5/2) and C(B)=B^tau,tau<3/2 for an exponent improvement.
Explicitly expanded remainder equations already fail: the highest weighted
part of the cubic remainder coefficient is h_(B-3)(e1,e2,e3,e4).
It contains Theta(B³) monomials with weights1,2,3,4. Their signed multinomial
coefficients are nonzero forp>B; lower-degreeH terms cannot cancel that weight.
Root checked this counting/coefficient argument. Expansion alone exceeds the
chosen setup budget. This is not a bound on unexpanded DAG solvers.

The independent reviewer supplied a coverage argument for iid known scalars:
N=16*choose(B,4) signed distinct-index vectors; each pair collides with
probability1/q. IfJ counts collisions, coverage>=N-J andEJ=choose(N,2)/q.
Thus badcoverage probability<= (N-1)/q before distinct-x conditioning, which
costsO(B²/q). Uniform shifts and capped restart blocks avoid uncontrolled inverse
coverage expectation. Root checked this argument in the stated sparse regime.
It supplies geometric coverage, not successful execution of a capped solver.

Missing operation: actually solve/find-or-finish-empty using a paid unexpanded
DAG below the threshold. 'Bounded sparse elimination' alone does not specify
that algorithm. Hence no generic DAG or elimination infrastructure is funded.
This ranks afterGRR operationally becauseGRR has the more explicit frozen system;
the independent reviewer ranked it first as a broader cost/coverage hypothesis.

## 3. Full scalar-circuit pruning (two oracle variants)

Native CARRY-LP-v1 and T3 Sol's target-conditioned capped-F4 proposal independently
use full-scalar circuit branch search. Deduplicate their search/extraction
framework, while distinguishing LP infeasibility from polynomial certificates.
CARRY-LP-v1 is frozen in H007-carry-lp-v1.md; a local falsezero witness exists,
and independent whole-circuit symbolic review now proves Omega(n) expected
search nodes for this frozen v1 (H007-carry-lp-obstruction.md). No LP pilot.
Its hypothesis is early pruning sufficient to pay for every LP/certificate.
Sol's F4 variant requires a fixed degree/matrix budget and full retained-tree
profile; last-stage uniqueness is not evidence of cheap early pruning.
No scalar-range narrowing. No implementation authorized before symbolic screen.

## Parked and rejected

Additive rich-line, bucket and energy reporters: actual supplied implementations
cost at least the matched square-root scale; a cheap reporter remains missing.
See H007-additive-screen.md. Rational lifts lack cheap dependence construction;
carry-only Coppersmith lacks a suitable explicit lattice/root theorem.
Fullcost cards are known/overlapping or incomplete (H007-fullcost-screen.md).
Raw universal TT/sparse-support extensions and two-coset large-prime cost closures
are not accepted as universal results; no time is allocated to extending them.

Best supported ordinary classical reference: square root with known constants
and charged resources. Verified improvement NONE. No GPU throughput calibration
or new Lean claims. Significant changes to this ranking require a concrete
algorithm/cost argument or a reproducible, scoped experiment.
