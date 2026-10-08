# H020 memory costs: corrected models, no all-budget dominance theorem

2026-10-08. Factory Fable cost review COMPLETED; native Astra independent
correction review COMPLETED; root checked algebra and scope. Raw review retained
in H020-memory-cost-fable-raw.md, original proposal in H020-memory-grok-raw.md.
Exact briefs/IDs in hypotheses/H020-memory-reviews.md. No numerical experiment,
new Lean claim or verified improvement. The shadow card is separately scoped
in H020-shadow-disposition.md.

## Finite field-work ledger

Retain the independently checked H019 expression

    Cx(k,ell)=S+5(ell+1)/(2ell+1)M
                +(ell+1)/(k(2ell+1))*(I-3M).

Thus Cx(8,8)=S+9(37M+I)/136; at I=8M this is S+(405/136)M. The raw
2.45M+S sets I to zero. The limit2.5M+S requires ell growing AND negligible
inversion amortization; k growing with ell=8 leaves45M/17+S. Both reports
must retain finite parameters instead of turning the limit into a benchmark.
Chord extra cost lies in[1/3,2/5] for S/M in[0,1]; the .95 ceiling remains
unsupported. Existing H019 F=3 arithmetic comparison remains scoped and valid.

For the Fable DP model ONLY, put A=5+s, iota=I/M and let D be DP-record
capacity. Its assumed stopping overhead n/theta and choice theta=D/T would
give

    W/T=(1+n/D)*(A+iota/n)
       =A+iota/n+A*n/D+iota/D.

Fable omitted iota/D. The formal continuous minimum is
A*(1+sqrt(iota/(A*D)))². Neither version is a finite-resource theorem: the
stopping law, final record occupancy, integer n and n active walk states are
additional requirements. Even within regular affine arithmetic, exact batch
accounting substitutes A+(iota-3)/n for A+iota/n. Do not publish the raw
small-D multipliers or a claim of the same leading constant at every D>=1.

The b+q/(4b) crossover is for a particular capped listing schedule, under its
uniform-secret and arithmetic assumptions. It does not identify the best
algorithm at every bit budget. Convert abscissa/index records, active states,
DP labels/seeds, setup tables and scratch storage to the same units. The
reported .19sqrt(q) threshold is not an established matched-bit boundary.

## Restart counting needs input-independence

For N affine-labelled points with labels precommitted independently of the
unknown scalar, signed pair equations give fewer than N² candidate scalars
with nonzero recovery coefficient. This bounds uniform-secret coverage of that
specified listed-point scheme. It does NOT bound arbitrary coordinate-adaptive
algorithms merely by counting their realized labels.

If restarts are independent conditional on k, each failed restart costs N,
and p(k) is its success probability, then

    E[failed work]=N*E[1/p(k)-1]
                 >=N*(1/E[p(k)]-1),

with infinite work if p(k)=0 on a positive-mass set. This is a useful scoped
repair. Conditional distributions, adaptively selected restarts and cheap
failed attempts need separate analysis. It is not a proof of constant-factor
dominance at every budget or a lower bound on all low-memory walks.

## Fingerprint compression remains a construction question

Under a specified uniform hash-collision model, B stored fingerprints of t bits
give expected false-verification work B*2^(-t)*C_verify per query. Capping this
at C_giant/(2lambda) requires

    t >= log2(2lambda*B*C_verify/C_giant).

The raw upper-bound direction was reversed. Nevertheless Fable's generic
membership-filter argument does not prove Omega(log q) bits per baby: global
false-positive probability1/log(q) gives only loglog(q) in that argument.
Recovering a matching index is a different task. Stored indices, implicit
bucket bits, bucket directories, reconstruction work and preprocessing all
need an explicit layout and ledger.

A static packed table can plausibly improve constants. Neither a universal
threefold compression ceiling nor the same compression for an arbitrary rho
DP store was established. Applying an existing standard compression equally
to competent baselines is still required. No new specified complete solver
with a supported material gain was supplied, but the entire direction is not
closed by the reviewed bit-count argument.

## Replay and distinguished points

The literal schedule with T/b FULL replays of T points costs T²/b generation
steps. Unequal buckets, early termination and success rates need their own
accounting. This counts that implementation, not every implicit detector.
Noncoalescent equal side keys can share a coordinate-based DP predicate;
under the accepted uniform-key model the event is thinned by theta, not theta².
The expression1+(F-1)*theta further assumes the ordinary useful channel is
retained and the extra useful-event rate has been correctly modeled.

## Decision

Remove both reports' blanket claims that all cards are dominated at every
budget. Retain exact arithmetic, conditional restart/replay costs and the
fingerprint direction correction. No tested or established complete-work gain
emerges, and no defined promising numerical pipeline is ready. No hardware
rates or broad coordinate-aware impossibility claims are inferred. External
constants not independently sourced in these reviews remain unused.
