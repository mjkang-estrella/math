# H045 one-residual-point divisor completion screen

2026-10-09 UTC. Native Sol /root/h034_c4_implementation proposed and screened
a concrete alternative to constrained tuple solving. Root independently checked
the scalar relation, probability and cost scope. No new solver card, executable
experiment or Lean claim. Working complete-solver exponent1/2; verified gain NONE.

## Construction and standard group-law content

Let G have odd prime order q, Q=kG, and R=Q+rG. Prescribe four subgroup
anchors A_1,...,A_4 and −R as zeros of a function with pole divisor at most
6(O). If the residual degree-one divisor is (S), the principal-divisor
condition implies

    A_1+A_2+A_3+A_4−R+S=O,
    S=R−sum_i A_i.

This is the familiar group completion, even if represented using interpolation
and fixed-degree factorization. Repeated points, a residual O and lower actual
pole order require divisor multiplicities/exception handling; counting five
ordinary evaluation rows does not automatically enforce prescribed tangencies.
None of those representations makes the final point a free selectable witness.

Root read [Galbraith, Section 7.9, Theorems 7.9.8–7.9.9](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch7.pdf).
The point/divisor-class correspondence and its agreement with the elliptic
group law justify this interpretation. It is prior art, not a new attack.
The following probability calculation is elementary and independently derived;
it does not claim the book proves an ECDLP complexity lower bound.

## Frozen-base sampler and exact success probability

Freeze a set F of B distinct subgroup points, 1<=B<=q, and the anchors before
choosing a fresh uniform scalar r in Z/qZ. Conditional on F and the anchors,
R is uniform and translation by −sum A_i is a bijection. Thus

    Pr[S in F | F, anchors] = B/q.

With fixed anchors and independent fresh blindings, membership trials have
that geometric law and mean q/B. Counting all possible multi-anchor
decompositions does not increase this particular sampler's hit probability.

For explicit known-log anchors A_i=a_i G and matched point S=sG with stored
known s, a hit yields k=s+sum_i a_i−r modulo q, followed by exact verification.
If instead affine labels a_i G+b_i Q and sG+tQ are used, the recovery equation
is (1−sum_i b_i−t)k=s+sum_i a_i−r. A zero coefficient is a null event, not a
successful recovery. Membership probability remains B/q under the stated
independence, but useful success may be smaller. The geometric membership
law must not be silently identified with useful recovery in that variant.

## Optimistic price and narrow verdict

For this one-target cold-start sampler, even assigning only one work unit to
each explicitly constructed base record and one to every membership trial gives

    W_optimistic = B+q/B >= 2sqrt(q).

The inequality follows from (sqrt(B)−sqrt(q/B))²>=0. The normalized units
are an optimistic accounting screen for this specified sampler, not measured
curve work or a universal arithmetic lower bound. Actual costs include base
construction, arbitrary blinding scalar multiplication or paid precomputation,
completion/interpolation, lookup and bytes, exceptions, nulls and verification.
If preprocessing is reused across targets, that is a different amortized
invoice and needs a matched baseline; it cannot be omitted for one target.

The conclusion does not cover anchors selected adaptively after seeing the
fresh R, a different nonuniform proposal with a justified useful-hit law,
implicit nonmaterialized sets, or other coordinate-aware algorithms. Multiple
residual points require their actual joint distribution and extraction method;
the number of possible decompositions is not that distribution.

## Decision and process

No new extraction operation survived the bounded pass. Do not build a generic
interpolation engine or run a synthetic diagnostic around this known completion.
The next conclusion-changing evidence would be a specified different sampler
or selector with paid generation and recovery and a better useful-event law.
No script, import, experiment, edit or child was run by the proposer. Root owns
this record and integration. H034 cap and stopped roles were untouched.
Validation command and result are in STATE; existing Lean checks do not certify
this paper-only calculation. Other independent H045 roles remain active.
