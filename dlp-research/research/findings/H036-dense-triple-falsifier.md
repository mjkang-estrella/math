# H036 dense unweighted triple-sum screen

Status: scoped PAPER key-count falsifier, independently reviewed by Opus;
root corrections to target and precomputation hypotheses are stated below.
Targets the dense specialization of GPT6Sol's cached-pair hyperedge proposal.
No numerical experiment, source import or edit. No statement about all sparse,
weighted or adaptively chosen hypergraphs.

For independent uniform source labels P_i=a_iG+b_iQ, enumerate each sorted
i<j<k once by increasing newest vertex k. Emit x(P_i+P_j+P_k) and
x(P_i+P_j-P_k). Pay for cached pair preparation and all usual recovery/lookup
work. At a complete n-vertex prefix, t=2*choose(n,3)~n³/3 output keys.

A geometric equality of disjoint triples gives a signed coefficient vector
on six sources. Up to global sign there are at most2^5=32 such ±1 patterns per
six-element support. Therefore their distinct nonzero relation count obeys

    N6 <= 32*choose(n,6) ~ (2/45)*n^6 ~ (2/5)*t².

Pairs of overlapping triples have at most five source variables, coefficients
in{-2,-1,0,1,2}, and O(n⁵) distinct candidate forms. A partial last newest-vertex
layer contributes O(n²) outputs and O(n⁵) additional comparisons. Root proposes
the uniform-prefix bound N(t)<=(2/5)*t²+O(t^(5/3)).

For a fixed input scalar k, each nonzero coefficient relation on independent
uniform source points occurs with probability1/q. Union bounding distinct
forms would give

    Pr(first useful hit <= t) <= (2/5)*t²/q + O(t^(5/3)/q).

Integrating only up to sqrt(5q/2), below a3sqrt(q) cap, would then imply

    E[min(T,3sqrt(q))] >= (2/3)*sqrt(5/2)*sqrt(q)-o(sqrt(q)),

whose coefficient is about1.054, larger than H019's2sqrt(2)/3 about0.943.
This needs no independence among collision events and no Poisson approximation.
At the same paired kernel price it would defeat the hoped-for key-count gain
before helper costs, but not prove universal runtime domination under every
memory or machine model.

Review must check structural zero/proportional equations, within-triple pairs,
the partial-prefix estimate, infinity/tangent/direct recoveries, and optional
helper/seed comparisons. If at most O(n²) cached helper outputs are also searched,
their interactions with O(n³) leaves add O(n⁵) relation candidates; they cannot
be assumed absent or free. Any adaptive search beyond this scope needs a new
argument. No helper is an independent new source variable.

NEW Claude Opus5.5 review:
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h036-hyperedge-count-review-opus-20261008-r1`.
Read-only, no runs/imports/edits/children. Main exponent remains the square-root
reference; verified improvement NONE.

## Completed review and root corrections

Opus accepted the32-pattern bound, uniform newest-vertex prefix argument,
nonzero formal collision equations, union-bound integration and O(q^(1/3))
remainder. Raw report retained separately. Root adds essential qualifications:

1. Use a source cap n=Theta(q^(1/6)) with at leastsqrt(5q/2) candidate outputs,
   and no fallback before that prefix unless a counted hit/exception occurs.
   Merely a lower bound on n is insufficient if arbitrary larger source/cache
   searches are allowed. A tiny enumeration that falls back earlier is outside
   this conclusion and needs its complete fallback cost analyzed.
2. For a FIXED target the assertion excludes Q=O: its success is certain, not
   probability1/q. The review's 'every fixed k including0' statement is false.
   The literal solver has no other deterministic early input tests. Averaging
   over uniform FULL-RANGE k including0 restores the same leading lower bound,
   since this one immediate success changes the expectation by onlyO(q^-1/2).
   Additional public-input tests require explicit accounting.
3. Eagerly precomputed helpers are present before small t; they are not all
   bounded by t^(2/3). With O(n²) helper keys, an adequate uniform extra term is
   O((n⁴+n²*t)/q), covering helper/helper and helper/leaf comparisons. Its
   integrated effect is O(q^(1/3)) for the stated n. Optional source/cache/direct
   exceptional relations must be included, not silently excluded.
4. This is a key-count obstruction, not complete-runtime dominance. A runtime
   comparison needs justified entire per-key/table/lifecycle costs, not merely
   the fact that both methods use the same field kernel. The report's wording
   'falls below' smaller baseline key counts is a verbal error: its lower bound
   is larger. No heuristic1.40sqrt(q) mean is accepted.

Under these hypotheses the accepted uniform full-range lower bound is

    E[candidate keys before first terminating hit/exception or exhaustion]
      >= (2/3)*sqrt(5/2)*sqrt(q)-O(q^(1/3)).

Here a null hit that terminates into fallback also ends the candidate phase;
the union bound counts it as a hit even though it supplies no solution. The
full prefix required for the integral exists before exhaustion. Seed/cache
successes and direct exceptional recoveries are covered by the additional
probability terms. Failed/null relations cannot increase useful success rate.
The dense construction therefore fails its proposed improved key-count premise
against the known0.943sqrt(q) reference. Sparse, weighted and adaptive triples
remain untested; no universal hypergraph lower bound follows. No run admitted.
