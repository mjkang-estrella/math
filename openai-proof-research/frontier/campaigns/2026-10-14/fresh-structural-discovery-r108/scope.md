# Frozen research target T104AS

Frozen before development of a proposed full algorithm, 2026-10-18 local date.
This is a research target, not an asserted theorem or nomination.

There exist one uniform deterministic Turing machine A and an absolute C>0
such that the following holds for EVERY finite explicitly listed total directed
multigraph with vertex partition Vmax,Vmin,Vchance, integer edge rewards in
binary, nonnegative binary integer vertex priorities, and explicitly listed
rational chance probabilities in binary summing to one at each chance vertex.
Loops, parallel edges, zero probabilities and unreduced probability fractions
are allowed. The empty arena returns the empty set. Let L be the complete
binary encoding length. Both players observe the entire finite history and
may use arbitrary behavioral strategies, including infinite memory and private
randomness. Chance draws use the given conditional distributions.

Within 2^{C (log_2(L+2))^2} bit operations, A outputs EXACTLY the set

  {v : there exists sigma, for every tau,
       P_{v,sigma,tau}(liminf_{T -> infinity} T^{-1} sum_{t<T} w(e_t) >= 0
         AND min{p(x): x occurs infinitely often} is even) = 1}.

Equality at zero is included. All priority counts, probability denominator
sizes and reward magnitudes are unrestricted and charged only by binary input
length. The constant C is independent of all those quantities. The machine
need not output a strategy. No promise gap, positive threshold, bounded
priority count, deterministic/MDP restriction, limsup replacement, expectation
replacement or larger running-time exponent is an acceptable substitute.

Stipulated inputs are the actual statements and proof operations in family104
at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. These solve stochastic expected
liminf mean payoff and deterministic mean-payoff parity separately. The target
requires a stochastic conjunction bridge and its full unrestricted complexity.
Primary and historical deductions are credited, not treated as new inputs by
an unsupported name substitution. Source truth is not being audited.

Selection rationale: the source supplies a full exact numerical solver and
an explicit bounded-dominion recursion; the primary stochastic conjunction
paper supplies positive-attractor decompositions. Thus two substantial engines
are available. Whether their asymmetric stochastic restriction interfaces admit
the source's bounded-dominion amortization is the precise proposed unpaid
operation. This is not a claim that the operation is already proved, nor an
independent significance assessment. I113/I116 already screened this interface;
no freshness is inferred merely from an absence of exact keyword matches.

No gate, count increment, formalization, public upload or publication is claimed.
