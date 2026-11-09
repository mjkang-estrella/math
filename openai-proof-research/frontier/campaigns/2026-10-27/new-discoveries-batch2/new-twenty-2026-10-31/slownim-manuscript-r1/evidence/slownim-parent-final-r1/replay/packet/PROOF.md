# Proof

Keeping coordinate i decreases total mass by n−1: legality ensures every reduced coordinate was positive. Induction bounds any fuel-limited run by mass/(n−1). With n≥2, mass strictly decreases at each move; fuel mass+1 cannot exhaust. Runs with any two fuel values exceeding the starting mass agree (`run_independent`). Thus `length` is a total representation of the legal terminal play, rather than an unproved truncation.

GM selects the least divisible value if present, otherwise the greatest value; it selects the largest coordinate index attaining that value. At a nonterminal position any zero is unique. Zero is divisible by every ℓ, so GM keeps it. Consequently all coordinates GM reduces are positive. If no zero exists every kept-index choice is legal.

At x=(4,4,5), GM keeps the largest coordinate and the exact coordinate trace is

(4,4,5) → (3,3,5) → (2,3,4) → (1,3,3) → (0,2,3) → (0,1,2) → (0,0,1).

There are 6 moves, so player 0 loses. For C=7 its payoff is −(7−6)=−1.

Change only player 0's strategy: keep coordinate 1 at x, use GM elsewhere. The trace is

(4,4,5) → (3,4,4) → (3,3,3) → (2,2,3) → (1,1,3) → (0,0,3).

There are 5 moves, so player 2 loses and player 0 receives (7−5)/2=1. The predicates in `literal_bridge` certify nonterminality at every preterminal position and precisely the prescribed profile move at every step. The deviation is legal at x and uses globally legal GM everywhere else.

Every legal play from x has length at most floor(13/2)=6. Hence 7 is admissible against every legal profile. Since 1>−1 the profile is not Nash. Instantiating the universal conjecture with this state, these parameters and this admissible C proves its negation.

For the non-vacuity control n=2, terminality implies both coordinates vanish. Every legal move decreases mass by exactly one, so induction proves every profile's length equals the initial mass. Every player's payoff is therefore independent of the profile. No deviation improves it; every profile is Nash, for every initial state, every ℓ≥2, and every rational C.

Proof mechanism: finite traces and lengths use ordinary kernel-checked `decide`, not native evaluation. All other steps use elementary induction, finite-set extrema, integer arithmetic, and exact rational arithmetic. Optional all-n,all-ℓ families and fallback-free witnesses are outside this deliverable.
