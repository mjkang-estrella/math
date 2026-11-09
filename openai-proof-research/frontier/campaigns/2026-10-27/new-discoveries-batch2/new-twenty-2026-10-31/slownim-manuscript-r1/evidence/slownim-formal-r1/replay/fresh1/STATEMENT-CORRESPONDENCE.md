# Statement correspondence

MathDB 360653 is the target; 361128 is a duplicate, with no separate credit. The full literal records are preserved in evidence/360653.jsonl and evidence/361128.jsonl. In particular 360653 states:

> A position is a non-negative $n$-vector, players move cyclically, and on each move a player keeps one entry unchanged and decreases each of the other $n-1$ positive entries by $1$.

> The set of $\ell$ GM-strategies forms a uniform Nash equilibrium.

361128 states:

> The set of $\ell$ GM-strategies form a uniform Nash equilibrium.

Both records expressly include the largest-entry completion when no multiple exists. The second record omits the payoff; the primary source supplies it, and our endpoint includes it.

Primary source: Gurvich–Naumova, arXiv:2311.03257v1, main.tex, lines 185–200 and 1106–1148. Excerpts are preserved verbatim in evidence/2311.03257-excerpts.tex. Source rules (original spelling):

> Choose a minimal entry of $x$ which is a multiple of $\ell$. If there are several such entries, take one with the largest index.

> keep the pivotal entry unchanged and reduce the remaining $n-1$ entries by 1.

> provided they are positive.

> If $x$ has at least two non-positive entries, it is called a {\em terminal} position, the game is over, and the player who has to move in $x$ (but cannot) lost

> Choose a large constant $C$; it should be larger than the length of any play from $x^0$.

> Then the loser pays $C-L(P)$ and $\ell-1$ winners share this amount, genning $\frac{C - L(P)}{\ell-1}$ each.

> If a position $x$ has no entries which are multiple of $\ell$, the GM-move in $x$ keeps the lagest entry

> The set of $\ell$ GM-strategies form a (uniform) Nash equilibrium.

The duplicate source arXiv:2312.08382v1 has the identical conjecture at lines 1777–1780, rules at 1744–1775; its rightmost tie-break also applies to maxima. No source permutation or sorted-position abstraction is used in this proof.

| Source symbol/rule | Lean symbol |
| --- | --- |
| nonnegative n-vector x | `Pos n := Fin n → Nat` |
| n ≥ 2, ℓ ≥ 2 | `hn`, `hl` throughout conjecture |
| at least two nonpositive coordinates | `Terminal`, two distinct zero coordinates, equivalent over Nat |
| keep i, reduce the others | `move x i`; `Legal x i` requires positivity before subtraction |
| a legal positional strategy | `Strategy.choose`, with global `Strategy.valid` on every nonterminal state |
| minimum multiple, largest-index tie | `multiples`, `pivotValue`, `pivots`, `gm`; `gm_minimum`, `gm_rightmost` |
| largest-entry fallback | `pivotValue` else branch, `gm_fallback` |
| GM strategies | `GM`, `GMProfile`; globally legal by `gm_legal` |
| length L(P) | `length`, fuel mass+1; `run_independent`, `no_exhaustion` |
| cyclic order, first player 0 | profile selection at `t % l`, initial t=0 |
| terminal player loses | `loser := length % l` |
| exact source transfers | `payoff : Rat`, negative payment for loser, division by ℓ−1 for winners |
| admissible C | `Admissible`, quantified over all legal profiles |
| unilateral Nash condition | `IsNash`, all players and all globally legal positional deviations |
| uniform in initial state | `Conjecture`, universally quantifies x and admissible rational C |
| negation | `SlowNim360653.conjecture1_false : ¬ Conjecture` |

Positional deviations embed into history-dependent ones by applying the positional function to the final position in the history. The GM strategies are positional. Thus finding a profitable positional deviation also refutes Nash for every larger strategy class that includes these deviations. The general play bound follows from the mass decrease of every legal move, independently of strategy choices; a history cannot revisit a state, so any single legal finite history can also be extended to a globally legal positional profile using GM elsewhere. Our admissibility definition uses the explicitly requested all-legal-profile quantifier.

Rational C suffices for refutation of an assertion permitting more general constants: the counterexample uses the integer 7. No assumption of an initially divisible coordinate is imported from the source's dynamical-systems section; the game subsection expressly supplies the no-multiple rule.

The finite witness is n=ℓ=3, x=(4,4,5), C=7. Player 0 keeps coordinate 1 (zero-based) at x and uses GM everywhere else. It is globally legal. `literal_bridge` certifies the actual coordinate traces, their lengths, and payoffs −1 and +1. `seven_admissible` uses the general mass bound, not strategy enumeration. `two_every_profile_nash` is a general non-vacuity control for all x and C with two piles.

Root's ruling permits proceeding with 360653. The sibling DAM 2024 version of record remains unread; this certificate makes no novelty, priority, or acceptance determination. No unqualified minimality claim is made for this witness.
