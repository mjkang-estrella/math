# DRAFT proof and formal scope

AI-assisted; root review pending.

## 2. A family for every n,l ≥ 3

Theorem. Let n,l ≥ 3, put a = (n − 2)l + 1 and b = (n − 1)l − 1, and start from x⁰ = (a,…,a,b), with n − 1 copies of a. All-GM play has length T = (n − 1)l. If P₀ instead keeps an a on the first move and uses GM thereafter, while every other player uses GM, the length is T − 1. Thus the respective losers are P₀ and Pₗ₋₁, and the GM profile is not Nash for every admissible C.

Proof. We use multisets only to describe values. Keeping either of two equal entries produces the same successor multiset. The least divisible value and the largest fallback value depend only on this multiset, so a rightmost tie cannot affect the value argument. This justifies the following calculation for the literal coordinate rule, without imposing an additional tie-breaking hypothesis.

Initially b − a = l − 2 > 0. The entries have residues 1 and −1 modulo l, neither zero. GM therefore keeps b. Set tᵢ = 1 + (i − 1)l and qᵢ = (n − 1 − i)l. At time tᵢ the all-GM invariant is

Iᵢ = {qᵢ repeated n − i times; qᵢ + l repeated i − 1 times; qᵢ + l − 1},   1 ≤ i ≤ n − 1.

The first move gives I₁. Suppose i ≤ n − 2, write q = qᵢ, and select a q-valued pile as a representative pivot. Here q ≥ l. If that representative is kept for s moves, the other values are q − s (n − i − 1 copies), q + l − s (i − 1 copies), and q + l − 1 − s. For 1 ≤ s < l, none of these is divisible by l except the last value at s = l − 1, when it equals q. Hence GM keeps value q throughout the block. A possible change of representative at that equality has exactly the same multiset effect.

Before each of the l reductions, the smallest potentially reduced entry is at least q − l + 1 ≥ 1. Thus every move is legal; no intermediate state is terminal. After l moves the values are q − l repeated n − i − 1 times, q repeated i times, and q − 1. These are precisely Iᵢ₊₁. This proves the invariant by induction, including blocks with zero multiplicity in one of the displayed groups.

At Iₙ₋₁ the values are {0; l repeated n − 2 times; l − 1}. The zero is unique, and GM keeps it. The entry l − 1 reaches zero after exactly l − 1 further moves; all other reduced entries remain positive until then. The total length is

1 + (n − 2)l + (l − 1) = (n − 1)l = T.

The next player is P₀, who loses. The proof so far uses the largest-entry fallback only on the initial move; later pivots exist throughout. The deviating trajectory, treated next, also has a divisible pivot throughout its blocks. The final phases are included explicitly because a zero is a legal kept entry, but two zeros end play immediately.



## 3. The deviating blocks and a literal witness

Keep an a at the first move. The resulting multiset is {(n − 2)l repeated n − 2 times; (n − 2)l + 1; (n − 1)l − 2}. At the same times tᵢ, the second invariant is

Jᵢ = {qᵢ repeated n − 1 − i times; qᵢ + 1; qᵢ + l − 2; qᵢ + l repeated i − 1 times}.

This holds initially. For i ≤ n − 2 there is at least one fresh q-valued pile and q ≥ l. Keep such a representative. At s moves into a block, the two distinguished piles would have values q + 1 − s and q + l − 2 − s. For 1 ≤ s < l, the former is divisible only at s = 1 and the latter only at s = l − 2, in each case equalling q. When l = 3 these events coincide, so both piles tie the pivot simultaneously. They still have the same value q. Other fresh and previously kept piles have values q − s and q + l − s, respectively, and are not divisible within the block.

It follows inductively that GM always keeps value q. Every tie can be represented as continuing to keep the original representative, since the successor multiset agrees. The positivity bound q − l + 1 ≥ 1 applies to all reduced entries before reduction. At the end of l moves the values are q − l repeated n − 2 − i times, q − l + 1, q − 2, and q repeated i times. This is Jᵢ₊₁, proving the second invariant.

The last boundary is Jₙ₋₁ = {1; l − 2; l repeated n − 2 times}. GM keeps an l. One move yields {0; l − 3; l − 1 repeated n − 3 times; l}. If l = 3, two zeros already make this terminal. Otherwise the zero is unique and is kept for exactly l − 3 more moves until the second distinguished entry vanishes; no other entry vanishes earlier. The length is

1 + (n − 2)l + 1 + (l − 3) = (n − 1)l − 1 = T − 1.

Its terminal player is Pₗ₋₁. Strict mass decrease means that x⁰ cannot recur. Therefore “keep an a at x⁰, use GM elsewhere” is a globally legal positional strategy for P₀ and changes no other player's strategy. The payoff comparison is −(C − T) < 0 < (C − T + 1)/(l − 1). Admissibility makes both strict signs valid. This completes the proof.

For n = l = 3 the family gives (4,4,5). The following are coordinate traces, without sorting between moves. All-GM play is

(4,4,5) → (3,3,5) → (2,3,4) → (1,3,3) → (0,2,3) → (0,1,2) → (0,0,1).

P₀ instead keeps coordinate 1 (zero-based) initially; subsequent moves follow GM:

(4,4,5) → (3,4,4) → (3,3,3) → (2,2,3) → (1,1,3) → (0,0,3).

Mass is 13 and each move removes 2, so every play has length at most 6 and C = 7 is admissible. The displayed lengths are 6 and 5; P₀'s payoffs are −1 and +1. This is an exhibited witness, with no minimality assertion.





## 5. What the formal certificate proves

The reused archive proves the literal negation, not the full parameter family. In namespace SlowNim360653, Pos n is Fin n → Nat, with no sorting abstraction. Terminal means two distinct zero coordinates. Legal x i requires every coordinate other than i to be positive, and move keeps i and subtracts one elsewhere. Although natural subtraction is truncated, Legal prevents an illegal zero reduction. Strategy consists of a positional choice function and a proof of legality at every nonterminal position.

The finite sets multiples, pivotValue and pivots define gm by the minimum divisible value, or the maximum value when there is no multiple, followed by maximum index. The lemmas gm_minimum, gm_rightmost and gm_fallback identify these rules; gm_legal makes GM a valid Strategy. GMProfile assigns it to every player. Thus legality is part of the formal strategy type, rather than a premise omitted from evaluation.

The total run is defined with Nat.rec on fuel. A terminal state contributes zero further moves; otherwise the player at t mod l chooses and the recursor continues at t + 1. The mass-decrease theorem gives run_bound. The theorem run_independent identifies any two fuel values strictly exceeding the initial mass, and no_exhaustion certifies termination before fuel can run out. The function length uses fuel mass + 1 and initial time zero. Its value is therefore the legal play length, not an unsupported truncation. The terminal loser is length mod l. The rational payoff is precisely the source transfer, and Admissible quantifies over every legal profile at the same initial state.

IsNash says that no player can increase its payoff by replacing its own strategy with any other valid positional strategy. This suffices for refutation of the unrestricted claim: positional deviations are also history-dependent deviations. Conversely, for admissibility, every legal play can be implemented by a positional profile, because mass strictly decreases and a position cannot recur. Specify the chosen move at each state on that play and use legal GM elsewhere. Hence the formal all-profile length bound covers every legal play, even if one initially permits history dependence.

Conjecture quantifies over n ≥ 2, l ≥ 2, all initial states and every admissible rational C. Restricting C to rationals does not weaken the refutation of a claim allowing real constants, since the witness uses the integer 7. The endpoint is

SlowNim360653.conjecture1_false : ¬ SlowNim360653.Conjecture.

The literal_bridge certifies the two actual coordinate plays from (4,4,5), their lengths and payoffs; seven_admissible derives admissibility from length_bound. The control two_every_profile_nash concerns n = 2, not l = 2: every legal profile is Nash. Indeed each move removes one unit of mass and terminality means both piles are zero, so every profile has the same length and payoffs. This is a non-vacuity check, distinct from [GMMV].

The archive's mathematical modules are Basic, Play, Witness, Control and Certificates, with Audit inspecting the environment. The supplied root replay reports successful strict builds and explicit leanchecker checks for every module. The endpoint's reported transitive axioms are propext, Classical.choice and Quot.sound. The metadata and source audits report no prohibited proof device; the finite witness uses ordinary kernel-checked decide, not native_decide. These are inherited replay reports, not a new replay in this manuscript lane. Here the archive was copied byte-identically, hash-checked and safely extracted without executing Lean, lake or leanchecker. The complete family and the robust computation remain outside the formalized scope.

---PAGE---

