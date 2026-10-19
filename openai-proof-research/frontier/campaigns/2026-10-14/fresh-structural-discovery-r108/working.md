# T104AS: full target unresolved

The frozen scope is scope.md, SHA256
314784562d56ff8f515e81c3fc8ec4be42cceb0879650635aad07d5ee6180ed9.
No full algorithm meeting that scope is proved. No nomination or count credit.
The following are author deductions, not independent gates. They do not replace
the target by a bounded-priority, expected-value, limsup, or conditional theorem.

## 1. Exact input operations and numerical subproblem

Write S for the pinned stochastic manuscript, sections introduction, discount,
labeling and application, all read completely; P for the pinned deterministic
parity manuscript, all five substantive sections and history read completely.
S thm:discount supplies one pure positional pair, gain G and bias psi, with:
selected Max edges i->j have G_i=G_j and w+psi_j-psi_i=G_i;
Min edges have G_j>=G_i and the same inequality with >= if gains agree;
chance averages satisfy E G_j=G_i and E(w+psi_j-psi_i)=G_i.
G is the expected pathwise-liminf value. These are stipulated inputs, not
an upstream proof audit. S thm:labeling and its shrinking box solve the
zero-threshold numerical question in full binary quasipolynomial time.
P lem:mp-prefix is pathwise and its thm:labels protects ordinary dominions.

### A bounded-potential certificate when all gains are nonnegative

Suppose G_i>=0 at every state of a finite arena. Fix S's Max policy. Set
W=max_e |w(e)|, B=max_i |psi_i|. If there are distinct gain values let Delta
be their smallest positive separation and a=(W+2B)/Delta; if all gains are
equal put a=0. Define h_i=psi_i+a G_i and O=max h-min h.
For a selected Max edge, w+h_j-h_i=G_i>=0. For a Min edge with equal gains,
the same expression is >=G_i>=0. For a Min edge with increasing gains it is
at least -W-2B+a Delta=0. At chance states its conditional expectation is
G_i>=0. Thus, for every behavioral opponent and its observed-history
filtration, R_t=w(e_t)+h(X_{t+1})-h(X_t) has conditional mean >=0.
The differences D_t=R_t-E(R_t|F_t) form a martingale difference sequence
with |D_t|<=2(W+O). For M_T=sum_{t<T}D_t, telescoping gives, simultaneously
for every integer T>=0,

  sum_{t<T} w(e_t) >= -O + M_T.                                      (1)

Bounded martingale differences have M_T/T ->0 almost surely, for example
by S lem:bounded-martingale-average. Directly: E M_t^2<=K^2 t for
increment bound K, so Chebyshev and summability give M_{j^2}/j^2->0;
the deterministic increment bound fills each gap of at most 2j+1 steps.
Consequently this fixed
policy wins the pathwise liminf mean-payoff condition almost surely.
The constants are finite instance constants, not new polynomial strategy
bounds. This is a direct gain/bias potential construction using source-paid
martingale operations; it is technical support, not a substantial nominee.

This proof is independent of an erroneous inference from nonnegative expected
payoff at a SINGLE start. A chance split to +1 and -1 absorbing rewards has
expected value zero at its splitting state but fails almost-sure nonnegativity.
The all-states premise in (1) is essential.

### Exact almost-sure ordinary mean-payoff oracle (technical)

For a target X, PosAttr_J(X) repeatedly adds a J-state with some successor in
the current set, an opposing state with all successors there, and a chance
state with some POSITIVE-probability successor there. Its complement is a
total restriction closed at J and at chance states. Stage ranks give a
positive hitting probability at least p_min^n in <=n steps under J's rank
policy (remove probability-zero edges first). It is not an almost-sure
reachability operator.

The empty arena returns the empty set immediately. Start U=V. Use S to find negative EXPECTED mean-payoff states X in G[U].
If X is nonempty delete PosAttr_Min^{G[U]}(X); repeat. At most n deletions
occur. If U becomes empty, return it. Otherwise, at termination all gains in
G[U] are nonnegative, so (1) gives an
almost-sure mean-payoff policy in U. The accumulated restriction is closed
at Min and chance states, and Max may stay in it; this is also a policy
in the original arena.

Conversely let D be the original almost-sure winning region for ordinary
mean payoff. It is closed at Min and positive chance transitions and has
winning Max strategies staying inside D: a finite history of positive
probability at a vertex outside D would violate the original almost-sure
guarantee. This argument is unaffected by private behavioral randomization.
If D survives inside U, its winning strategies still work in G[U], so it
misses X. The positive Min attractor misses D by induction on its rank:
no Min successor exits D, no positive chance successor exits D, and at
Max states a retained winning successor remains in D. Thus D survives
all deletions. The final U is exactly D.

Every query is an induced arena of polynomial binary length; no chance
probability is renormalized. There are <=n+1 S calls and polynomial graph
work, hence the oracle has 2^{O(log^2(L+2))} bit complexity. This is the
numerical subproblem of T104AS, NOT its parity conjunction. Standard
qualitative deletion and S already pay the mechanism.

## 2. A stopped-martingale even-priority bridge

We prove a conditional strategy-combination lemma to test whether stochastic
restarts themselves are fatal. They are not. The hypothesis below on lower
priority strategies is explicit and has NOT been established for every
winning lower-priority stochastic subarena in this packet.

A pure strategy has property M if, for each epsilon>0, constants C_epsilon,
K_epsilon<infinity exist, independent of the opponent, such that for every
deterministic history-dependent opponent one can construct an adapted
martingale M with M_0=0, increments bounded by K_epsilon, and simultaneously
almost surely for all finite prefixes of length t,

  weight(prefix) >= -epsilon t-C_epsilon+M_t.                        (2)

The strategy is fixed before epsilon. The martingale and its law may depend
on the opposing strategy. (1) gives M for the source's policy on an all-
nonnegative arena. A deterministic pathwise uniform-prefix certificate is
also an M certificate with zero martingale. Finitely many strategies share
constants by maxima. Independent behavioral opponent seeds may be fixed at
time zero; integrating the deterministic-opponent conclusions then gives
almost-sure claims against arbitrary behavioral opponents. This is not a
simultaneous null set over all opponents.

**Lemma E.** Let a finite stochastic arena H have only priorities >= an even
d, let S_d={v:p(v)=d}, A=PosAttr_Max(S_d), and R=H\A. Suppose all states of H
have nonnegative expected mean payoff and each x in R has a fixed pure
almost-sure conjunction-winning strategy sigma_x IN R with property M.
Then from each state H admits a fixed pure almost-sure conjunction-winning
strategy with property M. All constants may depend on H and the supplied
finite family. S_d is allowed to be empty.

**Proof.** In round j=1,2,... follow the policy from (1) for exactly j edges.
If the current state is x in R, start sigma_x with fresh memory and follow
it while the play stays in R. On exit, or if already in A, follow the Max
positive-attractor policy until the first of: reaching S_d, leaving A, or
n=|H| edges. Then start round j+1. An exit from R can only be chosen by
Min, because R is closed at Max and chance states. Charge its reward as
one separate edge, without applying a subgame inequality to it.

Fix a deterministic opponent. The internal R segment can be extended in R
using arbitrary retained choices after the moment when the ambient opponent
would exit. Until that stopping time it is exactly a legal restricted play.
The M martingale for this extension can therefore be stopped just before
the exit. Patching these stopped differences with the martingale differences
from (1), and putting zero on exit/attractor steps, gives a martingale with
increments bounded by the common maximum. The patch is predictable: with
an opponent seed fixed, the decision to exit is known before its edge; no
future chance outcome is used. There are countably many possible finite
restart histories, so the required martingales may be selected history by
history. This is a proof construction, not an executed strategy subroutine.

For delta>0, every partial or completed round of length t has weight at
least -delta t-B_delta plus its martingale increment, where

  B_delta=O+C_delta+(n+1)W.

The mean phase contributes -O, the internal subgame phase contributes
-delta times its length minus C_delta, and at most n+1 other edges contribute
-(n+1)W. If q rounds have finished by time T, then q(q+1)/2<=T.
Thus all T-prefixes satisfy

  weight >= -delta T-B_delta(1+sqrt(2T))+M_T.

Put delta=epsilon/2 and use
B sqrt(2T)<=epsilon T/2+B^2/epsilon. This proves (2), with constant
B_{epsilon/2}+B_{epsilon/2}^2/epsilon. Strategy choices never use epsilon.
Bounded martingale averages and the countable choices epsilon=1/m prove
liminf mean payoff>=0 almost surely.

If infinitely many rounds complete, infinitely many attractor phases start
in A. Conditional on their starting histories, each has probability at least
eta=p_min^n>0 of visiting S_d before its stopping rule. For any k successive
attempts the conditional probability of missing S_d throughout is at most
(1-eta)^k. After countably many possible initial attempts, this proves
infinitely many visits almost surely on the event of infinitely many rounds.
This argument does NOT assume the attempts are independent or condition a
per-attempt bound on future infinite survival. The least recurring priority
is the even d. If only finitely many rounds complete, the unfinished round
has an infinite R phase; its tail satisfies the subgame conjunction almost
surely. More explicitly couple with the retained-opponent extension until
exit: a losing infinite no-exit path is a losing path for that extended
restricted strategy and has measure zero. A countable union over restart
histories is still null. If S_d is empty, the first R phase is infinite.
These cases prove the conjunction. Integrate over an arbitrary behavioral
opponent's independent private seed. QED.

**Comparison.** The round schedule and square-root overhead calculation are
P lem:combine and its credited Bouyer et al. antecedent. The positive attempt
argument is CDGO2013 Lemma2. The additional bookkeeping here uses stopped
martingale certificates and the gain/bias potential, instead of a pathwise
lower bound that is false for chance games. This is method support only;
its conditional lower-priority M premise is not declared solved by notation.
CDGO's actual displayed limsup proof establishes good endpoints of very long
phases, not (2) at every prefix. Dantam--Mayr2026 Theorem5 is strictly positive
MP>0 and uses a fixed probabilistic clock; that strict slack is unavailable
at this target's zero boundary.

## 3. The bounded-dominion transfer fails in a general family

For every rational 0<p<1, take three states s,g,b, all with reward zero.
At the chance state s go to g with probability p and to b with probability
1-p. Let g and b be Max states with their sole outgoing self-loop. Priorities are p(s)=p(b)=1 and p(g)=2.
There are no strategic choices. The exact conjunction-success probabilities
are p,1,0 at s,g,b. Thus Max's almost-sure winning region is {g}, whereas
Min can make the conjunction fail with positive probability at both s and b.

D={s,b} is a positive Min 'killed dominion': from each of its states there
is positive probability of staying in D forever and violating the conjunction,
even if any exit is treated as an immediate Max win. Nevertheless,
PosAttr_Max({g})={s,g}, which intersects D. Therefore the preservation
implication used in P thm:labels cannot be extended by replacing ordinary
attractors with positive attractors and ordinary Min dominions with positive
Min regions. This is a proved all-p route obstruction, not just a finite
numerical example, and it is not a counterexample to T104AS.

The literal transfer of P's recursion makes an actual wrong decision here.
Its minimum priority is odd, so P=Min,Q=Max. Removing PosAttr_Min({s,b})
leaves R={g}. The first reduced-bound child with Max bound floor(3/2)=1
correctly labels the singleton g for Max. Deleting PosAttr_Max({g}) then
labels s for Max too. The remaining b is labelled Min. The returned Max
set {s,g} is wrong for every 0<p<1. A zero-reward arena already detects the
problem; improving the mean-payoff solver or martingale estimate cannot
repair this recursion.

Using ordinary almost-sure reachability attraction for Max instead gives
ASAttr_Max({g})={g}, so it preserves the positive Min state s. But its
complement {s,b} is not chance-closed: the transition of probability p to g
remains. Dropping it or renormalizing to s->b is a different stochastic game.
The source's induced total-arena and restriction proof no longer applies.

## 4. Second and third routes, and their exact unpaid steps

**Full primary recursion.** CDGO full report Algorithm1 and Theorem1 retain
the asymmetry, using an extra odd-priority nested loop. Substituting the
technical ordinary almost-sure oracle in section1 into its cost recurrence
still leaves the stated factor d n^{2d}. For unrestricted d this analysis
is not quasipolynomial. This is failure of the available bound, not a proof
that every execution actually takes n^{2d} time. Moreover the report uses
limsup mean payoff. Lemma E alone does not establish the missing global
liminf/M invariant, so even an exponential all-liminf algorithm is not claimed
here solely by that substitution.

**Boundary-terminal repair.** A possible replacement keeps original chance
probabilities after AS-attractor deletion and redirects exits to labelled
absorbing terminals. Two distinct issues remain:
(1) A terminal standing for an already certified conjunction winner can be
encoded with even priority and positive reward. A terminal standing merely
for 'the current least-priority attractor has been reached' is NOT yet a
conjunction winner. In particular an even-priority vertex with a forced
negative-reward self-loop loses the mean condition despite being its own
attractor. The corresponding exit-or-return obligation must be carried in
both the numerical test and the strategy proof.
(2) In bounded-dominion recursion the returned labels may be wrong outside
small protected dominions. A recursive Max label is not permission to create
an actual winning terminal. One needs a simultaneous hypothetical-boundary
invariant that preserves every protected strong Max dominion and positive
Min killed dominion, supports extraction after the least-priority test, and
charges all but one full-bound branch to a halving budget. No such invariant
or extraction theorem is proved here. A conditional assertion of it would
be precisely an unpaid bridge.

I attempted strong/weak dominion intersection rules: a positive Min killed
dominion survives restriction closed at Min and chance, and a strong Max
dominion is protected from a disjoint positive Min attractor. Those rules
cover only one direction. Section3 refutes the other direction needed for
the unchanged two-phase proof. Replacing one attractor by AS attraction
forces the terminal problem just described. No amount of parameter retuning
of the source's deterministic n,b_Max,b_Min recurrence proves that interface.

**Remaining gap.** A complete stochastic bounded-dominion or other reduction
with 2^{O(log^2 L)} total bit cost, preserving the non-strict liminf objective
and every behavioral opponent, is missing. Global closure of the stochastic
prefix-certificate induction is also not established here. Neither the source
truth stipulation nor a hash/finite check fills either gap.

## 5. References and exact attribution boundary

* S: OpenAI, *Turn-Based Stochastic Mean-Payoff Games in Deterministic
  Quasipolynomial Time*, pinned October5 manuscript,
  [discount section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Turn-Based-Stochastic-Mean-Payoff-Games-in-Deterministic-Quasipolynomial-Time-October-5-2026/build/build/sections/discount.tex),
  `thm:discount`, `eq:selected-gain-bias`, `eq:chance-gain-bias`,
  `eq:min-gain-bias`, `lem:bounded-martingale-average`; and
  [labeling section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Turn-Based-Stochastic-Mean-Payoff-Games-in-Deterministic-Quasipolynomial-Time-October-5-2026/build/build/sections/labeling.tex),
  `thm:labeling`. The numeric oracle and gain/bias operations are stipulated
  source inputs. They are not newly proved as a contribution here.
* P: OpenAI, *Mean-payoff parity games in quasipolynomial time*, pinned
  October5 manuscript,
  [strategy section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Mean-payoff-parity-games-in-quasipolynomial-time-October-5-2026/build/sections/03-strategies.tex),
  `lem:combine`, `thm:determinacy`, `lem:extract`; and
  [algorithm section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Mean-payoff-parity-games-in-quasipolynomial-time-October-5-2026/build/sections/04-algorithm.tex),
  `thm:labels`. Round overhead and the deterministic recursion are paid.
* Chatterjee, Doyen, Gimbert and Oualhadj,
  [Perfect-Information Stochastic Mean-Payoff Parity Games, full report](https://research-explorer.ista.ac.at/download/5405/5516/IST-2013-128-v1%2B1_full_stoch_mpp.pdf),
  IST-2013-128-v1+1, Lemmas2–3, Algorithm1 and Theorem1. The positive-attractor
  attempts and asymmetric recursion are antecedents. Their limsup objective
  and priority-dependent complexity are not replaced silently.
* Dantam and Mayr,
  [Mean-Payoff-Parity and Lifting Strategies from MDPs to 2-Player Stochastic Games](https://arxiv.org/pdf/2606.19324v1),
  Theorems3 and5, Section4. The strict-positive clock mechanism was compared,
  not imported at the non-strict threshold. Theorem5's full appendix proof
  was not read; no conclusion here assumes it for a different scope.

The ordinary deterministic companion's complete §7 already supplies value
and strategy self-reduction, and I113/I116's G113 chain already extracts
Blackwell policies from the stochastic labeling precision. Those operations
cannot be claimed again as new output strength. Conversely, the support
lemmas here do not provide the missing stochastic extraction/halving theorem.
`source-receipts.json`, `primary-receipts.json` and `reading-limits.md` give
the exact bytes and semantic reading boundary for these comparisons.
