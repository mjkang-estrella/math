# R162AJ independent substantial-contribution review — round 1

**Assessment: TECHNICAL, conditional on correctness of the entire unchanged frozen theorem.** This is a full-scope contribution assessment. It is not a correctness PASS, acceptance, campaign increment, manuscript, or release. The other review has not been inspected. No author report of completeness, test outcome, inherited reading ledger, or campaign count is used to infer this assessment.

The comparison below pays the full decision theorem by integrating the actual Source104 stochastic gain–bias and threshold operations, the actual CDGO stochastic decomposition, the full GK split/reset/merge transfer, classical finite-MDP occupation and reachability arguments, and the arbitrary-monotone HS acceleration. In particular, it does not infer a contribution from the fact that CDGO writes limsup or that DM requires strict positivity. Those differences are real, but there is a compatible route around them at the theorem's stated, decision-only scope.

The frozen statement and proof have SHA256 respectively `6a73b45333ee99648324171a070cec4fab8613a7af9b8687f87db7d0d31721e4` and `7980d626908175daf46c3326860a10888f26b61a252379e941b34636585a3817`. Both actual files were read, without changing their bytes or modes. The comparison retains every input and strategy quantifier, including threshold equality, possibly infinite memory, behavioral opponents, binary probabilities and priorities without favorable bounds, malformed-input rejection, and the complete quasipolynomial BIT bound.

## 1. Actual operations credited

Here S denotes the stipulated Source104 stochastic paper at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All of its operative proofs are premises, not audited for upstream truth.

* **Stochastic source.** The `discount.tex` proof supplies a common Blackwell positional strategy, a rational gain vector and bias, the gain comparison on controlled edges, the exact chance identities, determinant bit bounds, and an argument against arbitrary behavioral opponents. The `labeling.tex` and `application.tex` proofs supply the deterministic quasipolynomial finite-bit expectation-threshold solver, including nonzero rational separation and exact zero decisions. The gain process argument is stronger than a mere expectation headline.
* **Deterministic ordinary and randomized ordinary companions.** All their main mathematical sections were read: finite-box comparison and clipping, support projections, deterministic translations/reweighting, randomized orientation and its past-measurable comparisons, termination and full bit accounting. Exact values and globally optimal positional strategies, the randomized certifying output and expected-time repetition, energy-credit and tropical consequences are credited as source operations. None is renamed as a joint stochastic-parity theorem.
* **Deterministic parity companion.** Its uniform finite-prefix estimate for one strategy chosen before epsilon, increasing ordinary phases, lower-priority strategy restarts, determinacy/dominion extraction, reduced-precision recursion, and full binary complexity are paid. Its deterministic bounded attractor time does not automatically hold in the stochastic arena; the reduction below supplies the appropriate stochastic operation.
* **CDGO, IST-2013-128 full report and 2014 conference text.** The actual displayed Mean objective is limsup of the full reward average, with threshold >=0. Lemmas 1–3 and their full proofs give ordinary phases, lower-priority continuation and positive attraction at even priorities, and the full odd layer decomposition with eventual residence in a child. The full report's algorithm and Min-strategy proof were read. Its n^{2d}-type recursion is an upper bound for that implementation, not a lower bound against a monotone encoding and HS.
* **GK, arXiv:1401.6575v5, 28 March 2022.** Definitions 2.1–2.9 explicitly permit behavioral, unbounded-memory strategies and bounded Borel payoffs. Theorem 1.1 gives a positional optimum for the maximizing player of a shift-invariant submixing payoff. Sections 4 and 5 were read through the reset construction and the split/merge proof, including projection-law and conditional-payoff arguments. Theorem 6.2 is used with its actual epsilon-zero clause and with the submixing standing hypothesis of Section 6. It lifts an attained one-player optimum through restrictions, merge and reset. It is not merely an epsilon-optimality or finite-memory slogan.
* **HS, arXiv:1907.07020v5, 19 March 2021.** Definitions 3.1, 4.1 and 5.2, Lemma 4.6, Theorem 5.3, Remark 5.4, Lemma 6.2 and Corollary 6.5 were read in the actual proof. They apply to arbitrary monotone finite-lattice equations with a supplied basis and charged function evaluations. The chained-product greatest fixed point already suffices. Neither distributivity of the oracle nor an energy lattice is required.
* **DM, arXiv:2606.19324v1, 17 June 2026.** The whole admitted text, including the full Appendix B proof, was read. Its one-player randomized construction, linear-memory stochastic-game construction, odd layers, stationary-distribution perturbation and stopped-reward/Poisson calculation are genuine stronger operations. The operative even-priority construction uses a strictly positive mean margin (including Claim 17 and the final clock parameter). This is not a direct zero-endpoint finite-memory result. Its general memory-lifting discussion and counterexamples also prohibit a casual claim that randomized memorylessness transfers unchanged. We use all strategies in GK, not such a claim.
* **GZ 2010.** The actual rational multi-discount/Blackwell proof and priority-mean-payoff limit were read. Formula (19) averages at the extremal recurrent priority, not over all original time steps. That theorem is not the frozen conjunction by relabeling. Its strategy/value transfer is credited at its actual scope.

The next sections supply the compatible full reduction. The reduction uses only a small one-player all-prefix argument; it bypasses the need to promote every two-player recursive strategy to the author's stronger CP invariant.

## 2. Normalization, ordinary AS, and positive reachability

Let L be the entire explicit binary input length. Parse a fixed self-delimiting adjacency-list encoding, checking vertex labels, ownership, nonempty outgoing lists, integer and rational syntax, positive denominators, nonnegative probabilities and exact row sums. Reject a malformed encoding while scanning and checking the supplied fields. A binary declared count larger than the data can support is rejected by comparing counts with available input length; it need not cause an exponentially long allocation. Cross-multiplication or common denominators have polynomial bit length since the sum of the input denominator lengths is at most L. Unreduced fractions cause no issue. Delete exactly the zero-probability chance edges after validation. A validated chance row still has a positive edge.

For theta=a/b, b>0, replace w by bw-a. Each new reward has polynomial binary length, and for every infinite play its average is b times the old average minus a. This preserves the non-strict lower-limiting inequality exactly. Sort the distinct priorities and give them strictly increasing, parity-preserving ranks, bounded by 2n. Subtract these from an even number at least their maximum. This turns least-recurring even into greatest-recurring even and bounds the resulting priority d by 2n. Zero, duplicate and enormous binary priorities are included. No probability is rounded.

For sets A,B, make A absorbing success with zero reward and even priority; any forbidden state is absorbing failure with reward -1 and odd priority. Reaching a target has precedence over the safety condition. Finite incoming rewards are irrelevant to the tail. Chance rows are retained, with endpoints redirected as necessary; they are never conditioned on remaining in a set. In a retained subarena every chance row is closed and unchanged.

Let M(A,B) be the AS region for reaching A or staying in B forever with liminf average >=0. There is a deterministic quasipolynomial implementation with at most n+O(1) calls to S:

1. In the boundary game, ask the expectation-threshold solver which states have negative expected pathwise-liminf value.
2. Delete their positive Min attractor and repeat in the complement, until none remain.
3. Return the retained states.

The complement of a positive Min attractor has all Min and positive chance successors retained and a retained choice at each Max state. It is therefore a valid restriction. The true AS region survives: its positive-probability finite continuations must themselves win AS, so it is closed at Min and chance and has staying Max choices. Its winning strategy gives a nonnegative expected liminf. A positive-probability route to a negative-value state followed by a value-bounding Min continuation would create a positive probability of negative payoff, which contradicts AS winning. This argument can use a separate continuation after each finite history; there are only countably many finite histories.

At termination all gains in the retained arena are nonnegative. Here is the complete operative potential payment, including increasing-gain Min edges. Write G for the source gain and psi for its bias. A selected Max edge preserves G and satisfies w+psi_next-psi_current=G_current. Every Min edge has G_next>=G_current; at equal gain its bias inequality is >=G_current. A chance row satisfies E G_next=G_current and E(w+psi_next-psi_current)=G_current. Set

    K=max(0, (psi_i-w_ij-psi_j)/(G_j-G_i) over Min edges with G_j>G_i),
    h=psi+K G-min(psi+K G),    H=max h.

The maximum is over finitely many positive denominators; no positive gain gap is assumed in the theorem. Then w+h_next-h_current is nonnegative pointwise at controlled moves allowed by Max, and has nonnegative conditional expectation at chance moves. Center the latter increments and put zero martingale increment at controlled moves. For every prefix,

    sum_{t<T} w_t >= -H+M_T,       |Delta M_t| <= 2(W+H).                 (2.1)

This is valid against every behavioral opponent, before conditioning on any future event. The martingale strong law yields AS liminf>=0, even when G is zero. The failure sink cannot survive the deletion. This proves the ordinary primitive's safety and endpoint semantics. The source determinant bounds also give polynomial bit lengths for G, psi, K and h, although only finite magnitude is needed for the semantic arguments below. The decision algorithm need not print or compute these potential witnesses separately.

For P(T,B), first compute the greatest safety kernel of B union T, with T absorbing. Within it compute positive Max attraction: some successor at Max, all successors at Min, some positive successor at chance. The rank policy stays in the kernel and hits T within n steps with probability at least p_*^n against every opponent, where p_* is the least positive chance probability (or 1). Opponent randomization cannot reduce this conditional bound. Outside the kernel safety fails on a supported finite path; outside the attractor inside the kernel, Min can avoid the target. This proves the exact P semantics and polynomial bit cost. Both M and P are monotone in both arguments, by the pathwise stopped objectives, not by an unjustified monotonicity assertion about induced games.

## 3. The endpoint comparison in each MDP

Let J_- be the conjunction of max-even parity with liminf average >=0, and J_+ the same conjunction with limsup average >=0. These are different events on arbitrary paths. The following comparison is about optimal probabilities, not pathwise equality or a limit/expectation interchange.

In every finite maximizing MDP, both objectives have the same optimal probability at every state, and this optimum is attained for J_-.

To see this, fix any behavioral policy. Almost surely, the infinitely recurring states and actions of the run form an end component C. Finiteness gives eventual absence of every nonrecurring state/action. Conditional occurrence at repeated trials implies that every positive-probability successor of a recurring chance state/action also recurs. The recurrent directed support is strongly connected. These assertions do not require a stationary policy or any lower bound on its action probabilities.

On a J_+-successful path, the largest priority in C is even. Choose times along which the empirical mean is asymptotically nonnegative, and then a convergent subsequence of empirical edge/action frequencies. The finite-dimensional probability simplex is compact. The flow is balanced because incoming and outgoing empirical counts differ by O(1)/T at each state. Centered chance-transition counts are bounded martingale differences, so their normalized errors tend to zero along the entire sequence, and thus along this selected subsequence too. The limiting flow respects the original chance rows, is supported in C, and has mean reward >=0.

The stationary policy defined by the positive flow coordinates has this balanced flow as a stationary occupation measure. Decompose it into its finitely many recurrent classes. At least one class has mean >=0; otherwise their convex combination would be negative. States of zero flow are immaterial to that decomposition. Strong connectivity and chance closure of C let Max reach the chosen class AS from every state of C, using, for example, a full-support stationary policy on its allowed actions until the class is hit. Then use the class policy. Therefore the ordinary expected mean-payoff value in C is nonnegative everywhere.

Use S's positional ordinary policy in C and its bound (2.1). In round k, take k ordinary steps and then a trial of at most |C| steps using a positive-attractor policy for C's largest-priority states. Every trial has conditional chance at least p_*^{|C|} of success. Infinitely many trials give infinitely many visits to this even priority AS. There are O(sqrt(T))+O(1) trials and ordinary resets up to any time T. Charge at most |C|W for a whole or partial trial and H for each ordinary segment. Predictable pasting of the stopped ordinary martingale increments gives

    total reward through T >= -O(sqrt(T))-O(1)+M_T,

with a fixed finite increment bound. The inequality includes prefixes inside an ordinary phase or a trial. Hence liminf>=0 AS. The strategy is fixed before epsilon or T; it need not have finite memory. There is no strict-positive margin in this construction.

Call an end component good when it has even largest priority and a nonnegative feasible occupation flow. There are finitely many end components, and every J_+-successful run reaches their good union G almost surely by the preceding argument. Conversely, from any vertex of G choose one good component containing it and use the constructed J_- strategy without leaving that component. The maximal reachability probability of G is attained in a finite MDP. Reach G optimally, then select that component strategy. This attains at least the supremal J_+ probability for J_-; the opposite inequality follows from J_- subset J_+. Equality and attainment follow. This proof works in every action restriction and every absorbing-boundary game.

The use of empirical limits is not a favorable stationary-opponent assumption: arbitrary histories determine which end component and flow occur. It is the finite set of possible good components, not a fixed trajectory's frequency convergence, that determines the common reachability target.

## 4. Full GK transfer, and equality of two-player endpoint values

The indicator of J_- is shift-invariant and inverse-submixing. Indeed, for each of two J_--winning words and each epsilon>0, every prefix of length t has reward at least -epsilon t-C_epsilon. A prefix of any shuffle is the union of prefixes of the two words, so the same lower average bound, with the two constants added, holds. Both words appear in infinitely many nonempty blocks; the recurrent-priority set of the shuffle is their union. Its largest priority is the maximum of two even priorities and is even. Thus the complement payoff f=1-1_{J_-} is bounded, Borel, shift-invariant and submixing.

Apply GK with the player maximizing f being the original Min. Theorem 1.1 gives one positional optimal Min strategy, valid uniformly over starts and all original Max strategies. For original Max, use Theorem 6.2 with the family of all action restrictions and the class of all behavioral strategies. That class is closed under the actual reset and merge operations. Section 3 supplies an attained optimum in every fully original-Max-controlled restriction. The epsilon-zero clause therefore gives an attained original-Max optimum in the two-player game. This is the point at which merely citing weak determinacy or epsilon-optimal strategies would have been insufficient.

The full split/merge operation matters. It keeps the child histories along the two action parts at the pivot, uses their induced conditional laws, and handles both infinite projected plays and the eventual use of just one part. Submixing and the subgame-perfect child guarantees control the resulting merged payoff. Reset is then used to restore the required continuation property. These are exactly the operations read in GK Sections 4–6; there is no attempt to replace them with a guessed memoryless randomized lifting rule. For an edge-reward convention one may label the observed transitions, or insert one deterministic edge state per original edge and use doubled edge rewards and zero rewards on the other half-step. Duplicate the source priority on the inserted state. This preserves the average threshold sign and recurrent priorities and puts the game into the finite-color framework of GK. It preserves restrictions and behavioral information.

Let v_-(s) be the value for J_-. For every fixed positional Min policy tau the remaining game is a finite maximizing MDP. Section 3 gives

    sup_sigma P_s^{sigma,tau}(J_+) = sup_sigma P_s^{sigma,tau}(J_-).

Using the positional optimum tau_* for J_-, the two-player lower and upper values for J_+ satisfy

    v_-(s) <= lower_+(s) <= upper_+(s)
           <= sup_sigma P_s^{sigma,tau_*}(J_+)
            = sup_sigma P_s^{sigma,tau_*}(J_-)=v_-(s).                 (4.1)

The first inequality uses J_- subset J_+; it does not assert that a limsup-winning strategy itself wins liminf. Thus both endpoint values are equal. An attained Max optimum for J_- also attains this value for J_+. At value one it provides precisely the required AS strategy. The AS regions for J_+ and J_- therefore coincide, uniformly in all boundary games and restrictions. The same argument with constant even priority gives the ordinary limsup/liminf AS equivalence.

In particular, if a finite child game has no AS-winning state, its values are all <1. A single positional Min optimizer tau_* has a uniform gap eta=min_s(1-v_-(s))>0 against all Max strategies, for J_+ as well as J_-. The gap is used only semantically. It is neither computed nor assumed input-independent.

This is the compatible cancellation of the apparent CDGO endpoint discrepancy: transfer the value/AS region via fixed-opponent MDPs and GK, rather than demanding that CDGO's checkpoint strategy have a lower-limiting payoff. The source all-prefix estimate is needed only in the one-player verification, where sparse bounded trials suffice.

## 5. Monotone boundary equations from the paid decomposition

Define F_j(A,B) using J_+ initially: reach A, or remain in B intersect S_<=j forever and satisfy J_+. By Section 4 this is exactly the author's liminf F_j at every pair of parameters. Put F_-1(A,B)=A. Let D_j be the priority-j set. The paid target/safety form of CDGO's decomposition is

    j even:
    F_j(A,B) = nu Z [ M(A, B intersect Z intersect S_<=j)
                  intersect F_{j-1}(A union (B intersect Z intersect D_j),
                                    B intersect Z) ],                (5.1)

    j odd:
    F_j(A,B) = nu Z mu X [ A
                  union P(X intersect Z, B intersect Z intersect S_<=j)
                  union F_{j-1}(A union (X intersect Z), B intersect Z) ]. (5.2)

All arguments are increasing set expressions. All component functions are monotone, including the boundary F by its semantics. Thus these are genuinely monotone functions of every bound and free variable; no hidden map Z -> answer in an arbitrary induced subgame is asserted monotone. Here are the compatibility details establishing both equations with CDGO's actual operations.

### Even priority

Let W be the true AS region. Retain W with A terminal. Its winning strategy has winning continuations at every positive-probability history, so W has staying Max choices and is closed at Min and chance until A. Ordinary limsup winning in W implies ordinary liminf AS winning in W by the constant-even case of (4.1), hence the M term of (5.1). Stop the original J_+ strategy at A or the first priority-j state. If neither is hit, it is a lower-priority J_+ strategy. This proves that W is a postfixed point of the right-hand side.

Conversely let Z be the greatest fixed point. Every state of Z belongs to both displayed regions, and both strategies stay in Z until the terminal boundary. Play a long finite ordinary phase, followed by a fresh lower-boundary strategy until A or D_j is reached; if D_j is reached start the next round. A lower phase that never ends wins its lower J_+ objective AS. Infinitely many completed rounds give infinitely many visits to the even j.

For mean payoff in the latter case, it is sufficient to pay CDGO's checkpoint guarantee. This can be made explicit without future conditioning. If the current past length is t and this is round k, select a finite integer N=N(k,t) such that

    N >= k(Wt+H+1),     N >= k^2 D^2 2^k,     N >=1,

where (2.1) in the retained Z has increment bound D. Conditional on the current finite history, the ordinary martingale after N further steps has second moment at most D^2 N. Therefore its probability of being below -N/k is at most 2^{-k}. At a checkpoint where this failure does not occur, the accumulated reward is at least -Wt-H-N/k, so its average is >=-2/k (enlarging N or a harmless constant if needed). Charge the failure event only when the round is actually entered; its unconditional probability is still <=2^{-k}. Borel–Cantelli implies that along infinitely many rounds all sufficiently late checkpoints have averages tending to at least zero. The limsup is nonnegative. Hitting A at any time is already success.

The phase duration is selected at a stopping history, and no step conditions on the event of infinitely many future rounds. If a child is followed forever, extend the opponent's behavior at possible controlled exits to a legal child policy. The event of a bad infinite child continuation is included in the null bad event of that child policy. A countable union over entry histories handles all restarts. This supplies the behavioral and conditional-law detail omitted by an informal statement about conditioning on eventual residence. It proves (5.1) for J_+, and (4.1) gives its J_- semantics.

### Odd priority: soundness and layer exhaustion

At an outer fixed point Z, the inner least fixed point X equals Z. In its ascending finite iteration, the P term gives safety until an already admitted target; the F term gives safety until an already admitted target or a lower winning infinite continuation. Transfers to earlier inner iterates strictly lower their finite rank. Hence every admitted state can maintain Z until A. In particular Z is a controlled safety region with A absorbing, and Z outside A lies in B intersect S_<=j.

Within this retained arena, alternate positive-attractor saturation with adjoining the lower-boundary winning set. This has the same least closure as the union in (5.2): the operations are monotone and inflationary on the iterates (the lower term includes the current target); each saturation remains below the least common closed set, and a stable alternating closure is closed under the union.

After saturation at X, put U=Z minus X. Max and chance have no edge from U to X, and Min has a staying edge. Thus U is a chance-closed Max-trap. Outside X the lower-boundary winning region is precisely the lower AS region R in U with priority-j states forbidden. Indeed Min may stay in U; any Min exit to X is already successful. Max and chance cannot make such exits. R is a Min-trap in U, contains no j state, and has its supplied lower AS strategy. Adjoin its positive Max attractor Z_i in U and repeat. Since the least closure is Z, at most n nonempty layers exhaust it. A nonempty A supplies an initial terminal layer. This is CDGO's full odd layer certificate, not only a single child sublemma.

For completeness about eventual residence, fix the rank policies outside the R_i and the child policies inside them. Collapse each R_i to a state with a stop option and its possible exits to earlier layers; omit zero-cost waits inside R_i. This auxiliary finite MDP over-approximates Min's possible future exits even when they depend on an arbitrarily long child history. It has no nonterminal end component: take the least layer index in such a component. The fixed attraction ranks and closure of all supported chance transitions force a path to its r_i; every non-stopping exit from r_i goes to an earlier layer, a contradiction. Thus every policy of the finite active MDP stops AS. The usual universal-reachability rank argument even gives a finite uniform expected number of active steps, <=m p_*^{-m} after adding a stop sink. No polynomial magnitude is claimed.

Consequently the original play has only finitely many active transitions AS, so eventually one child strategy is followed forever. Countable entry-history null-event transfer, without conditioning its law on future non-exit, proves the child's objective and therefore the full objective. No payoff accumulated before that final residence affects a limsup or liminf tail objective. This is the paid odd-layer operation with its precise stochastic compatibility.

### Odd priority: completeness and the conditional-law step

Let W be the true AS region and evaluate the inner least fixed point with Z=W; call it X. It includes A and is positively Max-attractor closed. If U=W minus X is nonempty, it is a chance-closed Max-trap. Min can stay in it, and every state must still be AS winning: the original W-winning Max strategy has no opportunity to leave U against that restriction.

Let C be the positive Min attractor to D_j intersect U, and let Y=U minus C. Y is chance-closed and a Min-trap. There is no lower AS winner in the induced Y, because any such winner could stay in Y and would already appear in the lower term of the stabilized inner closure X. If Y is empty, the Min attractor already forces infinitely many j visits AS. Otherwise Section 4 gives one positional child Min policy with uniform J_+ success bound 1-eta, eta>0, on Y. Combine it with Min's positive-attraction policy on C.

On paths with infinitely many visits to C, choose disjoint trials beginning at successive visits not covered by the previous trial. Each has length at most n and conditional probability at least p_*^n of reaching D_j. Hence infinitely many j visits occur AS on that event and parity fails, since j is the largest priority and is odd.

For paths eventually in Y, write E for full success. At a finite history h in Y, modify Max's continuation only when it would first exit Y, choosing a staying action instead and then any legal staying continuation. This gives a child strategy: Min and chance cannot exit Y, and the events before a Max exit have the identical law. Thus the unmodified event E with no future C visit is included in the child success event of the modified continuation. The uniform child bound yields

    P(E | h) <= 1-eta + P(a future C visit | h).                       (5.3)

This inequality also holds for behavioral Max: implement the replacement as a map on its proposed action distribution, preserving the probabilities of staying histories. For a fixed N and t>=N, the final term is bounded by P(some C visit after N | history through t). Conditional-expectation convergence makes its limit the indicator of that fixed event. On the event of finitely many C visits, choose N after the last one, and then the bound tends to zero. On E, however, P(E | history through t) tends to one by Levy convergence. Equation (5.3) is incompatible with both facts. Success on eventual Y has probability zero. This contradicts U subset W.

Therefore X=W, W is a postfixed point of the outer map, and soundness gives equality. This closes (5.2), including the endpoint and uniform spoiling obligations. We used the actual CDGO decomposition plus finite-state and conditional-law completion, not the slower running time of its original recursion as a barrier.

## 6. Polynomial syntax and the complete bit cost

There is one occurrence of F_{j-1} in each of (5.1) and (5.2). Along the single recursive descent, B only accumulates intersections with fresh Z variables. Its expression has O(d) size. A accumulates at most d unions of terms, each of O(d) size. Even after literal substitution into every level's primitives, the whole formula has O(d^3) size and at most 2(d+1) binders. Variable renaming avoids capture. This is a syntax-tree bound, so it does not assume a circuit-sharing convention or hide exponential expansion.

Introduce one equation variable per binder, replacing its nested occurrence by that variable. Order inner binders before outer binders in HS Definition 3.1. Every resulting right side is a monotone powerset expression using union, intersection, constants, M and P. Ordered evaluation with the inner equation solutions substituted back recovers the nested formula. No quantification over subsets is expanded into a 2^n table.

Use Lattice=P(S), with the n singletons as basis and joins given by union. Let q=O(d+1) be the number of equations and a<=q their alternation parameter. The witness size in HS can safely be bounded by N=nq, even if several variables have the same alternation index. A universal graph for N vertices and O(a) priorities is sufficient. The basis size is n, not nW, a reciprocal probability, or the size of a strategy description.

For explicit construction cost, HS Lemma 6.2's universal-tree operation can be implemented by the standard recursive ordered tree. Round N up to 2^b. At height h, construct U(b,h) by concatenating under one root the child list of U(b-1,h), a middle child U(b,h-1), and another copy of that first list; U(0,h) is a chain and U(b,0) a leaf. Any ordered tree of height h with at most 2^b leaves embeds: split its root's child list at the child crossing the midpoint leaf count, put that child in the middle, and embed the two remaining forests, each with at most 2^{b-1} leaves, in the side lists. If all leaves fit in one side, no middle child is needed. The number of leaves is at most

    2^b binomial(b+h,b),

by the recurrence ell(b,h)<=2 ell(b-1,h)+ell(b,h-1); the number of nodes is at most (h+1) times this. With b=O(log L) and h=O(q)=O(L), this is 2^{O(log^2(L+2))}. Explicit recursive generation is polynomial in the generated size and height.

The ordinary parity-rank conversion used in HS gives the universal graph on these leaves. In a finite even edge-labeled graph, ranks at the odd priorities in descending order are nonincreasing on the corresponding truncated lexicographic tuples, strictly decreasing on an odd edge at that priority. Such ranks are obtained by successively removing the highest even edges and ranking the acyclic condensation across the highest odd edges; a highest odd edge cannot lie on a cycle. There are at most N distinct leaf ranks. Embed their ordered rank tree in U. Put an edge between universal leaves whenever the appropriate truncated comparison holds (strict for odd, non-strict for even). This graph is even: an infinite path with highest recurrent priority odd would eventually have a finite rank prefix decrease strictly infinitely often. It receives the rank homomorphism from every even graph of size at most N. Thus its entire adjacency relation can be generated by comparisons of finite navigation strings, at cost polynomial in its own size, q and string length. This supplies the finite-bit construction detail behind the universal-graph oracle; no nonuniform lookup or unread faster graph oracle is needed.

Now use HS Definition 5.2 and Theorem 5.3. For a subset U of basis x equations x universal vertices and a universal vertex z, each argument to a right side is the union of those singletons connected by an appropriate priority edge to an element of U. Compute these sets by scanning the explicit graph/table. A right-side evaluation then consists of polynomially many bitset operations and M/P calls. Membership of a basis element is one bit test. The monotone chained-product operator has a greatest fixed point computed by descending iteration from the full finite product. Each strict iteration removes at least one product element, so there are at most n q |Z_univ| strict iterations. Even allowing a full graph scan and every equation evaluation for every product vertex in every iteration, the overhead is polynomial in the quasipolynomial product size, hence still quasipolynomial. Recover membership in the designated outer equation by existentially scanning the universal coordinate, as in Theorem 5.3.

Each M call makes O(n) calls to S, on boundary games/restrictions with polynomially many vertices and edges and polynomial binary length. Chance probabilities are the original exact rows or deterministic sinks; no arithmetic with p_*^{-n}, eta, phase counters, or recursive strategy descriptions is part of the algorithm. The transformed integer rewards have polynomial bit length. Thus one M evaluation costs 2^{O(log^2(L+2))}. P and the set operations cost polynomial time. The product of a quasipolynomial number of such evaluations and this quasipolynomial cost is again

    2^{C(log_2(L+2))^2}

for one numerical C after increasing it to cover the finitely many small input lengths. Parsing, exact rational validation, sorting, graph construction, bitset tables, data access and the n output bits are charged. No randomized source solver is used to obtain the claimed deterministic algorithm. A polynomial change between fixed explicit encodings changes only the numerical constant. This pays the entire resource statement, including unrestricted priority count and magnitude and tiny positive probabilities.

## 7. Treatment of the author's stronger invariant and the contribution decision

The author's CP invariant has genuine compatibility work: it strengthens an asymptotic guarantee to a uniform all-prefix martingale lower bound; even rounds pay every stopped child prefix and the O(sqrt(T)) number of resets; odd rounds compensate active excursions by a finite-MDP potential rather than declaring every random excursion bounded. Those steps deserve credit in understanding the proof. They are not separate frozen assertions.

Even if one follows the CP route, the additional payments have available source/classical provenance. The completion h=psi+KG is finite lexicographic scalarization of the source gain–bias inequalities, with all gain-increasing controlled edges included. Predictably selecting a stopped martingale difference from finitely many types preserves zero conditional mean and a uniform finite bound; a controlled exit has zero martingale increment and can be charged W. For the odd active MDP of Section 5, proper finite-state reachability supplies a finite nonnegative Bellman potential V satisfying V>=c+E V_next for every action. Pulling it back constantly on each child yields, with a bounded martingale N,

    active_steps(T) <= H+N_T.

If each child has CP constant at most C_epsilon, at most active_steps(T)+1 child pieces have begun, and their stopped martingales paste. Subtracting (C_epsilon+W)N from their martingale pays the total reset/excursion charge. Zero-cost time inside a child does not change V, even if Min chooses an arbitrarily late exit. This explains the cancellation and uniformity in the submitted CP construction; it is not a claim that all random excursions have a deterministic length bound.

More decisively for the frozen theorem, Sections 3–6 avoid needing the full two-player CP claim. The all-prefix one-player construction verifies GK's actual prerequisite. GK then equates the endpoint winning regions; CDGO's limsup checkpoints and layers supply the monotone semantics; HS supplies acceleration on a polynomial basis with the source oracle fully charged. There is no essential comparison bridge left open in this integrated derivation.

Accordingly the full frozen decision theorem is **TECHNICAL relative to the stipulated source and the actual compatible primary/classical operations read here**. This assessment is not based on finding the same theorem title, on the author using familiar words, on a failed naive reduction, or on the difficulty of the auxiliary proof. It is based on an explicit full payment, including all boundary, attainment, opponent, numerical and complexity obligations. It does not claim literature priority, exhaustive search, that every proof must follow this route, or that every auxiliary strategy invariant has already appeared verbatim in print. The separate correctness review remains uninspected and unassigned here.

## 8. Dependency and reading limits

The source proofs are stipulated true. Primary reading used the exact admitted local text files, not the author's reading ledger or comparison narrative. Actual versions and precise line/byte extents are recorded in this review's own `reads.jsonl` and `READING-LIMITS.md`; selected source blobs were independently checked against the complete 13,223-entry pinned tree. Authentication is not semantic reading.

No optional original-history traversal was performed. No catalogue body was read. Only acceptance-journal bytes [4801,6347) were read; no whole-journal decode or hash occurred. The other review's namespace, brief, status, body and result were not opened or queried. No author FINAL/REPORT/COMPARISON, research notes, prior reading ledger, seal, or primary-access metadata was used for mathematical conclusions. No containing protected namespace was inventoried.

The exact admitted primary texts were reused; no network search/download or PDF render was performed in this review. Thus this is not a fresh publisher/PDF-to-text authentication audit. Displayed text includes extraction artifacts in some formulas and figures. The decisive payoff definitions, theorem scopes and operative equations were readable; this review spells out the needed equations and reductions instead of drawing a conclusion from a figure. HS's application appendix and some bibliography tails were not semantically read. Transitive bibliography sources such as the original universal-tree papers, Martin's determinacy proof, finite-MDP textbooks, and CDGO's older MDP antecedents were not independently fetched or read. GK's proved interface and HS's proved interface are the primary premises; elementary occupation, reachability, martingale and finite-bit construction details actually needed for applicability are supplied above. No separate claimed new result depends on an unverified transitive paper.

Initial tool output truncations in the stochastic labeling proof and CDGO introduction were recovered with targeted reads, as recorded in the limits file. Early text line displays around form feeds differed from raw split-line numbering; the ledger's raw byte ranges are authoritative. No failed access or known false admission occurred among this exact direct selection. This does not establish perfect historical isolation by classification: no such classification was attempted, and the broad inherited guards would coarsely exclude many potentially relevant originals. No exhaustive clearance follows.
