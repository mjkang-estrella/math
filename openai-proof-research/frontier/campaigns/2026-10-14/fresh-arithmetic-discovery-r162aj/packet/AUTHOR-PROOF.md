# Author proof: almost-sure stochastic mean-payoff parity in quasipolynomial bit time

This is an author proof for the immutable statement in STATEMENT.md, not an independent correctness or contribution review. The numerical input length is always the complete binary length. No strategy is an output of the claimed algorithm.

## Dependencies and the operation to be justified

Use the stipulated Source104 stochastic expectation-threshold algorithm and its operative discounted gain–bias proof, denoted S. Use the finite-lattice universal-graph construction of Hausmann–Schroeder, *Quasipolynomial Computation of Nested Fixpoints*, arXiv:1907.07020v5, Definitions 3.1, 4.1, 5.2, Theorem 5.3 and Corollary 6.5, denoted HS. Use Gimbert–Kelmendi, *Submixing and Shift-invariant Stochastic Games*, arXiv:1401.6575v5, Theorem 1.1, Section 5's split/merge proof, and Theorem 6.2 including its epsilon-zero clause, denoted GK. Classical finite-state Markov-chain occupation laws, finite-MDP reachability, bounded-increment martingale strong laws, and finite-dimensional rational linear algebra are also used.

The Source104 deterministic parity algorithm and randomized ordinary algorithm are stronger paid comparisons, not premises falsely relabeled as stochastic-parity algorithms. The primary CDGO 2013 full report/2014 conference paper supplies the layered decomposition viewpoint; its displayed mean objective is limsup. Dantam–Mayr 2026 supplies stronger finite-memory operations for the strict-positive liminf objective, but not the zero endpoint used below. Gimbert–Zielonka 2010 priority mean payoff averages only at the recurrent extremal priority, so its multi-discount theorem is not the conjunction here.

The proposed additional operation is an explicit monotone target/safety formulation of the *joint* stochastic zero-endpoint objective, together with a restart-compatible proof of its semantics. Once that formulation is established, HS pays the acceleration. Neither an extra nested loop nor failure of a naive dominion substitution is treated as a lower bound. Contribution and prior-art sufficiency remain for separate review.

## 1. Conventions and normalization

A finite arena has nonempty outgoing sets. At Max and Min vertices the corresponding player chooses an edge; at chance vertices the fixed rational distribution chooses it. Delete zero-probability chance edges after exact validation. Let W be the maximum absolute reward, enlarged to at least one. Write p_* for the least positive chance probability, or 1 when no genuine chance choice occurs. There is no input-independent lower bound on p_*.

We work internally with maximum-recurring-priority even and threshold zero. If the input threshold is a/b, b>0, replace each reward w by bw-a. The pathwise liminf inequality is equivalent, and all resulting integer lengths are polynomial in the original input length. Sort distinct priorities and replace them by strictly increasing integers with the same respective parities, using at most 2n values. Subtract these numbers from a common even integer at least their maximum. This reverses minimum to maximum and preserves parity. Thus the numerical maximum priority d is at most 2n, regardless of the original binary magnitudes. Sorting, the substitution, and validation take polynomial bit time. Original probabilities are not rounded or bounded away from zero.

Let S be the resulting vertex set and D_j its priority-j vertices; write S_<=j for their union up to j. For A,B subsets of S define F_j(A,B) as the almost-sure winning region for the following stopped objective. Reaching A is immediate success. Before that time, every visited vertex must lie in B intersect S_<=j. If A is never reached, the path must have liminf mean payoff at least zero and maximum recurring priority even. Starting in A succeeds; a different invalid initial vertex fails. Rewards on a finite path to A do not affect success.

These boundary objectives are represented by ordinary games: make A absorbing with reward zero and even priority, and replace each forbidden state by an absorbing losing state with reward -1 and odd priority. Transitions into these states retain their finite original reward, which is immaterial to the tail outcome. In particular F_j is monotone separately in A and B. No chance row is conditioned or renormalized. Put F_-1(A,B)=A.

The desired answer is F_d(empty,S).

## 2. Two monotone primitives

Let M(A,B) be the corresponding almost-sure objective “reach A, or stay in B forever with liminf mean payoff >=0”, without parity. Let P(T,B) consist of the vertices from which Max can stay in B until T on every supported path and force a positive probability of reaching T against every opponent. The successful target itself is included in both primitives. Both maps are monotone in both set arguments.

P is computable in polynomial time. Make T absorbing; find the greatest controlled safety kernel in B union T, with all Min and all positive chance edges retained and with Max choosing a staying edge. In that kernel compute the positive Max attractor of T: Max needs some successor in the current set, Min all successors, and chance some positive-probability successor. Outside T the chosen Max edges remain in the kernel. The rank policy gives success probability at least p_*^n in at most n steps from each attractor state. Conversely, a state outside the kernel cannot maintain safety; within the kernel but outside the attractor, Min can avoid T and chance has no supported edge into the attractor. This proves the stated semantics, including uniformity against behavioral opponents.

M is computable with at most n+O(1) calls to S on polynomial-size games. Use the boundary game with A a zero-reward absorbing success and forbidden states a negative-reward absorbing failure. In the current retained subarena compute S's expected pathwise-liminf values only to distinguish negative values from nonnegative ones. Delete the positive Min attractor of the negative-value states; repeat until no such state remains. A deletion leaves a valid subarena: its complement is closed under all Min and chance edges and admits a staying Max edge. There is no numerical tolerance at zero.

For completeness, the true AS region is closed under Min and chance and has a staying Max strategy, since a finite positive-probability prefix to a state without an AS continuation would contradict the original AS property. Its strategy ensures a nonnegative expected payoff, so none of it lies in a negative-value set. It cannot meet that set's positive Min attractor either: a positive-probability route to a negative expected-value state gives a positive probability of a negative payoff under a suitable continuation. Thus the AS region survives all deletions.

For soundness, at termination all expected gains are nonnegative. The following stronger operative consequence of S provides an AS strategy. The failure sink has negative gain, so it has already been removed. This proves safety as well. The number of calls is linear in the vertex count, each has polynomial input length, and S's stipulated bit bound makes M quasipolynomial in full input length.

## 3. The completed gain–bias potential

In an arena where all gains G_i are nonnegative, S's common Blackwell positional Max strategy and its rational bias psi have these properties:

* On a selected Max edge i→j, G_j=G_i and w_ij+psi_j-psi_i=G_i.
* On every Min edge, G_j>=G_i; if equality holds, w_ij+psi_j-psi_i>=G_i.
* At a chance vertex, E(G_next-G_i)=0 and E(w+psi_next-psi_i)=G_i.

Let K be zero or the largest positive number among

(psi_i-w_ij-psi_j)/(G_j-G_i)

on Min edges with G_j>G_i. Set h=psi+KG and subtract its minimum. Then 0<=h<=H for a finite H, and w+h_next-h_i is nonnegative on each controlled transition allowed by the strategy and has nonnegative conditional expectation at chance vertices. This handles gain-zero endpoints; no strictly positive drift is asserted.

At controlled transitions use martingale increment zero. At chance transitions subtract the conditional expectation of w+h_next-h_i. The resulting martingale M has increments bounded by 2(W+H), and every finite prefix satisfies

sum_(t<T) w_t >= -H+M_T.                                      (3.1)

S's rational determinant bounds give polynomial bit lengths for G, psi, K and h. Their magnitudes need not be polynomial. The semantic proof needs only finiteness, but it does not confuse bit length and magnitude.

All inequalities hold before conditioning on any future event. Stopping and restarting at controlled exits is harmless: the excluded exit transition has martingale increment zero, and may be charged separately by W. Chance distributions in the retained subgames are unchanged and chance cannot make such an excluded exit. Predictably pasting finitely many types of these martingale differences preserves their boundedness and conditional mean zero, even against private, history-dependent opponent randomization.

## 4. An attainment and spoiling interface

We need the following classical consequence at the zero endpoint: in every finite stochastic mean-payoff-parity game, both optimal strategies exist, and Min has a positional optimal strategy for minimizing the conjunction's probability. In particular, if a finite subgame has no AS-winning vertex, there is one Min strategy and one eta>0 such that, from every vertex and against every Max strategy, success probability is at most 1-eta.

Here is how the actual GK interfaces apply. The indicator of the conjunction is shift-invariant and inverse-submixing. If two bounded-reward words each have nonnegative liminf average, a prefix of their shuffle is a union of two prefixes, each with total reward at least -epsilon times its length minus a constant; the shuffled liminf is therefore nonnegative. The maximum recurrent priority of a shuffle of two parity-winning words is the maximum of their two even recurrent maxima. Complementing the indicator gives a bounded shift-invariant submixing payoff. GK Theorem 1.1 thus supplies a positional optimum for the player maximizing that complement, namely Min.

For the other player, apply GK Theorem 6.2 to the class of all strategies, which is closed under the actual merge and reset operations. Its epsilon-zero clause requires optimal strategies in all one-player restrictions. We verify this requirement rather than inferring attainment from weak determinacy.

In a finite maximizing MDP, almost every run eventually stays in the end component consisting of its infinitely recurring states/actions. Chance closure follows from the positive probabilities and the conditional occurrence law. On a successful run this component C has even maximal priority and supports a balanced occupation flow with nonnegative average reward: take a convergent subsequence of empirical edge frequencies and use the martingale law for chance frequencies. Hence some stationary recurrent class supported in C has nonnegative average reward. Because C is an end component, its controller can almost surely reach that class from every state of C. Consequently the ordinary expected mean-payoff value is nonnegative throughout C. By (3.1) an ordinary strategy there has the uniform prefix bound. Also every state of C is in the positive attractor of its maximal-priority set, by strong connectivity.

A pure strategy alternating j ordinary steps in round j with an at-most-|C|-step positive-attraction trial wins the conjunction almost surely. There are O(sqrt(T)) trials by time T, so (3.1), the bounded trial losses, and the martingale strong law give the liminf inequality at every time. Each trial has conditional success probability at least p_*^|C|; infinitely many trials yield infinitely many maximal even visits almost surely. Thus every such good C has an AS strategy, including when its optimum mean is exactly zero.

There are finitely many end components. Let G be the union of the good ones. Every successful run reaches G, and an optimal reachability strategy to G followed by one of the just constructed strategies achieves exactly the maximal probability of reaching G. Finite-MDP reachability has an optimal positional strategy, so this constructs an optimal strategy for the conjunction. The same argument applies to every one-player restriction. GK's actual epsilon-zero merge/reset theorem therefore gives Max an optimum in the two-player game. The transformations for boundary targets and failures preserve this game class.

For a subgame with no AS-winning state, attainment implies that every value v_s is strictly less than one. A uniform optimal positional Min strategy and eta=min_s(1-v_s)>0 give the promised spoiling interface. No algorithm is asked to compute eta, and no input-independent lower bound on it is assumed.

## 5. The compensated-prefix invariant

For semantic synthesis use a fixed pure strategy with this property, abbreviated CP: for every epsilon>0 there exist finite constants C_epsilon,D_epsilon, uniform over starts in its certified region and all opponents, and an adapted martingale M with increments bounded by D_epsilon, such that every prefix obeys

sum_(t<T) w_t >= -epsilon T-C_epsilon+M_T.                    (5.1)

The strategy is chosen before epsilon. The constants and martingale may depend on epsilon. Martingale increments can be taken zero at controlled transitions. Targets are made absorbing with zero rewards. All strategies below have this property. Applying the martingale strong law to epsilon=1/k, k>=1, proves almost-sure nonnegative liminf. Finite certificates give only finitely many martingale types for each fixed epsilon.

The M primitive has CP by (3.1). We now give the two closure operations, including the random-excursion costs needed at odd priorities.

### Even closure

Suppose a finite retained region Z, with A treated as terminal success, satisfies both:

(i) every state is in M(A,Z); and
(ii) every state is in F_(j-1)(A union (D_j intersect Z),Z), where j is even and a child CP strategy is supplied.

In round k play the ordinary strategy for k steps, unless A is reached. Then start a fresh child strategy and continue until A or D_j is reached; if D_j is reached start the next round. A child stage that never ends wins its lower-priority conjunction. Infinitely many completed rounds give infinitely many visits to D_j. Thus parity is satisfied almost surely in all cases.

There are at most sqrt(2T)+2 begun rounds by time T. Apply the child bound with epsilon/2, paste its stopped martingale increments and the ordinary increments, and charge a constant H+C_(epsilon/2)+W per round. The result is

sum w >= -(epsilon/2)T-K_epsilon(sqrt(2T)+2)+M_T.

The inequality a sqrt(T)<=epsilon T/2+a^2/(2epsilon) converts this to CP. The strategy itself does not depend on epsilon. This proves every intermediate-prefix bound, not merely bounds at selected long phase endpoints. Any excluded controlled boundary edge costs at most W.

### Odd layered closure

Suppose the largest priority j is odd and the region has a finite layer certificate

U_1=Z, R_i subset U_i without priority j,
Z_i=PosAttr_Max(R_i,U_i), U_(i+1)=U_i minus Z_i,
U_(ell+1)=empty,

where R_i is a Min-trap inside U_i and carries a child CP winning strategy. A terminal A can be the first zero-reward child. Use the fixed positive-attraction rank policy outside the R_i and the corresponding child inside each R_i, resetting upon entry. Max and chance cannot exit U_i; an exit from R_i must be an opponent move to an earlier layer.

Collapse each R_i to a state r_i. A step outside all R_i costs one; exiting an r_i costs one; waiting inside an R_i costs zero. In the auxiliary decision process an r_i offers either a stop action or one of its permitted exits to an earlier layer. The other transitions are the fixed attractor policy, the original chance rows, and all opponent choices. Delete the zero-cost waits when analyzing this auxiliary process.

Every policy of the auxiliary process eventually stops almost surely. Otherwise a nonterminal end component exists. Choose its least layer index i. Positive-attractor ranks force a supported path inside that component to r_i. A non-stopping action there leads to an earlier layer, contradicting minimality. All chance successors, not only the favorable one, are included in this end-component argument.

It follows that the maximum expected remaining active cost is bounded by some H<infinity and has a finite potential V satisfying V>=c+E V_next for all available actions. For completeness, the usual universal-reachability rank iteration has at most m states in this auxiliary process and a chance of at least p_*^m to stop in every m active steps, uniformly over all opponent histories. Thus H<=m p_*^(-m), after increasing m for a stop sink if needed. The potential also follows from the finite-horizon Bellman iterates and their bounded limit; a rational solution has polynomial bit length by the proper finite-MDP linear equations. This is an existence bound, not a polynomial-magnitude assumption.

Pull V back constantly over each R_i. Let A_T count active transitions in the original run. Center only the chance increments of c+V_next-V_current; at controlled transitions the inequality holds pointwise. For a bounded-increment martingale N,

A_T <= V(initial)-V(current)+N_T <= H+N_T.                  (5.2)

In particular E A_T<=H, so the total active cost is finite almost surely. Arbitrarily late opponent exits and arbitrarily long zero-cost child residence times are included.

For fixed epsilon let C be the largest child CP constant. At most A_T+1 child segments have begun. Pasting the child bounds and charging active rewards by -W gives

sum w >= -epsilon T-C-(C+W)A_T+M_T
       >= -epsilon T-C-(C+W)H + [M_T-(C+W)N_T].

The bracket is a bounded-increment martingale, proving CP. Almost surely only finitely many active steps occur, so eventually one child is followed forever and parity holds. Null events are transferred from child strategies by taking the countable union over finite entry histories; no child process is conditioned on the future event of never exiting.

## 6. The monotone fixed-point equations

All fixed points below are over the ordinary powerset lattice of S. Intersections and unions in an argument are literal set operations. For even j define

E_j(A,B) = nu Z [ M(A, B intersect Z intersect S_<=j)
                 intersect F_(j-1)(A union (B intersect Z intersect D_j), B intersect Z) ].       (6.1)

For odd j define

O_j(A,B) = nu Z mu X [ A
                    union P(X intersect Z, B intersect Z intersect S_<=j)
                    union F_(j-1)(A union (X intersect Z), B intersect Z) ].                    (6.2)

The claim is F_j=E_j or O_j according to parity. Inductively all child maps are monotone and all their AS regions have CP strategies. The displayed right sides are monotone in every bound or free set variable. The base F_-1=A is immediate success and has CP.

### Proof of (6.1)

Let W=F_j(A,B). The true AS region has a safe continuation at every positive-probability finite history, so Max can stay in W until A. Its strategy wins the ordinary M objective. Stopping it at the first priority-j visit also wins the lower boundary objective in (6.1). Therefore W is a postfixed point of that map, and W is contained in its greatest fixed point Z.

Conversely, at the greatest fixed point, every state of Z satisfies both objectives displayed in (6.1). In particular Z subset A union (B intersect S_<=j), and it has a strategy staying in Z until A. The lower objective's target D_j is inside Z. The even closure of Section 5, with the supplied child CP strategy and ordinary potential, proves a CP AS-winning strategy on Z. Hence Z subset W.

### Proof of (6.2): soundness

Fix a greatest-fixed-point solution Z and let X be the least inner fixed point. Then X=Z. Every inner iterate has a strategy maintaining Z until A: its P strategy maintains the boundary until a previously admitted target, and its lower strategy maintains that boundary until A or a previously admitted target. Along these target transfers the finite iteration rank strictly decreases. Thus the final Z is a controlled safety region up to A. Its chance and Min edges cannot leave Z before A, and Max has staying choices. Work in this retained arena with A absorbing.

Compute the inner closure equivalently by alternately saturating positive Max attraction and adjoining the lower winning set. This has the same least fixed point as the union in (6.2): both constituent maps are monotone, and the lower map includes the current target X. Saturating either operation cannot pass the least common closed set; conversely a stabilized alternating closure is closed under their union.

After a positive-attractor saturation, put U=Z minus X. This U is a Max-trap and is chance-closed. In particular Max and chance have no edge from U to X; Min's edges to X are successful exits, and Min has a staying edge at each of its states in U. Therefore the new lower winning region R outside X is exactly the AS lower-priority winning region in the induced U, with priority-j states forbidden. The equivalence is literal: Min can choose to stay, and choosing an edge to X is already success. Its AS region R is a Min-trap in U and has a child CP strategy. It contains no priority-j vertex.

Adjoin PosAttr_Max(R,U) and continue. Since the inner closure equals Z, these additions exhaust the arena; at most n nonempty layers are needed. If A is nonempty start with its trivial terminal child and positive attractor. We have precisely the odd layer certificate of Section 5. That closure yields a CP AS-winning strategy on Z. This proves soundness of (6.2).

### Proof of (6.2): completeness

Again let W be the true AS region, restricted to its staying arena until A. Evaluate the inner least fixed point of (6.2) with Z=W, and call its result X. It includes A and is positively Max-attractor closed. Suppose U=W minus X is nonempty. It is a chance-closed Max-trap, so Min can stay in U and Max cannot leave it. Every state of U must still be AS winning for the original conjunction.

Let C=PosAttr_Min(D_j intersect U,U), and Y=U minus C. The latter is chance-closed and a Min-trap. There is no AS lower-priority winner in the induced Y: any such winner could stay in Y, and hence would already belong to the lower boundary term of the fixed inner closure X, a contradiction. Section 4 gives a uniform optimal positional Min child policy on Y and eta>0 bounding every child success probability by 1-eta.

Define Min's policy in U to use its positive-attraction rank policy on C and the child policy on Y. On paths visiting C infinitely often, disjoint trials of at most n steps each have conditional chance at least p_*^n of reaching D_j. Thus D_j occurs infinitely often almost surely on that event, violating max-even parity because j is the largest priority in U.

On paths eventually staying in Y, a successful full path would contradict the uniform child bound. Here is the conditional-law justification. At a history ending in Y, modify Max's continuation only when it first tries to leave Y, thereafter choosing an arbitrary staying continuation. The unmodified event of winning without ever leaving Y is included in the child winning event of the modified strategy, whose probability is at most 1-eta. Therefore

P(full success | history) <= 1-eta + P(a future visit to C | history).

On the event of finitely many visits to C, the last conditional probability tends to zero. Indeed, for each fixed N and times t>=N it is at most the conditional probability of some C visit after N; martingale convergence and then N→infinity give the assertion. On a successful run, however, the conditional probability of full success tends to one by Levy's upward theorem. These conclusions are incompatible. Hence success on eventual Y has probability zero as well.

The constructed Min policy therefore spoils the conjunction from U, contradicting that U lies in W. Thus X=W. W is a postfixed point of the outer greatest-fixed-point map, so it is included in O_j(A,B). Soundness gives the reverse inclusion. This proves (6.2) and completes the induction, including CP.

## 7. Polynomial formula size and the bit algorithm

Substitute (6.1) and (6.2) recursively down to F_-1. There is only ONE occurrence of F_(j-1) at each level. The boundary update B becomes B intersect Z at each step. The target update appends either B intersect Z intersect D_j or X intersect Z. After literal substitution, each B expression has linear size in d, and each A expression is a union of at most d expressions of size O(d). Thus the complete nested formula has size O(d^3), with at most two fixed-point binders per level. In particular there is no exponential unfolding hidden in the use of boundary parameters.

Translate the nested formula to an ordered equation system in the exact sense of HS Definition 3.1: introduce a variable for each bound fixed point, replace the corresponding bound subformula in its parent's right side by that variable, and order inner binders before outer binders. Right sides retain their monotone set expressions and the M and P primitives. Their total description is polynomial in L. This is the standard definitional translation, and substituting the inner equations according to HS's valuation semantics recovers the displayed nested formula. No nonmonotone induced-subgame operator is being used.

The lattice is P(S), with n singleton basis elements, not an energy lattice with nW levels. The number of equations and their alternation depth are O(d)=O(n). HS's chained-product universal graph has size 2^O(log^2(n+2)); a simple descending greatest-fixed-point evaluation on its polynomial product with the basis/equation set already needs only quasipolynomially many equation evaluations. Its joins are set unions, memberships are bit tests, and graph construction and all table operations have quasipolynomial bit cost. The stronger lifting version is available but not needed for this bound.

Each equation evaluation makes polynomially many set operations and at most polynomially many M or P evaluations. P is polynomial. Each M evaluation makes linearly many S calls on an arena of polynomial binary length, with unchanged rational chance rows and polynomial-length signed rewards. Therefore each evaluation costs 2^O(log^2(L+2)) bit operations. Multiplying the two quasipolynomial bounds preserves that form. All constants are universal and independent of the input's priorities, probabilities, reward magnitude, threshold, or number of states.

This describes one uniform deterministic finite-bit algorithm. It validates the input, performs the exact normalization, builds the monotone equation system and universal graph, computes its solution, and writes the n membership bits. Every intermediate encoding, arithmetic operation, graph operation, and output operation is included in the bound. Polynomially intertranslatable explicit input conventions affect only the numerical constant C. This proves the frozen statement.

## 8. Scope of the result and remaining external obligations

The semantic strategy constructions have unbounded phase counters and finite recursive descriptions which may be exponentially large. Their costs and memory are not silently assigned the decision algorithm's bound: the theorem outputs only the winning region. The source randomized certification and exact ordinary values/positional strategies remain paid source operations. No lower bound, impossibility, finite-memory promise, favorable probability floor, fixed priority count, or strict-positive replacement is used.

The author regards the derivation above as a full proof submission at its frozen scope. The 450 tiny exact game comparisons are only consistency checks for the formulas, not proof or independent gates. No optional original-history traversal was performed, and transitive primary reading is incomplete; therefore this packet supplies no exhaustive novelty or clearance claim. Correctness, substantial contribution, acceptance, campaign accounting, formal support, manuscript and release steps remain entirely outside this author discovery packet.
