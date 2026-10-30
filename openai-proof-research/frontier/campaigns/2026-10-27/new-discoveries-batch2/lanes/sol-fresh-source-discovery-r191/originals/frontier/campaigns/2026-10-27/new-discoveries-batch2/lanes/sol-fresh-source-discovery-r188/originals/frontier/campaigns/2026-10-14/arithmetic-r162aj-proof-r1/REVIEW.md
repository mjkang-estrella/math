# R162AJ independent proof review — round 1

**Verdict: PASS.** This verdict covers the entire unchanged frozen statement and the entire unchanged author proof. No necessary author correction was found, and no essential correctness-verification obligation remains, relative to the stipulated Source104 proofs. The conclusion is the decision-only deterministic quasipolynomial **bit** bound for the almost-sure conjunction with nonnegative **liminf**, including the exact zero endpoint and arbitrary behavioral opponents. It is not a verdict on contribution, acceptance, campaign accounting, or priority.

Reviewed statement SHA256: `6a73b45333ee99648324171a070cec4fab8613a7af9b8687f87db7d0d31721e4`.
Reviewed proof SHA256: `7980d626908175daf46c3326860a10888f26b61a252379e941b34636585a3817`.

This is a fresh independent review by Codex / GPT-6 Astra / high reasoning / default service tier. No other review, peer status, author response, or prior correctness assessment was consulted. The author’s assertion of completeness and its reported small-game comparisons were not evidence for this verdict. The proof was not edited. The derivations below explain why the sensitive steps work; they are not a substitution of a narrower theorem.

## 1. Scope and dependency boundary

I read the actual stochastic Source104 discounted proof, labeling construction, and application/bit proof at the stipulated pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I also read the complete operative deterministic ordinary, randomized ordinary, and deterministic parity constructions, including their stronger values, strategies, certification, and prefix guarantees. Those source proofs are premises, not objects of a new upstream-truth audit.

For the new semantic and acceleration interfaces I read the actual GK reset, split, projection/merge and unrestricted transfer proofs, including Theorem 6.2 at epsilon zero; HS’s equation semantics, fixpoint-game interface, chained-product proof and complexity construction; and the essential primary antecedents of that construction. The latter include Baldan–König–Mika-Michalski–Padoan’s fixpoint-game correctness and formula/equation translation, Colcombet–Fijalkow’s tree/graph transfer, the Czerwiński et al. universal-tree interface, and Jurdziński–Lazić’s actual coding and counting proofs. Reading limits, versions, exact local line extents, recoveries and access records are in `private/READING-LIMITS.md` and the associated records.

CDGO’s full report and conference proof, DM’s full operative finite-memory construction through its final epsilon choice, and GZ’s priority-mean-payoff interface were checked as compatibility comparisons. None is silently assumed to prove the present conjunction at zero. Standard finite-state occupation arguments, finite-MDP reachability, martingale convergence/strong laws, and rational linear algebra are used in their usual finite, bounded forms. Relevant reductions and probabilistic arguments are spelled out below. No unproved new lemma or unread essential research interface is left as a premise.

## 2. Input, event and boundary semantics

For a threshold a/b with b positive, every finite average transforms to b times the old average minus a. Because b is fixed and positive, taking liminf preserves this identity, including equality. Multiplying each signed integer reward by b and subtracting a increases binary lengths polynomially. No gap or approximation is introduced.

If the distinct original priorities are p_1<...<p_k, assign increasing c_i of the same parity, choosing the least eligible value at each step. Then c_k<=2k, and reflection c_i -> E-c_i in an even E>=c_k converts the least recurring priority into the greatest while preserving its parity. Thus at most O(n) levels are used even if the encoded priority magnitudes are enormous.

Probability validation is exact: denominators must be positive, numerators nonnegative, and each chance row must sum to one. Products of denominators have bit length at most the sum of their input lengths. Zero probability edges can then be removed. Every remaining chance row is nonempty and unchanged. A conventional explicit encoding can reject malformed counts or field lengths by a scan bounded by the actual input length, before allocating according to an invalid huge declared count. GCD reduction is optional; unreduced rational inputs are harmless.

For F_j(A,B), membership in A takes precedence over every safety or priority constraint. An initial state outside A and B intersect S_<=j fails immediately. A valid state that never reaches A must satisfy the original tail conjunction. Replacing targets by zero-reward even sinks and forbidden states by negative odd sinks implements exactly these alternatives: entrance-edge rewards are a finite prefix, and the sink changes the eventual outcome correctly. No conditional chance law is involved. Enlarging either A or B can only enlarge the event won by a fixed strategy. This supplies the required monotonicity on the *whole* powerset domain, not only on subsets inducing subarenas.

The same argument applies to the ordinary boundary objective M. The strict support-safety meaning of P is also appropriate: a finite supported path leaving the permitted set has positive probability when its choices are selected, so almost-sure safety against every opponent excludes it. Targets themselves are always included.

## 3. Ordinary almost-sure extraction and the completed potential

A direct test of nonnegative expected payoff would be wrong. For example, a chance vertex leading equally to absorbing rewards +1 and -1 has expected limiting payoff zero but is not almost-sure winning. The repeated deletion in Section 2 of the author proof is therefore essential.

Let W_AS be the true ordinary almost-sure region of a boundary game. For any finite history with positive probability under an AS strategy, its continuation remains AS; otherwise an opponent continuation with positive failure probability would contradict the original guarantee. Consequently W_AS is closed under every Min and positive-probability chance edge and admits staying Max choices. In a retained subarena containing it, restriction of its AS strategy still guarantees expected pathwise-liminf payoff at least zero. A state with negative value is outside W_AS. If the positive Min attractor of those negative states met W_AS, the attraction policy would reach one of them with positive probability. Min can then use its value-optimal continuation; bounded payoff with negative expectation entails a positive chance of a negative payoff. This again contradicts AS. All deletions therefore preserve W_AS.

The complement of a positive Min attractor is a total subarena closed at Min and chance, with a staying Max edge. Each nonempty deletion removes a vertex. At termination all ordinary gains G are nonnegative. The losing sink has gain -1 and cannot survive. Thus the remaining task is a sound AS guarantee in an all-nonnegative-gain arena, not the false implication “nonnegative expectation at this one start implies AS.”

The operative source discounted proof supplies a single Blackwell Max policy, G and psi with the exact identities stated by the author. They follow from comparing constant and first-order coefficients of the discounted Bellman relations. On a Min edge with strict gain increase delta=G_j-G_i>0, put r=w_ij+psi_j-psi_i. Choosing K>=-r/delta ensures r+K delta>=0. One finite K works for all such edges. Equality-gain Min edges already satisfy r>=G_i>=0. Selected Max edges have delta=0 and r=G_i>=0. At chance states, E delta=0, so adding KG does not alter the conditional expected residual. After shifting h=psi+KG to have minimum zero, h lies in [0,H] and

    R_t = w_t + h(X_(t+1)) - h(X_t)

is nonnegative on controlled transitions and has nonnegative conditional expectation at chance transitions. Define Delta M_t=R_t-E(R_t|F_t) at chance transitions and zero at controlled transitions. Then R_t>=Delta M_t pointwise and |Delta M_t|<=2(W+H). Telescoping gives, for every T,

    sum_(t<T) w_t >= -H + M_T.

This is an all-prefix inequality before conditioning on any future event. For completeness, bounded differences give sum_t E[(Delta M_t)^2]/(t+1)^2<infinity. The corresponding martingale series converges almost surely; Kronecker’s lemma then gives M_T/T->0. This proves the ordinary AS property. The inequalities hold for every available Min action, so random mixtures and private history dependence introduce no extra hypothesis.

For numeric compatibility, the source determinant argument bounds coefficient lengths after clearing all chance denominators; the product denominator has polynomial length. Factoring the appropriate power of the discount parameter from the determinant and numerator leaves a nonzero integer constant denominator coefficient. G and the first derivative psi are quotients of polynomial-length coefficients. Differences, nonzero-gap division for K, and h therefore have polynomial bit lengths. Their magnitudes may be exponentially large. The decision algorithm only asks the source for signs; it does not need to synthesize these potentials.

P is computed by a greatest safety kernel followed by a positive attractor. In the kernel, all Min and chance successors stay and Max has a staying choice. The attractor iteration uses existential Max/chance and universal Min predecessors. Following its ranks offers a conditional chance at least p_*^n of reaching the target in n steps, uniformly over all behavioral Min policies. Failure to make favorable chance moves does not violate safety. Conversely, outside the kernel safety cannot be maintained; inside it but outside the attractor, Min can stay outside and no chance edge enters the attractor. This proves the exact two-argument primitive semantics.

Thus M costs O(n) source calls on polynomial-length arenas, while P is polynomial. Arbitrarily small positive chance probabilities affect semantic trial constants but not these oracle call counts.

## 4. Attainment, the zero endpoint and behavioral quantifiers

The indicator of the conjunction is inverse-submixing. To see this without exchanging limiting operations, fix epsilon>0. For each successful word i there is a finite c_i such that its first k rewards sum to at least -epsilon k-c_i for every k, including short prefixes. A prefix of a shuffle is exactly the union of one prefix from each word. Its total is therefore at least -epsilon T-c_1-c_2. Letting T grow and then epsilon decrease gives nonnegative liminf. The infinitely recurring priority set of the shuffle is the union of the two recurrent sets; the greater of their two even maxima is even. The complemented indicator is consequently bounded, Borel, shift-invariant and submixing.

GK’s maximizing player is therefore original Min. Its positional-optimal theorem gives a single positional Min optimum for the complemented indicator, hence for minimizing the success probability. The other side requires GK’s *unrestricted* reset/merge theorem, including its explicit epsilon-zero clause, not merely weak determinacy or a finite-memory theorem. The family of finite action-restricted arenas is closed under the required splits; chance vertices are one-action probabilistic states. The class of all strategies is closed under projection, merge and reset. The submixing hypothesis used in the proof is satisfied even though Theorem 6.2’s display abbreviates the standing assumptions of its section.

Here is the one-player attainment prerequisite in detail. Under any strategy in a finite maximizing MDP, the states and actions visited infinitely often form an end component almost surely. For a chance/action outcome of fixed positive probability that is offered infinitely often, the probability of avoiding it for k further offers is at most (1-p)^k, even after arbitrary previous histories. Hence every positive supported successor belongs to the recurrent component. Eventual absence of the finitely often used edges and repeated mutual reachability give strong connectivity.

On a successful path choose a convergent subsequence of empirical edge frequencies. Conservation of arrivals and departures has an O(1/T) error. Bounded martingale differences for each chance frequency show that the limiting frequencies respect the fixed chance rows. Their weighted reward sum is nonnegative because the path’s liminf is nonnegative. The resulting balanced flow gives a stationary policy on its positive-mass states. Its recurrent-class decomposition expresses the reward as a convex combination of recurrent means, so at least one class has mean >=0. Strong connectivity of the end component supplies a controller policy reaching that class almost surely from every component state. Therefore ordinary expected mean-payoff value is nonnegative everywhere in that component.

Apply the completed potential there. In round k take k ordinary-policy steps and then one bounded positive-attraction trial toward its maximum-priority set. The latter has even priority. By time T there are O(sqrt(T)) trials and resets, each of bounded length/cost. Pasting the ordinary martingale differences gives a lower prefix bound -O(sqrt(T))+M_T, at *every* time T. Infinitely many trials occur, each with conditional success probability at least p_*^|C|; the repeated-failure bound proves infinitely many maximum-priority visits almost surely. This is an AS conjunction strategy when the good mean is exactly zero.

There are finitely many candidate end components. Call one good if it has even maximum and admits the nonnegative flow just used. Every successful run reaches their union G. Conversely, after reaching G the controller chooses a containing good component and uses its AS strategy. Thus the optimal conjunction probability is exactly the optimal reachability probability of G. Finite-MDP reachability attains this value with a positional policy. One direct derivation maximizes E[beta^tau 1_(tau<infinity)] for 0<beta<1, with tau the target hitting time. The non-target Bellman operator is a contraction and has a uniform greedy positional optimum. Along a sequence beta increasing to one, one of the finitely many positional policies is optimal on an infinite subsequence. Comparing it on that subsequence with any behavioral policy and taking the bounded monotone limit shows it maximizes the actual hitting probability, simultaneously at all starts. The same argument works in every required one-player restriction.

GK’s actual transfer proof builds the two-player minimizing strategy from split games by merge and reset; its projection/measure argument treats infinite alternation, rather than identifying a future-conditioned law with an unconditioned MDP. With one-player optima available, its epsilon-zero clause yields a Max optimum here. Thus if a finite subgame has no AS state, every attained value v_s is strictly below one, and the positional optimal Min policy gives a uniform gap

    eta = min_s (1-v_s) > 0.

Neither eta nor the optimizing semantic strategy is an algorithmic output.

As an endpoint stress case, take a Max state u of priority 1 with a zero self-loop, an edge u->v of reward -1, and the sole edge v->u of reward 0, with v of priority 2 (maximum convention). Increasing zero-reward waits between visits to v achieve liminf zero and parity. Every finite-memory behavioral policy that ensures infinitely many v-visits induces a finite Markov chain whose relevant recurrent classes give v positive frequency, hence strictly negative mean. This is compatible with the theorem’s unbounded-memory semantics and shows why a strictly-positive finite-memory construction cannot silently replace them. This example is diagnostic, not the basis of the verdict.

## 5. Restart estimates and odd excursions

The induction needs one fixed pure strategy for each certified region, chosen before epsilon. For every epsilon, its prefix inequality has form

    reward(T) >= -epsilon T - C_epsilon + M_T,

with increments of M uniformly bounded over starts and opponents. Pure strategies are available: the ordinary policy and rank policies are pure, the MDP construction is pure, and the semantic closures preserve purity. The finite number of states and child certificates lets constants be maximized. This is a stronger property than AS winning alone.

For even closure, a completed round k has k ordinary steps, so the number of begun rounds is at most sqrt(2T)+2. The ordinary segment loses at most H apart from its martingale; a child segment, including an interrupted one, loses at most (epsilon/2) times its length plus its fixed constant apart from its martingale. Any excluded controlled boundary edge loses at most W. The total deterministic error is therefore

    -(epsilon/2) T - K_epsilon (sqrt(2T)+2).

Young’s inequality absorbs the square-root term into another (epsilon/2)T plus a constant. The schedule never depends on epsilon. If a child stage persists forever, its lower-priority conjunction wins; otherwise infinitely many completed rounds visit the even highest priority. Countably many finite entry histories suffice to transfer the child’s null exceptional sets.

The odd closure is more delicate because an adversary may wait arbitrarily long in a child before exiting it. Bounding chronological exit times would not suffice. Count instead each transition outside children and each exit from a child as one active step. Collapse a child R_i to r_i, permitting a stop action or any of its ambient permitted exits. This enlarges the adversary’s options and costs; it is a valid upper-bound process even if some exits are not attainable under a particular internal child history. Its other actions are the fixed Max attraction choices, all Min choices, and the original chance rows.

There is no nonterminal end component in this active process. Choose the smallest layer index represented in one. At any state of that layer outside its child, attraction ranks give a supported route to the child: Max’s fixed choice decreases rank; every staying Min choice decreases it; a chance state has a decreasing supported edge and all its successors must remain in an end component. Such a route cannot escape to an earlier layer in this component by minimality. It must reach r_i. A non-stopping exit from r_i goes to an earlier layer, a contradiction. All chance successors are retained in this reasoning.

For a finite process with no nonterminal end component, the universal-reachability rank iteration covers every state. At each nonterminal state every available action has a positive supported step toward a smaller rank. With m states this gives a conditional probability at least p_*^m of stopping in each block of m active steps, regardless of past choices. Thus the maximal expected total active cost is at most m p_*^(-m), with an inessential extra sink allowance. Finite-horizon Bellman suprema increase to a bounded potential V with

    V(x) >= c(x,a) + E[V(next) | x,a]

for every action. It can be taken nonnegative and bounded by H. This derivation uses no distributional assumption on the opponent’s residence time in a child.

Pull V back constantly over each R_i. On internal child transitions its cost and potential change are zero. At controlled active transitions the Bellman inequality is pointwise. Center the chance increments of c+Delta V, obtaining N with bounded increments and

    A_T <= V(initial)-V(current)+N_T <= H+N_T.

Taking expectations and monotone convergence yields E[A_infinity]<=H, hence finitely many active transitions almost surely. For a common child constant C there are at most A_T+1 child segments, so summing their prefix inequalities and charging active rewards gives

    reward(T) >= -epsilon T-C-(C+W)H + M_T-(C+W)N_T.

The bracket is a bounded-difference martingale. The finiteness of H, not a polynomial bound on its magnitude, is the semantic requirement. Eventually one child is followed forever, giving parity.

All pasting here is predictable: at a chance transition the current strategy type and its finite local history are fixed before the fresh chance outcome. At a controlled exit the local martingale increment is zero. Extending stopped component differences by zero and choosing among finitely many component types preserves conditional mean zero, including with private behavioral Min memory. No pasting argument conditions a child on the future event that it never exits. Applying the strong law for epsilon=1,1/2,1/3,... gives the liminf conclusion against each arbitrary fixed opponent; one common null event for uncountably many opponents is neither needed nor claimed.

## 6. Both fixed-point equalities

I checked the equations for arbitrary boundary sets, including overlapping targets/safety sets, missing priority levels and empty retained regions. These cases are part of the monotone functions needed by HS, not just the final call.

For even j, let W=F_j(A,B). Every positive-probability continuation of an AS strategy stays in W until A and wins ordinary mean payoff. Stopping at the first D_j visit gives a lower-priority boundary win; if the stopping target is never reached, only smaller priorities occur. Consequently W is postfixed for (6.1). At its greatest fixed point Z, each state satisfies both the ordinary and lower boundary tests, with every pre-target state in B intersect Z. The child target D_j is also inside Z. The even closure above proves the reverse inclusion and the CP invariant. If D_j is empty, the child may simply run forever; the same reasoning applies.

For odd j, at a greatest fixed-point solution Z the inner least fixed point equals Z. Iteration ranks show that admitted states remain in Z until A: a P or lower strategy is followed until an earlier admitted target, then the rank decreases. No infinite descent of such finite ranks is possible. This establishes the controlled safety region before treating it as a retained arena.

Saturate P and the lower map alternately. Both operations are monotone and inflationary on subsets of Z because the previous set appears as a target. Any common closed set contains every intermediate iterate, and a stabilized alternating iteration is closed under their union. Hence this process has exactly the same least fixed point as (6.2).

After P saturation, U=Z minus the accumulated set X is a chance-closed Max trap: Max/chance cannot reach X in one step, and each Min state has a staying option. In the lower boundary game, a Min exit to X is success, while there are no Max/chance exits there. Thus its new winners outside X coincide exactly with the induced-U lower winners with priority j forbidden. Their AS region R is closed under Min/chance within U and has staying Max choices; it contains no priority-j state. By induction it carries CP. Adjoin its positive Max attractor and repeat. Termination at Z gives the finite odd layers analyzed above. This proves soundness and CP, including a terminal A layer.

For completeness, take the true AS region W and evaluate the inner least fixed point at Z=W. Suppose its complement U is nonempty. It is a chance-closed Max trap. Restrict Min to its staying actions there; Max cannot exit. Every U state must still be AS for the original conjunction.

Let C be Min’s positive attractor to D_j in U and Y=U minus C. Y is closed under Min/chance and admits staying Max choices. If it had a lower-priority AS winner, Max could retain that strategy in U, so that state would already be in the lower boundary term of X. Thus it has no such winner. The attainment result provides one Min child policy on Y and a gap eta>0. On C use the attraction policy.

On infinitely many C visits, take successive disjoint trials of at most n steps. Their conditional success probabilities are at least p_*^n. Iterated conditional failure bounds, rather than independent-trial assumptions, imply infinitely many D_j visits almost surely. These violate parity.

For eventual residence in Y, the author’s conditional-law argument is necessary and valid. At a finite history h in Y, couple the actual Max continuation to a strategy in the induced child, replacing the first attempted exit by a staying choice. Until that exit the laws coincide. The event of full success with no future C visit is included in a child-success event, so

    P(success | F_t) <= 1-eta + P(a C visit after t | F_t).

For each fixed N and t>=N the last conditional probability is bounded by P(E_N|F_t), where E_N means some C visit after N. Lévy convergence gives P(E_N|F_t)->1_E_N. On paths with finitely many C visits there is an N with E_N false; taking a countable intersection of these convergence events shows the last term tends to zero. On successful paths, however, P(success|F_t)->1. The two facts contradict the displayed bound. Hence success on eventual Y has probability zero too. The constructed Min policy contradicts U being AS, proving X=W. This establishes completeness of (6.2) and closes the semantic induction.

## 7. Polynomial description and a fully charged bit algorithm

There is exactly one recursive child occurrence per priority. Along substitution, B acquires at most d intersections with bound variables. A gains at most d summands, each of size O(d). Repeating those expressions at O(d) levels gives O(d^3) literal formula size. Alpha-renaming binders avoids capture. Ordering the O(d) binders from inner to outer and replacing bound child subformulas by their variables gives the HS ordered equation system. Its valuation semantics fixes outer parameters while solving inner equations; inductive substitution recovers the original nested expression. No distributivity or special modal form is required of M or P; they are arbitrary monotone functions with the already verified evaluation procedures.

Let q be the number of equations and n the singleton-basis size of P(S). Then q=O(n), and the parity index can be bounded by 2q+1. A positional witness in the fixpoint game has at most N=nq basis/equation nodes after tuple choices are suppressed. This conservative bound avoids identifying the number of equations with a potentially smaller alternation index. The exponential set of tuple positions is a semantic device only; the algorithm never constructs it.

The universal graph can be built uniformly and explicitly. For h=O(q), Jurdziński–Lazić’s coding embeds each ordered tree with at most N leaves into the tree of h-tuples of binary strings having total length at most g=ceil(log_2 N). Its proof chooses a median root branch, adds one leading bit on the two sides, and recurses without a bit on the median branch. On either side the leaf count halves; on the median the height decreases. Therefore g bits suffice along every root-to-leaf path. The tuple set can be enumerated with elementary bounded loops. Its size is at most

    sum_(ell=0)^g 2^ell binom(ell+h-1,h-1)
      <= 2^(O(log(N+2) log(N+h+2))).

The harmless h=0 or N=1 cases have a singleton construction. An explicit representation may store all h components; that adds only polynomial overhead. The Colcombet–Fijalkow transfer constructs graph edges by comparing appropriate truncated ancestor orders, using strict descent for odd labels and non-strict descent for even labels. Every infinite path is even because at the highest recurring odd label strict descent in a fixed finite order could not persist. Their converse rank/tree representation for an even finite graph, followed by the coding embedding, gives universality. Listing all labeled edges by testing every leaf pair is polynomial in the leaf count and h, hence still quasipolynomial. No nonuniform graph advice or hard graph-construction oracle remains.

Writing U for the number of universal graph vertices, HS Definition 5.2 gives a monotone function on n*q*U bits. For each graph vertex z and equation i form the mask

    P_i(z) = {s: some z' with a label-ad(i) edge z->z'
                   has (s,i,z') in the current product set}.

Evaluate f_i on these q masks and put its output bits at graph coordinate z. This implements g directly with unions, scans and the original RHS oracles. HS’s proof works in both directions: embed a finite even witness into the universal graph to obtain a postfixed product set; conversely, choose a graph successor for every basis challenge in a surviving product triple, obtaining a parity-winning path. BKMP’s actual fixpoint-game correctness identifies the resulting solution with the nested equations. Its finite-powerset specialization needs no additional continuity or arithmetic-lattice hypothesis.

Starting from the full product set, descend under g. At most n*q*U strict deletions can occur, followed by a stability test. A deliberately loose implementation uses polynomially many operations in n,q,U per round and at most q*U full RHS evaluations. It is unnecessary to invoke HS’s faster lifting implementation. Each RHS has polynomial description length and calls M/P only polynomially often. Each M uses O(n) source calls on boundary games of polynomial binary length; probabilities remain unchanged, apart from deterministic sink rows, and rewards are copied normalized rewards or fixed constants.

For absolute constants a,b,c, the full computation is consequently bounded by

    (L+2)^a * 2^(b log_2(L+2)^2)
              * 2^(c log_2((L+2)^a+2)^2)
      = 2^(O(log_2(L+2)^2)).

All graph labels, counters and addresses have at most polynomially many bits, and polynomial simulation overhead of a standard bit machine stays within this bound. Exact normalization, validation, graph generation, masks, rational arithmetic inside S, and n output bits are charged. The constants are fixed independently of priorities, weights, probabilities and threshold. Polynomial intertranslation of conventional explicit encodings only changes the universal exponent constant. Nothing in this computation enumerates phase counters, eta, 1/p_* trials, child strategy trees or energy levels. Those quantities occur only in the semantic existence proof.

## 8. Stronger-source checks and disposition

The source deterministic ordinary algorithm supplies more than a threshold headline: simultaneous potential-witness labeling, full exact values, globally optimal positional policies, and stronger credit/tropical consequences. Its randomized companion supplies fixed-comparison whole-vector guarantees, exact top-potential recovery, an exact certificate check, and an expected-time always-correct conversion. These paid operations were read. They do not require the proposed algorithm to output its semantic parity strategies.

The deterministic parity source already supplies the all-epsilon uniform-prefix scheduling, compatible dominion extraction and a quasipolynomial ordinary-oracle reduction. Its proof is for deterministic arenas. Here the chance residual is handled by a martingale, and the odd active-excursion count has its own stochastic potential. No failure of a naive dominion substitution or slow older recursion was used as a lower bound.

CDGO’s displayed objective is limsup in both the full report and conference paper. Its strongest even proof ends with infinitely many favorable prefix averages via a limsup event and Fatou, so it cannot be invoked unchanged for this liminf assertion. Its decomposition remains a relevant stronger comparison. DM’s Appendix B.1 supplies a substantially stronger finite-memory strict-positive construction than an abstract suggests: odd layers, two-mode mixing, stationary perturbation, and explicit probability-bit bounds. Its final choice divides a positive mean mu-prime by accumulated excursion costs. At mu-prime=0 this no longer supplies a positive mixing parameter. The author’s gain-completion and all-prefix arguments address that endpoint directly. GZ’s priority mean payoff instead discards rewards away from the extremal recurrent priority in its average; its multidiscount limit is a different payoff, as its actual definition and transfer proof confirm.

These checks reveal no omitted hypothesis that narrows the frozen theorem. There is no required repair, counterexample to the theorem, essential unread interface, or unresolved algorithmic cost. The mathematical PASS is independent of the artifact checks. No optional original-history traversal was performed, so this review makes no history-clearance or exhaustive-literature claim. Contribution and all downstream decisions remain outside this review.
