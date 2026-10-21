# Source129: return-aware probabilistic feasibility, without a nominee

PREFREEZE. No theorem statement was frozen, no author-proof or supporting-result nominee is submitted, and no independent grade or count is assigned. All old source/target scopes and dispositions remain unchanged. These are original feasibility notes (CC BY4.0), not a manuscript. Their principal operations are explicitly credited below.

## 1. The unchanged source interfaces and actual history

Write R_h for ALL binary relations on [h], with product in path order, and L_h for ALL finite words over R_h having nonempty product. The empty word is live. The pinned source gives an (h+2)-state no-left-move NFA for L_h and requires

    s >= 2^(floor((h-2)/127))/2 - 1

for EVERY unrestricted read-only one-head s-state 2NFA for its full complement. Its deterministic companion gives

    4(s+2)^2 >= 2^floor((h-2)/31)

for every 2DFA for L_h. Finite accepting runs, arbitrary word lengths, stays, partial transitions and nonaccepting infinite computations are all retained. No alphabet or transition-table-size replacement is imposed. Pin and operative proof operations are stipulated true.

Both mathematical source bodies have been read in full. In particular, the deterministic representation uses a functional configuration graph, its sink TREE, symbol-local candidate slots and Brauer matchings. The complement proof instead uses arbitrary finite-path diagrams, inclusion monotonicity, missing recurrent classes, common-set transport, nested-idempotent loss and full relation corners. The proof needs the ENTIRE relation image and exact finite-semigroup idempotent powers, not just the displayed edge additions. These are credited inputs, not proposed new work.

Actual r31 already proves the fixed-binary transfer (14h+2 source states, constant-factor two-way macro pullback); r38's larger encoder is explicitly redundant. The first r153 history scan found both before any proposed new derivation. The later focused scan located r117's original automata.md, read AFTER the first live sampler calculation and BEFORE this integrated note. It already gives rational O(h)-state restart recognition of L_h and its complement. The sampler is therefore both classical composition and actual prior project work. No alphabet/state-constant/coin-denominator variant is offered as a new finding. The late-read chronology is retained in note01.

## 2. Which error orientation the source already handles

Consider a probabilistic two-way machine with finitely many states and arbitrary real transition probabilities. If it accepts each empty-product word with positive probability, and accepts every live word with probability ZERO, replace each positive-probability transition by a nondeterministic choice. Finite acceptance has positive probability exactly when at least one finite positive-probability accepting path exists: the accepting event is a countable union of finite cylinder events. The resulting 2NFA recognizes exactly the complement of L_h with the same states (up to acceptance-convention normalization). The source bound applies directly.

This argument also handles a zero-error, almost-surely halting decider, by reading its rejecting outcomes as acceptance for the complement. It does not handle the opposite one-sided orientation, where live inputs may have a small positive chance of rejection, nor general two-sided error. Repeated majority amplification to a positive error epsilon' does not turn positive wrong paths into impossible paths. Taking an infinite amplification limit does not preserve a fixed finite state count or finite accepting events. This is a routine support consequence, not a nominee.

## 3. The compatible restart operation really defeats the unrestricted extension

For clarity retain the already-paid r117 construction at its exact original normalization. For w=R_1...R_ell let N(w) count paths (p_0,...,p_ell) with (p_(i-1),p_i) in R_i, and set Q=h^(ell+1). A round chooses a path-sampling branch or a calibration branch equiprobably. The path branch chooses all vertices independently and uniformly, checks the scanned edges in its finite transition table, and accepts at the right marker only if every edge was present. Calibration survives its initial coin with probability 1/(2h), and each letter with probability 1/h, rejecting at the right marker if it survives. Failed trials physically rewind to the left marker and restart. Thus

    a(w)=N(w)/(2Q),    b(w)=1/(4Q),
    P_accept(w)=a/(a+b)=2N(w)/(2N(w)+1).

There is no input-length counter or teleporting head. O(h) states suffice. A round has O(ell+1) steps, the halting chance is at least 1/(4Q), and expected time is O((ell+1)h^(ell+1)); halting is almost sure. The empty word has N=h. For N=0 acceptance is zero; for N>=1 it is at least 2/3. Swapping the two terminal labels decides the complement with the same error and time. On a live word, the complement machine still has the positive wrong-acceptance probability 1/(2N+1), so section2 cannot be applied to it.

Yakaryilmaz--Say, arXiv:0903.0050v2, Lemmas1--4 give the exact restart ratio, time accounting and physical rewind; Lemma7 uses the same small-success/small-rejection calibration (stated there in a quantum model, whose proof operation here is directly classical). r117 separately cites their postselection paper. These operations are available, not unpaid. The power-of-two variant sketched in live note01 changes only rational constants. Applying the same path sampling to the actual r31 total binary NFA also handles malformed encodings according to that NFA's language. This is a credited composition, not a new binary or randomized result.

Consequently the attempted unrestricted bounded-error exponential state lower bound is false for this family. This does NOT refute either pinned theorem or any old frozen target, and does not claim that probabilistic methods cannot yield a time-dependent lower bound.

## 4. Exact segment composition retains ALL returns and nontermination

A probabilistic segment with s entry labels from each side has nonnegative matrices F,B,L,R recording first exits, using the source's directional conventions: F is left-to-right, B right-to-left, L left-return and R right-return. Let H^+,H^- have two terminal columns, accept/reject. Every row has total mass at most one; its deficit is the probability of never exiting or halting. For juxtaposed segments a,b, define K=sum_(k>=0)(L_b R_a)^k and J=sum_(k>=0)(R_a L_b)^k. The exact formulas are

    F_ab = sum_k F_a (L_b R_a)^k F_b,
    B_ab = sum_k B_b (R_a L_b)^k B_a,
    L_ab = L_a + sum_k F_a (L_b R_a)^k L_b B_a,
    R_ab = R_b + sum_k B_b (R_a L_b)^k R_a F_b,
    H_ab^+ = H_a^+ + sum_k F_a (L_b R_a)^k (H_b^+ + L_b H_a^-),
    H_ab^- = H_b^- + sum_k B_b (R_a L_b)^k (H_a^- + R_a H_b^+).

These are sums of the COMPLETE nonnegative products shown. One must not form an undefined infinite entry of K or J and then multiply it by zero. Each product sum is at most one entrywise because the associated first-exit/halting events are disjoint. Paths trapped forever contribute only to the deficit. When the relevant transient restriction has spectral radius below one, the sums can be computed with an inverse. Otherwise first remove the states with no route to an output; solve on the remaining transient subsystem and assign zero output probability to the removed states. This gives the least nonnegative solution, not an arbitrary solution of a singular linear system.

Proof: partition finite trajectories by the number of completed alternating returns at the join, and by whether they finally exit or halt in a or b. The strong Markov property supplies the products. Expanding or contracting visits to a consecutive block preserves these disjoint events, so composition is associative, even with internal recurrence. This is the probabilistic form of the source path expansion and the primary Markov first-exit operation. It is not a new obstruction.

Exact equality of complete body summaries makes all external contexts have the same acceptance probability. Therefore, if a bounded-error machine recognizes L_h, equality of two summaries implies equality of their relation products, by surrounding them with singleton identities I_{p},I_{q}. The generated (generally infinite) summary semigroup thus has a well-defined surjection onto R_h. This observation retains the source's full relation-image requirement; it does not supply a finite matching representation or an order-reversing support image.

Three distinctions matter. First, support inclusion preserves existence of finite accepting paths, but need not preserve a probability threshold. Second, a stochastic summary can have infinitely many distinct powers: a forward-survival probability r in (0,1) becomes r^k, never an idempotent at finite k. Third, passing to closure need not preserve threshold information after unbounded returns. For a single transient state with acceptance mass a, rejection mass b and return mass 1-a-b, the probability is a/(a+b). The sequences (a,b)=(u,u^2) and (u^2,u), u decreasing to zero, have the SAME support for every u>0 and the SAME limiting kernel, but their acceptance probabilities tend to 1 and 0. This demonstrates a real continuity failure at a closed recurrent limit. It does not exclude a more careful, time-aware compactness or corner construction.

## 5. Relative perturbation already handles that difficulty when time is controlled

The strongest compatible comparison read here is Dwork--Stockmeyer (1990), actual author-posted paper, Lemmas4.1--4.3 and Theorem6.1. Lemma4.1 derives a multiplicative absorption comparison from the Markov chain tree theorem. Leighton--Rivest, MIT/LCS/TM-249, Theorems1--2 and the complete graph-theoretic proof, have also been read visually. Their positive forest formula includes recurrent classes; for an absorbing chain it gives the absorption probability as a ratio of nonnegative sums of fixed-degree monomials. Thus same-support transition probabilities within a factor beta give absorption probabilities within beta^(2m) in an m-state chain, regardless of the number of returns. An additive-instability example alone cannot dispose of this operation.

Dwork--Stockmeyer Lemma4.2 goes further. If two m-state chains are beta-close mod lambda (corresponding entries are both <=lambda, or both >lambda and within factor beta), and both expected absorption times from the designated start are at most t, then

    a(P') >= (1-2 lambda m^3) beta^(-2m) a(P)
             -4 sqrt(lambda m t).                         (1)

The proof removes rare transitions, controls the resulting error using expected time, and applies the forest comparison to the large transitions. It already includes arbitrary repeated visits and both chains' expected times. Their Lemma4.3 quantizes logarithms above the cutoff and obtains

    [alpha_epsilon c (log T(n)+log(cn))]^(c^2) >= N_L(n)

for n beyond its stated epsilon-dependent threshold, with N_L(n) the number of pairwise distinguishable prefixes. Their Theorem6.1 then gives a 1DFA with at most c^(b c^2) states for error epsilon and time a n^d, where b depends on epsilon, a AND d. These dependencies cannot be declared uniform over a family whose time prefactors grow. The complete statements and proofs were read, not imported from a survey snippet.

## 6. Integrated singleton-context calculation, including the time parameter

Here is a direct application of (1) to ALL 2^(h^2) relation letters. It avoids replacing a two-sided relation distinction by a one-sided prefix count. It is a classical packing composition, not a substantial nominee.

Suppose an s-state 2PFA recognizes L_h (or its complement) with error epsilon<1/2 and finite expected halting time at most T_3 on EVERY input of length3. All transition probabilities may be real; arbitrary returns and stays are allowed. Set

    g = 1-2 epsilon,  m=5s+2,  t=max(1,T_3+1),
    lambda=min(g/(16m^3), g^2/(256mt)),
    beta=exp(g/(8m)),
    B=1+ceil(ln(1/lambda)/ln(beta)).

Then the paid comparison gives the necessary bound

    2^(h^2) <= B^(3s^2).                                   (2)

To check every interface, encode the local transition row of a relation letter by its at most 3s^2 numbers indexed by old state, new state and displacement -1/0/+1. Terminating states have fixed rows. Each number is put into the small bin [0,lambda], or into logarithmic bins on (lambda,1] of multiplicative diameter at most beta. This uses at most B bins per number.

If two distinct relations U,V had the same signature, choose (p,q) in their symmetric difference. The full inputs I_p U I_q and I_p V I_q have different membership. Each full input has five tape cells INCLUDING its distinct markers. Keep all 5s configuration labels, adding one common accept sink and one common reject sink. An old terminal configuration moves deterministically to its sink in one additional step. This prevents aggregating several transition entries and invalidating the bin condition. Pad inaccessible configurations if necessary. The two resulting m-state chains differ only in the middle cell's row entries, and are beta-close mod lambda; their expected absorption times are at most t. Inaccessible recurrent states are allowed by the primary lemma. On the accepting instance a(P)>=1-epsilon, while the rejecting instance has a(P')<=epsilon.

But 2lambda m^3<=g/8, beta^(-2m)=exp(-g/4)>=1-g/4, and 4sqrt(lambda mt)<=g/4. Equation(1) therefore gives

    a(P') >= a(P)-g/8-g/4-g/4
          >= 1-epsilon-5g/8
           > epsilon,

a contradiction. Hence all 2^(h^2) signatures differ, proving (2). The same proof swaps yes/no contexts for the complementary language. There is no input-length promise in the machine's decision problem; length3 is used only as a set of mandatory test inputs.

For fixed epsilon and polynomial T_3 in h, (2) has the scale s=Omega(h/sqrt(log h)) when s<=h (the case s>h is already stronger than that displayed lower bound). It does NOT give an exponential state lower bound. The actual O(h)-state restart machine has T_3=O(h^4), so this limitation is witnessed by a compatible full-language machine, not only a weakness of a local estimate. Dwork--Stockmeyer's all-length polynomial-time simulation can separately be combined with the source deterministic lower bound; it yields only b s^2 log s=Omega(h) with b retaining its time dependencies. Neither consequence is a new source-level exponential mechanism.

## 7. Why the source's long-product induction has not been paid in this setting

The finite source induction simultaneously needs exact idempotent lifts, unit lifts, common support/missing-class transport, and an additive budget across a chain of changing corners. Exact stochastic summaries give full relation images and exact composition, while the primary forest/rare-transition method gives a time-dependent approximation stable for a fixed bounded-length comparison. These facts do not yet provide all those induction interfaces on the SAME object.

In particular, bins used in (2) are not asserted to form a monoid congruence. Concatenating representatives changes first-exit probabilities through the geometric sums in section4. Choosing new cutoffs independently in each source corner would discard the common-budget requirement. Limiting idempotents cannot be substituted for exact finite powers without preserving the isolated language gap through all needed contexts and controlling the time or rare mass expended. The scalar limiting example shows why that extra justification is necessary; the forest theorem shows why the example is not a universal obstruction.

For an exploratory time-restricted extension, the unpaid operation would therefore be a time-aware representation or common loss-budget argument compatible with all source corner restrictions and the primary return/rare-transition bounds, or a different full construction/argument. No such operation was obtained. No assertion is made that it is impossible, that a named time-restricted conjecture is currently open, or that the displayed residual is itself a finding. No restricted theorem was frozen as a substitute for the failed unrestricted extension. There is no nominee.

The work ends with credited exact source proofs, credited r31/r38/r117 operations, exact return-aware reduction and bounded primary packing, not a renamed baseline. All old full/technical/failed statements and H138/T185R144 dispositions remain unchanged. No correctness/contribution grade, priority, exhaustive-search certificate, acceptance or count is supplied.

## Bounded diagnostic, not a gate

The exact rational diagnostic compares the displayed composition with an independent absorbing-chain solve for324 segment pairs (including a closed trapped join),120 triples, and72 small forest-sum identities. It checks the credited restart ratio on all4369 h=2 relation words of length at most3. It also records a precise failure of an undirected-walk shortcut: R1={(0,0)}, R2={(0,0),(1,0),(1,1)}, R3={(1,0)} has empty directed product, but its undirected layered graph has the path (0,0),(1,0),(2,0),(1,1),(2,1),(3,0). This rejects only that shortcut; oriented refinements, source/classical operations and time-aware methods are not excluded. Four rational recurrence examples check the limiting instability discussed in section4. None of these finite checks proves an arbitrary-size lower bound, a new contribution or an independent gate.
