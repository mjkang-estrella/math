# Symmetric count and half-Euler interfaces

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0. Technical support toward the unchanged full family128 RC factor-two target; no nomination or count. This uses the stipulated pinned source and the bounded primary/body reading documented in immutable r36 (manifest `cab895515b09212292a8fc5dc840b1992ed51eee836c7b7fa810a950d7d393d2`). Parent supplied the equivariant-count lead and independently identified the disjoint-text lower-bound argument.

## Symmetric count lower bound

Write rho(s)=rc(s). Remove empty requirements. Group input words into rho-orbits, and remove any orbit whose words occur as substrings in a different remaining orbit. This is legitimate: if s is a substring of t then rho(s) is a substring of rho(t), so any choice satisfying the longer orbit satisfies the smaller one. Select all words in the remaining orbits as the symmetric required set R. Let V consist of all their substrings including empty. It is rho-closed. Let L be the sum of lengths of one representative of every remaining input orbit, so L is bounded by the encoded input length.

Construct m on nonempty V in decreasing length, simultaneously on each rho-orbit. At a nonfixed orbit {s,rho(s)}, take the maximum of all source extension/period/requirement lower bounds for BOTH words, and assign that same integer to both. At a fixed word, take all ordinary lower bounds, impose at least2 when required, and round the maximum upward to the next even integer. At a nonfixed required word impose at least1. Missing words have count0. All constraints on a length-l word refer only to longer words, so this is an explicit finite recursion. The source's finite enumeration of periods applies unchanged, including nonleast periods. No iterative fixed point or real optimization oracle is involved.

Let T be any RC-feasible word and define

N(s)=N_T(s)+N_rho(T)(s)=N_T(s)+N_T(rho(s)).

This is the occurrence count in the **disjoint collection** of the two finite words T and rho(T). It is symmetric and even on fixed words, and satisfies the stated required bounds. The source occurrence lemma's induction extends to disjoint collections as follows. Extension inequalities hold componentwise and sum. Each blocking functional is linear, and counts blocked occurrences componentwise. If N(v)>B_A(v;N), an unblocked occurrence lies in one component; its k+1 period-spaced prefixes are distinct unblocked occurrences in that component. If N(v)=B_A(v;N)>B_A(v;m), some longer bracketing word r has integer positive difference N(r)-m(r); the same source multiplicity argument gives b_A,w(r)>=k+1. Every other difference is nonnegative by descending induction. Thus every ordinary bound imposed for s is at most N(s). The bounds for rho(s) are at most N(rho(s))=N(s), so their maximum remains dominated. At a fixed word, rounding up to even remains at most the even integer N(s). Therefore

m(s)<=N_T(s)+N_T(rho(s)) for every nonempty s,
W_sym=sum_(letters a) m(a)<=2|T|,
and W_sym<=2OPT_RC.

Taking T to be a concatenation of one input representative per orbit shows m(s)<=2L. There are polynomially many substrings and source period/blocking rules, each using polynomial-size integer counts. Orbit pairing and even rounding are also polynomial in the fully encoded input size. This proves a polynomial count construction; it does not construct the desired final superstring.

Remark on equivariance of the unpaired source rules: if v has period p and |v|-|w|=kp, its relevant prefix w is also its suffix. Reversal maps this period rule to another such rule, with reversed periodic text A'(i)=cm(A(|v|-1-i)). The text alignment for w agrees because |v| and |w| are congruent modulo p. Bracketing placements transform by j'=|r|-|s|-j. Thus the source bounds themselves should already pair; the maximum-of-both definition above avoids relying on this optional simplification.

## Equivariant base graph and parity

Use the source multiplicities u(s)=m(s)-sum_c m(cs) on pref(s)->s and d(s)=m(s)-sum_c m(sc) on s->suf(s). The graph is balanced by the source telescoping calculation, and has W_sym up edges and W_sym down edges. Symmetry gives u(s)=d(rho(s)). Pair edge copies accordingly. The reversing involution tau sends the up edge pref(s)->s to the down edge rho(s)->rho(pref(s)); it swaps tails and heads under rho and has no fixed edge, because an up edge cannot be a down edge.

At a nonempty fixed vertex s, its outdegree is

m(s)-sum_(c,d) m(csd).

The first term is even. The words csd are paired by rho; paired nonfixed words have equal counts, and fixed words have even counts. Hence the sum and outdegree are even. At empty, outdegree is sum_a u(a)=sum_(|s|=1)m(s)-sum_(|s|=2)m(s), not W_sym (which is total up cost). Each whole-length sum is even because its words occur in equal nonfixed pairs or are fixed words with even counts. Hence empty also has even outdegree. This verifies every fixed-vertex parity, not only parity at required words.

Adding a closed walk C together with its reversed image tau(C) preserves this property: at a fixed vertex, their combined increment to outdegree is outdeg_C(v)+indeg_C(v)=2outdeg_C(v). Balance and equivariance are preserved as well. The difficulty is paying for such pairs within the original connection budget.

## Half-Euler lemma

Let D be a finite nonempty balanced directed multigraph with a reversing involution tau on vertices and edge copies, with no fixed edge. Assume its underlying support is connected, it contains a fixed root r, and every fixed vertex has even outdegree. Then there is a directed closed walk starting at r using exactly one edge from each tau-pair. Its union with the tau-image uses every edge copy exactly once.

Proof by quotient incidence pairing. Form one quotient vertex per vertex orbit and one quotient edge per edge orbit, retaining its two incidences, including loops. At a nonfixed orbit choose representative v and label an incidence + if its lift is outgoing at v, and - if incoming at v. This is well-defined because reversing the chosen edge swaps its endpoint role and applies tau. For an edge from v to tau(v), both incidences have label+; the opposite case has two labels-. The number of + incidences is outdeg_D(v), and the number of - incidences is indeg_D(v), so they are equal. At a fixed vertex ignore signs. Its quotient degree is outdeg_D(v), hence even.

Pair all + incidences with - incidences at each nonfixed orbit, and pair incidences arbitrarily at fixed vertices. These pairings decompose the quotient edges into closed trails with the appropriate alternating rule. Each can be lifted to a directed closed walk: at a nonfixed orbit an incoming edge and the paired outgoing edge have compatible lifts, and at fixed vertices either edge orientation has a compatible lift. For a trail not containing a fixed vertex, alternation also makes the final incidence compatible with the first. At a fixed vertex the lift closes automatically.

If more than one trail occurs, connectedness supplies a quotient vertex shared by two trails. At a nonfixed vertex, switch two opposite-sign pairs crosswise; at a fixed vertex switch two pairs crosswise. This splices the trails into one without breaking the local rules. Equivalently perform ordinary Hierholzer splicing with the same incidence constraints. Repeating gives a single quotient Euler trail containing r. Lift it starting at r. It uses one lift of each edge orbit and ends at r, proving the claim. This is a finite polynomial construction in the explicitly materialized multigraph.

For the hierarchical graph, every edge changes word length by +1 or -1. Therefore any closed lift has equal numbers of up and down edges. If D has U up edges, it has U down edges, so there are U edge orbits and the half-Euler lift has U/2 up edges. Its visited words include at least one vertex from each nonempty vertex orbit of D: every used orbit has an incident selected quotient edge, whose lift visits one of its representatives. Hence every required input orbit is represented. A closed hierarchical walk through empty yields the usual ordinary output string, and its length equals its up count.

Consequently, an equivariant balanced extension D of the symmetric base graph, connected to empty, with at most2W_sym up edges and even fixed-vertex outdegrees, would give an RC superstring of length at most W_sym<=2OPT_RC. This is a conditional interface. The half-Euler lemma does not provide the needed extension or its budget.

## Unpaid connection requirement

The ordinary source connects an arbitrary eligible base graph at extra up-cost<=W_sym. Adding that extension and its tau-image is valid and preserves parity, but can cost2W_sym extra, not W_sym. One must prove an equivariant, parity-preserving connection at the same W_sym budget, or a different construction with the same final length bound. Simply applying ordinary connection and then selecting half its symmetrization does not establish2.

The source's ordered-window, collective-link, host-request and maximal-rotation operations are one-sided choices. Their reversed counterparts are valid operations, but pairing them is free only when disjoint paired layer budgets can be charged. Self-reversed primitive texts, fixed layers, host choices and cycle opening therefore need actual compatible constructions. Choosing a maximal rotation over both orientations may help with the final short-contact comparison, but by itself proves neither a paired decomposition nor budget feasibility. These are the current outstanding interfaces.

Update: the conditional same-budget extension above is now explicitly refuted by budget-counterexample.md (W_sym6<OPT_RC7). The supporting count and graph lemmas are not refuted. The technical3 construction still follows if the half-Euler interface and ordinary source connection are applied, but is inferior to the primary8/3 guarantee and earns no credit.
