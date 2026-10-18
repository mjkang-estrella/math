# Family 128: reverse-complement factor-two target remains unresolved

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0. No candidate or acceptance is proposed. This second screen is distinct from family137 and from all r35 screens.

## Full research question

Input is any finite family of explicitly represented finite strings over an arbitrary explicitly encoded finite alphabet, together with an explicitly encoded involution cm of that alphabet. Define rc(s) by reversing s and applying cm letterwise. Fixed letters of cm and reverse-complement palindromes are allowed. Seek a deterministic algorithm, polynomial in total encoded input size including symbol labels and the involution table, that outputs a string containing s or rc(s) for every input s, of length at most twice OPT_RC. Empty families, empty strings and duplicates are included; substring domination is removed only with an orientation-consistent justification. There is no fixed alphabet, fixed input length, randomization, numerical oracle or promised orientation. This is a full research question recorded during discovery, not a frozen proved candidate.

## Source operations that must transfer

The pinned source is *A Polynomial-Time 2-Approximation for Shortest Common Superstring*, September24,2026. All seven substantive sections were read completely. `source-receipts.json` records the exact bodies. The source is an ordinary-string algorithm; it does not choose orientations.

In `sec:counts`, the downward recursion assigns an integer m(s) to every nonempty input substring. Extension inequalities and period-triggered inequalities force counts. The period rule is not merely a flow constraint: if m(v)>B_A(v;m), a shorter prefix w with |v|-|w|=kp must satisfy m(w)>=B_A(w;m)+k+1. `lem:counts` proves m(s)<=N_T(s) for every ordinary common superstring T. Hence W=sum_c m(c)<=OPT. Up/down multiplicities form a balanced hierarchical graph with W edges of each type and every required word present.

The subsequent `lem:layers`, collective-link and host-request operations, period-group processing, and `thm:connection` connect this base graph at additional up-cost at most W. Planned-link cycles are opened using a maximal periodic rotation and the saved period of an omitted outgoing link. Euler traversal yields an ordinary superstring of length at most 2W. The entire mechanism uses coherent integral oriented words, extension relations and periodic alignments, not only overlap-cycle costs.

The actual closest primary read is Ryosuke Yamano and Tetsuo Shibuya, *Improved Approximation Algorithms and Hardness Results for Shortest Common Superstring with Reverse Complements*, WABI2026, LIPIcs390 article2, [DOI10.4230/LIPIcs.WABI.2026.2](https://doi.org/10.4230/LIPIcs.WABI.2026.2). Its scope includes arbitrary alphabet involutions. Theorem1 gives 8/3, not2. Sections3–4 were read through Theorem13, including the actual matching gadget and cycle extraction.

That primary computes an optimal constrained cycle cover selecting exactly one formal orientation per input pair. It splits incoming/outgoing copies, uses auxiliary zero-weight edges to forbid simultaneous matching of a copy and the opposite orientation's incoming copy, and solves a general-graph perfect matching problem. It joins the matching's retained edges to their reverse-complement image. The resulting cycles occur in disjoint reversed pairs, so choosing one cycle per pair gives a valid optimal constrained cycle cover. Its approximation then uses periodic representatives and critical-rotation overlap bounds, leading to OPT_RC+(5/3)CYC<= (8/3)OPT_RC. These orientation-cycle and representative operations are already paid. Applying the new ordinary algorithm requires another argument relating its forced-count/connection construction to the original unoriented optimum.

## Exact obstruction to preserving OPT by cycle-cover orientation

Consider identity cm on {a,b,c}, so rc is ordinary reversal, and

S = {cabbbca, aaccbb, cbacbca, bbacbb}.

All eight strings in S union rc(S) are distinct and none contains another. There are16 orientation choices,24 Hamiltonian paths for each choice, and9 loop-free cycle-cover successor permutations for each choice. Every input is a distinct formal pair, so a cycle on the selected four vertices automatically contains neither both orientations nor an edge to its own opposite orientation.

For an orientation vector, let P be the shortest ordinary superstring length and C the minimum constrained cycle-cover cost. The exact table is:

| orientation | P | C | source forced-count W |
|---|---:|---:|---:|
|0000|21|21|21|
|0001|19|17|17|
|0010|22|22|22|
|0011|19|18|18|
|0100|22|22|22|
|0101|18|18|18|
|0110|22|22|22|
|0111|19|17|18|
|1000|19|17|18|
|1001|22|22|22|
|1010|18|18|18|
|1011|22|22|22|
|1100|19|18|18|
|1101|22|22|22|
|1110|19|17|17|
|1111|21|21|21|

The original string is orientation0, its reversal orientation1. For each path pi, the length is sum_i |s_i| minus the sum of maximal suffix-prefix overlaps along consecutive vertices. This computes the exact ordinary optimum here: order selected occurrences in any superstring by starting position. Substring-freeness makes their endpoints strictly increasing. Each consecutive starting-position gap is at least |s_i|-ov(s_i,s_j). Summing proves the path lower bound; merging by maximal overlaps realizes it. Thus minimizing these paths loses no possible ordinary superstring. An RC superstring chooses at least one orientation of every pair, so minimizing over all16 choices gives the exact RC optimum as well.

For each cycle successor permutation sigma, the cost is sum_i (|s_i|-ov(s_i,sigma(i))). Enumerating all derangements therefore covers every allowed cycle cover, including two disjoint 2-cycles. No Hamilton-cycle restriction is imposed.

The table proves OPT_RC=18 and minimum cycle-cover cost17, but **every** orientation achieving cost17 has ordinary optimum19. For example, orientation0101 has path order (2,0,3,1), zero-based, with string `cbacbcabbbcabbccaa` of length18. Orientation0001 has best path19; its cover (0 3)(1 2) has cost17. Full optimal paths, their concrete strings, cycle successors and costs are in `validation.json`. `checks.py` performs exact integer enumeration with no solver or heuristic. The finite table can be independently checked by these definitions; no numerical test is used as a universal theorem.

This refutes the proposed implication OPT(selected orientations)<=OPT_RC for an arbitrary, or even best tie-broken, minimum-cycle-cover orientation selection. It does **not** refute the final factor-two guarantee of an algorithm that uses these orientations and a sharper analysis.

In particular, the source's sharper guarantee is 2W, not merely 2P. The table explicitly computes the source's descending forced-count recurrence as an additional diagnostic. Some minimum-cycle orientations have W=17<18. Thus the present example does not refute choosing minimum-cycle orientations and proving W<=OPT_RC; it leaves exactly that stronger route open. Also, W is not universally bounded by C for every such orientation: orientations0111 and1000 have W=18>C=17. The unary check m(a^j)=h-j+1 for input a^h confirms why ordinary flow or cycle weights alone do not pay period forcing. No general minimum-over-ties W theorem was proved. A bounded further random search was exploratory and supplied no new certificate or theorem.

## Other attempted bridges and what is missing

Symmetrization is sound but only gives4: apply the ordinary source to S union rc(S). If T is RC-feasible, T rc(T) contains both orientations, so OPT(S union rc(S))<=2OPT_RC. The ordinary2 guarantee then gives4OPT_RC. This routine consequence earns no contribution credit.

Orbit occurrence counts N_T(s)+N_T(rc(s)) can provide symmetric lower-bound information, but do not select coherent integral oriented extensions. Dividing symmetric counts by2 can produce fractional base multiplicities. The source's connectedness argument retains all integral base edges and chooses actual periodic layers; an integral selection theorem with the same budget is unpaid. Reverse complementation reverses edges and exchanges up and down edges in the hierarchical graph. Closed-walk total cost is preserved, but edge costs individually are exchanged. A quotient graph and a chosen half of its Euler structure therefore need a proof, including fixed words, self-reversed components and consistency of period alignments. No such proof was obtained.

A meaningful next mathematical test within this family would be to prove or refute the existence of a polynomially selectable optimal constrained cycle cover whose chosen orientations satisfy the ordinary source's W<=OPT_RC, or to build a genuinely involution-compatible forced-count and layer connection construction. The matching gadget alone establishes neither property. The full factor-two question remains **UNRESOLVED**; the scope has not been narrowed to fixed alphabets, nonpalindromic inputs or fixed string length.

A feasible Lean support interface could certify the finite overlap table, permutation minima and the shortest-path characterization under substring-freeness. That would certify this failed-reduction example, not a factor-two algorithm, and no Lean compilation is claimed.
