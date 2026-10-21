# Core/forest integration and the unpaid global comparison

PREFREEZE / no nominee. These are feasibility calculations, not a frozen theorem, full author-proof submission, independent grade, or replacement for the old arbitrary-degree connected-switch question. Original prose: Myeongjin Kang, no affiliation, CC BY4.0; original code MIT. All pinned theorem statements AND their operative proofs are stipulated true.

## Retained question and credited baseline

For every n>=4 and every labeled degree vector d admitting a connected simple graph on [n], retain ALL connected realizations, including all leaves, densities and surpluses. P_c is Source131's half-lazy proposal: choose a uniform four-set and a uniform ordered pair of distinct perfect matchings, perform the switch if valid AND connected, otherwise hold. The desired operation is one uniform polynomial worst-start total-variation mixing bound. This is already the r30/r139 exploratory question, not a newly named conjecture. Nothing is frozen or nominated here.

The full eight-section Source131 proof pays unrestricted mixing and expected-polynomial exact uniform sampling. Its three-row and disjoint-pair operator arguments are at the unrestricted conditional measures; this round neither audits them nor silently changes their hypotheses. r139 already pays the sharp local connected pair-fiber comparison and explains precisely why the unchanged triangle-square constant fails. r30 already rules out polynomial-cost rejection from all degree realizations and polynomial maximum-fiber all-state retractions in the leaf-containing regime. Those operations and their limitations are credited, not repeated as new findings.

FGMS Section3.1/Lemma1/Theorem2 supplies a polynomial connected-state transfer when every degree is at least two: cycle-edge joining, bounded image distances and maximum fiber2n. The entire pertinent proof was read. CDGH's stronger explicit simulation and congestion analysis in Section4 is credited in its even-regular domain; it does not acquire arbitrary degrees by a change of notation. No inference of impossibility follows from a tree component lacking their chosen cycle edge.

## Exact macrostate measure

Write E=(sum_i d_i)/2 and ell=E-n+1. If ell=0, all connected realizations are trees. Classical Prüfer words with multiplicities d_i-1 provide exact independent uniform tree samples and count (n-2)!/prod_i(d_i-1)!. This does not by itself bound P_c mixing. If ell>=1, let C be the unique2-core vertex set, k=|C|, m=n-k, and H=G[C]. Then H is connected, each s_i=deg_H(i)>=2 and

 |E(H)|=k-1+ell.

To justify the decomposition, iteratively delete vertices of current degree at most one. Every deleted vertex has a unique route toward the surviving core. A deleted component with two core attachment points, or one containing a cycle, would have retained a degree-at-least-two subgraph, contrary to deletion. A connected graph with ell>=1 retains a cycle, hence a nonempty core; paths between retained vertices also survive, so the core is connected. Conversely a connected simple minimum-degree-two H with rooted trees attached once has exactly H as2-core.

Orient every attached tree away from C. The child counts are

 c_i=d_i-s_i for i in C,   c_j=d_j-1 for j outside C.

They are nonnegative and sum_v c_v=m. Put A=sum_(i in C)c_i. For m>0, the classical forest-volume identity of Pitman Theorem1 is

 sum_(forests rooted exactly at C) prod_v x_v^(children(v))
       = (sum_(i in C)x_i)(sum_v x_v)^(m-1).

Extracting x^c gives

 F(C,s) = (m-1)! A / prod_v c_v!.                         (1)

For m=0, F is1 if s=d and0 otherwise; for m>0,A=0 it is0. This treats isolated roots and all zero child counts. The forest count depends on C,s, not on the arrangement of H. Uniformity on the full realization space therefore disintegrates into a macrostate law

 mu(C,s) = N_conn(C,s) F(C,s) / Z_conn(d),                 (2)

followed by independent uniform choices of the connected core H and a forest with child counts c. Equations(1)–(2) are classical counting/composition, not substantial-contribution evidence.

## The forest and fixed-core sampling costs are paid

There are m!/prod c_v! functions from the m labeled nonroots to parent labels with multiplicities c. Generate one uniformly by a uniform multiset permutation. Permit self-loops and directed cycles at this proposal stage, and accept exactly when every nonroot reaches C by iterating its parent. Accepted functions are exactly the rooted forests in(1). Their probability is

 F(C,s) / (m!/prod c_v!) = A/m >= 1/m                       (3)

on every feasible nonempty-forest macrostate. Conditional uniformity is exact. Cycle testing and a multiset permutation have polynomial bit cost; expected trials are at most m. Acyclicity is thus not an exponential rejection debt once C,s have been fixed. The root-set-empty tree case was treated separately.

For fixed feasible C,s, Source131's exact core sampler and FGMS's minimum-degree-two fiber bound give an exact connected core sample with at most2k expected unrestricted trials. Small k<4 is enumerated directly. The core sampler and forest sampler use independent randomness.

The composition extends beyond separate fixed fibers. Define

 Z_allcore = sum_(C,s feasible) N_all(C,s) F(C,s),

with precisely the same constraints and boundary conventions as(1)–(2), but N_all counts all simple core realizations, connected or not. FGMS's bound implies term by term

 N_all(C,s) <= 2k N_conn(C,s) <= 2n N_conn(C,s).

Thus Z_conn <= Z_allcore <= 2n Z_conn. If one could draw C,s proportional to N_all F, then draw an unrestricted uniform H and the forest, rejection only when H is disconnected would accept with probability at least1/(2n) and yield the exact uniform connected realization. The old exponential all-graph rarity does not obstruct THIS distribution: it has integrated the trees before allowing disconnected cyclic cores. This is the strongest completed sampling reduction here. Its starting macrostate sampler has NOT been implemented or proved polynomial. An exponential number of macrostates alone does not prove that task impossible.

## Variable-core weights and the attempted matching composition

Set D=prod_v(d_v-1)!, valid since connected n>=4 implies d_v>=1. On an arbitrary simple graph H with support C and positive degrees s_i>=2, define at each vertex

 f_i(0)=1, f_i(1)=0,
 f_i(s)= (d_i-1)!/(d_i-s)! for 2<=s<=d_i,
 f_i(s)=0 otherwise.

For |C|=k<n and |E(H)|=k-1+ell, its macrostate contribution, after multiplying by D, is

 (n-k-1)! (sum_(i in C)(d_i-s_i)) prod_(i in C)f_i(s_i).    (4)

One must sum over ALL such H and k; the k=n contribution is handled separately by s=d. This gives a concrete weighted subgraph partition problem with a support-size/excess constraint and a marked slack sum, not merely the phrase 'sample the core'. Introducing variables y for positive-degree vertices, z for edges and u^(d_i-s_i) for positive-degree slack represents the sum as the y^k z^(k+ell-1) coefficient of u(d/du) of its finite graph partition polynomial, evaluated at u=1, times (n-k-1)!/D. This is an exact algebraic representation, not an efficient coefficient-extraction algorithm.

The actual Source113 companion Corollary10.1 and its constant-fiber Tutte gadget count arbitrary-host FIXED-degree subgraphs and sample them approximately. The operative gadget proof and the deletion-sampler proof were read. They pay N_all(C,s) for an explicitly specified C,s. Summing exponentially many independently countable fibers, or replacing fixed degrees by the above f_i, needs a further algorithm; it is not supplied by the statement of that corollary.

The matching route was tested beyond the elementary parity obstruction. McQuillan1301.2880v1 allows nonnegative rational edge weights AND unmatched-vertex fugacities in matching circuits, compiles these to unweighted perfect matchings in polynomial binary size, and proves every such circuit's signature is windable. The relevant closure, parity-extension, weight-compilation and necessary-inequality proofs were read. Thus large factorial weights are not by themselves an obstruction: binary rational matching weights are already paid.

For d_i>=3, pin all but three edge coordinates of the unmarked local signature to0. Its symmetric values at Hamming weights0,1,2,3 are

 (1, 0, d_i-1, (d_i-1)(d_i-2)).

McQuillan's necessary ternary inequality at000 is f(000)f(111)<=sum of the three complementary weight1/weight2 products. Here the left side is positive and the right side zero. Hence this particular local signature has no nonnegative matching-circuit realization, even allowing fugacities. This is a classical criterion applied to a concrete attempted composition; it is NOT an impossibility of an approximation-preserving reduction, a signed/holographic transformation, a nonlocal construction using the fixed-excess constraint, or a different positive global representation. Search results on broader Holant approximation were navigation only; their proofs were not read and they supply no blanket claim either way.

## Special-surplus summation is paid, not nominated

For ell=1, a connected core is a cycle, so s_i=2 and N_conn(C,s)=(k-1)!/2. For k<n equation(2) has unnormalized core-set weight

 ((k-1)!(n-k-1)!/(2D))
       (sum_(i in C)(d_i-2)) prod_(i in C)(d_i-1).          (5)

Eligible vertices have d_i>=2. The k=n boundary exists exactly when every degree is2 and has (n-1)!/2 cycles. For the other k, the weighted subset sum in(5) is computed in polynomial time by an elementary-symmetric dynamic program and its marked first moment: give each eligible vertex weight w_i=d_i-1; select a distinguished i with additional weight d_i-2 and select k-1 other vertices with product weights. Summing over the mark gives exactly the slack sum. Backtracking this positive DP, choosing a uniform labeled cycle, and using(3) gives an exact expected-polynomial independent sampler at ell=1. All factorial and product weights have polynomial bit length.

This is an elementary special case of known tree-based enumeration/sampling operations and is not a full-scope or supporting nominee. It neither gives a uniform-in-ell bound nor proves switch-chain mixing. It is included to avoid leaving a tractable substep unpaid or treating the mere presence of variable core size as a proof of difficulty.

Bhamidi–Sen1608.07153v3 supplies a different compatible representation: a plane tree tilted by the number of admissible sets of ell leaf pairs, followed by gluing. Section6 proves a constant graph multiplicity prod(d_j-1)! by depth-first exploration. The proof is finite and directly covers the relevant leaf-containing inputs when its construction is nonempty; its asymptotic hypotheses must not be confused with a finite obstruction. Its Remark9 rejection discussion costs a factor m^(2ell)/epsilon with an additional lower bound on the tilt normalizer. This does not yield one fixed polynomial for arbitrary ell. Horvat–Modes2009.03747v2 gives computable weights for an exact biased sequential sampler; importance weights alone are not a uniform-sampling guarantee. Both representations are credited, and neither is ruled out as a starting point for a stronger method.

## Sampling does not yet control the specified chain

Even an efficient independent sampler for(2) would not alone prove the original P_c mixing statement. Here is a precise sufficient comparison, retaining the genuine transitions rather than inventing a macrostate chain.

Partition Omega_c by alpha=(C,s); for trees use one empty-core macrostate. Let P_alpha be the restriction of P_c to its fiber, with departing transitions made holding. Let g_* be a common positive lower bound on all nonconstant restriction gaps, if such a bound is available. Define the actual averaged projection

 Pbar(alpha,beta)= sum_(G in alpha) pi(G|alpha)
                         sum_(G' in beta)P_c(G,G').

It is reversible for mu, and let gbar denote its gap. No bound on g_*,gbar is proved here. With fbar(alpha)=E[f|alpha], Vw=E_mu Var(f|alpha), and E_P the actual Dirichlet form, total variance gives Var(f)=Vw+Var_mu(fbar). Restriction gaps would give Vw<=E_P/g_*.

For every crossing edge G in alpha,G' in beta,

 (fbar(alpha)-fbar(beta))^2
 <=3[(fbar(alpha)-f(G))^2+(f(G)-f(G'))^2
                                      +(f(G')-fbar(beta))^2].

Multiply by pi(G)P_c(G,G')/2 and sum. Reversibility and exit probabilities<=1 give E_Pbar(fbar)<=3 E_P(f)+3 Vw. Hence a projection gap would imply

 Var_pi(f) <= [g_*^(-1)+3 gbar^(-1)(1+g_*^(-1))] E_P(f).  (6)

This is a direct standard variance/energy composition, not new contribution evidence. It makes explicit that endpoint conditional means need not equal the stationary fiber means; simply applying Jensen to a product law across macrostate transitions would skip this issue.

Within fixed C,s, independent core/forest sampling is paid above. Comparison of those resamplings to actual connected switches is still needed. An attempted parent-label transposition chain is insufficient even for a single-root path: every two nonroot vertices are ancestor-related, and swapping their parents creates a directed cycle. Undirected segment-reversal switches can repair that example, so it does not rule out a stronger forest comparison. More generally one switch can change many2-core vertices along an attached path, so neither a nearest-neighbor chain on core size nor a product chain on core membership is the actual projection. No uniform flow/congestion estimate for(6) was obtained. The old global H_c Poincare route remains another possible approach, with all r139 local progress intact.

## Status and finite diagnostics

The exact program checked all33,864 labeled simple graphs on3–6 vertices, grouped their connected core/forest fibers (23,864 nonempty groups), and checked(1) in every group. It checked(5) for476 unicyclic labeled degree vectors and(3) across878 parent maps/170 multiplicity fibers with fixed representative root sets. These are finite exact diagnostics, not proofs of general mixing, an independent correctness review, or formal support.

No full arbitrary-degree connected-switch theorem was proved. The unpaid operations are the full variable-surplus weighted-core sampler and, separately, polynomial restriction/projection or flow bounds for the actual chain. The forest count, its A/m acceptance, fixed-core connected comparison, special-surplus DP, rational-weight compilation and DFS multiplicity are paid compatible operations. The local windability failure limits one route only. No reduced target, new conjecture name, grade, acceptance/count, current-open, priority, exhaustion, or all-method impossibility claim is made.
