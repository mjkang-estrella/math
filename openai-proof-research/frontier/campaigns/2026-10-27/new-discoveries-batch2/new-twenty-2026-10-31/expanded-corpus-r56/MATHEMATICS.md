# r56 mathematical attempts — zero credit

## 361679: full ordinary source-corollary argument, not a Lean endpoint

Primary body read: arXiv 2402.00237, Section 4.2, Proposition 4.11 and Proposition 4.12 with proofs, Lemma 4.13 with proof, Example 4.22 and following unnumbered conjecture. The metadata sentence suggesting disproved status has no authenticated counterexample and is not used.

Use zero-based indices. For a word w of length m starting in 2 define Z(w)=sum_{0<=j<m,w_j=1} rho^j. Proposition 4.11 gives

f_w(1)-rho = (1-rho)(1-Z(w)).

Indeed sum over all positions rho^j=(1-rho^m)/(1-rho), and the positions labelled 1 complement those labelled 2. Thus Proposition 4.12 says a reduced banned word alpha starts in 2, has Z(alpha)>=1, and every proper contiguous subword starting in 2 has Z<1. Lemma 4.13 says alpha ends in 1.

Let n=|alpha| and gamma be alpha with its last letter deleted. I claim every subword beta of gamma gamma that starts in 2 and has length at most n has Z(beta)<1. A subword inside one copy of gamma is a proper subword of alpha, so this follows immediately. Otherwise it crosses the join. Let s in {0,...,n-2} be its starting offset in the first gamma, t=n-1-s the length up to the join, and l=|beta|-t the length after the join. Thus 1<=l<=s+1.

If s=0, length at most n permits only l=1; that new letter is gamma_0=2. Therefore Z(beta)=Z(gamma)<1.

If s>0, let A=Z(alpha_s ... alpha_{n-2}), and B=Z(alpha_0 ... alpha_{l-1}). The suffix alpha_s ... alpha_{n-1} is proper and starts in 2. Its last letter is 1, so A+rho^t<1. The prefix of length l is proper, starts in 2, and has B<1. Concatenation gives

Z(beta)=A+rho^t B < A+rho^t <1.

Every reduced banned alpha^j with j<=i has length at most n, begins in 2 and has Z>=1. None can therefore occur in gamma gamma. This proves the exact doubled-prefix conclusion, including equality thresholds for rho and arbitrary numbers of reduced banned words. Only positivity of rho and the source characterization were used; no enumeration completeness is assumed.

Assessment: this is an explicit full-scope deduction from the same source's elementary characterization and last-letter lemma. It is a serious routine-source-corollary exclusion under this assignment's standard; shortness alone is not the reason. No assertion is made that the final conclusion was printed previously. Root may independently adjudicate that assessment. No accepted credit, novelty clearance, independent review, or literal Lean endpoint exists. A formal candidate would still require the actual top-address language, its subword semantics and the proof of Proposition 4.12 from the address-map definitions, rather than declaring the weighted-sum test to be the banned-word predicate. Those semantic bridges are not supplied in Lean here. The beta-shift literature search is only a lead: Cyr–Kra–Petite, Strong approximations of shifts, Lemma 5.5 characterizes minimal forbidden words; its body was exposed by search but the top-address conjugacy and full subsumption bridge have NOT been checked.

Diagnostic: banned_scan.py performs exact integer arithmetic on rational rho, using f_{wd}(1) recurrence and rejection of all previously found forbidden suffixes. Eight scans reached length 20; rho=51/100 stopped at length 19 after exceeding the 400,000-state cap. All runs finished without a witness. The above ordinary proof does not depend on those scans.

## 362246: sustained exact-cover route; no universal theorem

Primary body read: arXiv 2403.06318 Section 10, Definition 10.1, Conjecture 10.2, translation to Young diagrams, a=3,4,5 discussion and proof construction. Also introduction's explicit tilted order and rank definition. Latest fetched body includes larger verification for weaker standard partitions, not a proof of the ribbon conjecture.

Coordinates: x in {0,...,a-1}^{a-1}, c'<sum x<=c; rank T(x)=sum (i+1)x_i. The order is componentwise in suffix sums y_i=sum_{j>=i}x_j. Covers increase y_i by one: x_0 increases, or x_{i-1} decreases while x_i increases. This derives the graph used by ribbon_scan.py, rather than guessing an adjacency rule.

Every ribbon has exactly a vertices and consecutive ranks. If rank counts are h_k and the number of ribbons starting at rank k is b_k, then h_k=sum_{j=0}^{a-1}b_{k-j}. Hence b_k=h_k-sum_{j=1}^{a-1}b_{k-j} is forced. Nonnegativity is a necessary condition; this is the coefficient quotient by [a]_q, not a sufficient condition for chains. The second script uses it to remove paths whose initial rank has zero quota.

At a=6,c=5, c'=1, there are 246 vertices. The first 8-second MILP timed out. The start-rank pruning run found 41 disjoint six-vertex paths within 25 seconds. The witness was checked for complete vertex coverage and disjointness, and paths were generated only along actual covers. It is retained as a diagnostic parameter instance, not a formal theorem and not new-solution credit. At a=6,c=7 (510 vertices), both runs timed out without a primal witness. The larger c=11 slice produced 1,530,272 paths and triggered the finite path cap; no solve was attempted. Full logs retain these limitations.

Remaining exact mathematical problem: a uniform construction for every a and coprime c, or a certified obstruction to exact covering in one source-valid slice. Rank nonnegativity alone discards all order information. MILP timeouts are not infeasibility certificates. No Lean work is justified on the isolated positive parameter case.

## 361793: classical odd-resistance obstruction and normalization HOLD

Read actual current source 2402.06008 last page of conclusions, Conjecture 16 and Corollary 17 with proof. It explicitly defines er as a minimum matching of edges removed followed by suppressing incident 2-valent vertices, then states r>=2er.

Read actual older 1212.3641 Section 7 construction/proof: networks N1,N2 built from Petersen multipoles; N2 stays uncolourable after deleting one nonterminal vertex, by parity and conflicting terminal colours. Its circuit construction with r copies N2 and one N1 has resistance 2r+1. For r=1 the body explicitly gives a cyclically 4-connected 44-vertex snark with resistance 3.

There is a direct bound r(G)<=2er(G) for the stated matching-reduction convention. Pull a proper colouring of the suppressed graph back to its unsuppressed paths. At every endpoint of the removed matching delete one of its two nonmatching incident edges (at most two deleted edges per matching edge). Every such endpoint now has at most one coloured nonmatching incident edge. Reinsert each matching edge and give it a colour avoiding those at its two endpoints; three colours suffice. Other vertices stay proper. Components consisting only of degree-two vertices can be broken by these deletions and coloured as paths. Consequently resistance three forces er>=2 and contradicts r>=2er. This would be an immediate old-example corollary, not a substantive newly constructed snark result.

Material qualification: the cited Allie predecessor's primary abstract uses a vertex-reduction normalization and no factor two; it was read only at abstract depth. The PDF request returned 403 and was not retried. Its full definitions/proof body remain unread. Do not promote a possible normalization/transcription issue to a campaign solution. This route is parked/excluded from discovery investment, with the explicit old-result bridge retained. No literal graph certificate or Lean endpoint was generated.

## Direct source-result exclusions

361591: actual 2401.12670 introductory Theorem 1.8 and Section 5 establish a d-rigid spanning subgraph edge-disjoint from a spanning tree at connectivity d^2+3d+5. A d-rigid graph is d-connected (source rigidity bridge). Thus deleting the tree retains that spanning subgraph and gives the exact k-connected remainder; the source itself explicitly announces the resolution. Read theorem scope and selected Section 5 proof passages, not every rigidity lemma or full paper. No new proof/Lean credit.

361623: actual 2401.14768 Theorem 7 and its complete short proof immediately precede Conjecture 8. Substitution n[z,g]=z(g-1)+1 gives the complete conditional claim. This is an explicit same-source conditional arithmetic consequence, not a solution of the antecedent Behzad–Chartrand–Wall conjecture. No formalization needed for exclusion.
