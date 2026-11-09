# Mathematical attempts and exact residuals

## 337160: a missing minimum-location exception

The actual source is Brouwer–Cioabă–Ihringer–McGinnis, arXiv:1709.09011v2, revised 20 April2018, manuscript dated23 April2018. Section6 p20 gives the eigenvalue formula; Conjecture6.2 p21 asserts unimodality of absolute values with specified exceptions and specifies the minimum index. In particular, for e=3/2 it specifies i=floor((d+e+1)/2). This is a separate assertion from the location of the smallest *signed* eigenvalue in Conjecture6.3. We do not confuse them.

Choose q=4, e=3/2, d=4, j=2. The field parameter is a square prime power, as required for the unitary polar families. Put qe=q^e=8. The source displayed Gaussian sum, evaluated with exact rational products, gives:

|i|summands|C_2(i)|
|---|---|---|
|0|91392|91392|
|1|−168+5376|5208|
|2|4−200+256|60|
|3|84−168|−84|
|4|1428|1428|

Thus the absolute values strictly decrease to60 at i=2 and strictly increase afterwards. The unique minimum is2, whereas floor((4+3/2+1)/2)=3. The counterexample is neither a tied-minimum ambiguity nor one of the listed exceptional tuples. It refutes the *minimum-location clause*, not unimodality itself. Even the weaker existential interpretation of a tied minimum fails.

The diagnostic first used the coefficient of z^j in

    product(s=0..d-i-1)(1+qe*q^s*z) * product(s=0..i-1)(1-q^s*z).

Expanding and applying the finite q-binomial identity gives exactly the displayed Gaussian sum after setting a=i−h and b=j−i+h. A separate direct-sum calculation produced the same five values. The Lean certificate bypasses this generating-function bridge and checks the printed sum itself. For natural arithmetic, b is encoded as j−(i−h); encoding it as (j−i)+h would be WRONG. The summation support ensures nonnegative exponents. The Gaussian coefficient is the rational product product(h=0..k−1)((q^(n−h)−1)/(q^(k−h)−1)) for k<=n and zero otherwise.

`DualPolar.SourceFormulaConjecture` encodes prime-power parameters, all five doubled e codes, genuine square-field restrictions for half-integral e, the exceptional tuples, valley unimodality, and the minimum-location clause. `source_formula_refuted` proves its negation with no assumed numerical/spectral theorem. All definitions and five endpoints are audited. The formula encoding restricts j to1..d, a necessary part of any broader formulation and sufficient for this refutation.

**Precise formal residual:** the file does not define maximal isotropic subspaces over finite fields or their adjacency algebras, or prove that their eigenmatrix is the source Gaussian expression. The primary paper supplies that identification, citing Vanhove2011 Theorem4.3.6 and Stanton1980 Theorem5.4. Those predecessor proof bodies were not read here. Therefore this is a complete kernel certificate for the explicit formula assertion, but NOT a claimed complete Lean endpoint for the original polar-space problem with all semantic bridges.

**Literature/significance residual:** the current arXiv v2 retains Conjecture6.2. The publisher accepted-manuscript route returned403; no retry or alternative blocked route was used. Search misses do not rule out a published correction. The identified Cioabă–Gupta2102.10155v1 successor's introduction and its precise Grassmann conjecture passage were read; this is not proof-body clearance of polar-space literature. The current OpenAI/math path screen has no matching polar/eigenvalue result located, but is not a body screen. An omitted exceptional tuple may fail the user's substantive-new-result requirement even if the arithmetic refutation is correct. This issue requires root/independent adjudication; no significance or acceptance credit is asserted.

The parameter sweep checked24570 columns across d2..40, q2,3,4,5,7,8,9,16 with integral e0,1,2 and square q4,9,16 with e1/2,3/2. It found no new unimodality failures, and this one minimum-location failure. Only the five exact source-sum values are used in the Lean proof; the sweep is diagnostic and does not prove any positive range.

## 336772: upper domination in direct products

The original arXiv1708.01305v2 Section4 was inspected through the actual proofs of Proposition4.1, Lemma4.3, Theorem4.4, Proposition4.5, Theorem4.6 and Corollary4.7. A minimal dominating set D has, for each v in D, a private *closed* neighbor w such that N[w]∩D={v}; isolated members may use themselves. This is the exact predicate in the diagnostic.

The first shortcut partitions the graph into b1-cliques and packs private neighbors, obtaining b1*l+2*s<=n for lonely/social counts. With b1=3 this does not give3(l+s)<=n. Treating each social vertex as occupying a full3-clique would be unjustified.

A stronger source argument obtains a triangle either among the social vertices or among their private neighbors. For K3^4, fix that triangle as0000,1111,2222. A vertex outside its closed domination must contain all three symbols in its four coordinates. There are36 such vertices (choose the repeated symbol, its two positions, and order the other two). Hence the source triangle argument only gives |D|<=3+36=39, short of27. It cannot close this residual case.

The closest inspected successor is Alon–Defant arXiv1904.02595, Theorem1.2 and Section3 list of37 exceptional graphs. It proves alpha=IR, hence alpha=Gamma, for all other products. K3^4 is explicitly in that residual list; generic new applications of its isoperimetric theorem would be old corollaries. The beginning of its proof and the lonely/social bound |Soc|<=2^t were inspected, but the full successor proof was not read.

The bounded1458-variable MILP has81 inclusion bits and1377 private-neighbor bits. It imposes domination, x_v<=sum_w y_vw, y_vw<=x_v, and sum_(u in N[w]\{v}) x_u <=16(1−y_vw). It asks for |D|>=28, fixing one vertex in D by vertex transitivity. The35-second solve reached its time limit with no incumbent. No infeasibility or optimality proof was produced. Residual: either exhibit a minimal dominating set above27 or supply a stronger structural charging argument/certificate. No Lean theorem is claimed for this target.

## 336964: matched disjoint domination

The source arXiv1708.09774v1 defines DD_m as the size of either of two disjoint dominating sets D,D', connected by a perfect matching, not their total size. Conjecture34 applies to connected graphs *already having* a swap set. The source has proofs for alpha2/3, so those are not new targets. Its doubled-triangle subdivision on9 vertices has alpha6 but no swap set, so it does not refute Conjecture34.

The exact per-graph diagnostic enumerates every subset, computes closed domination and independence by bitmask recurrence, and enumerates disjoint equal-size dominating pairs in increasing size. A recursive exhaustive bipartite matching search checks the perfect matching. This proves only the diagnostic answers for the tested finite graphs, not the universal conjecture.

After the sampled search, a deterministic repair mechanism was pursued: add each missing edge to the9-vertex no-swap graph; then attach a complete graph of size1,2,3,4, joining each of its vertices to the same arbitrary nonempty subset of the9 old vertices. All511 attachment subsets per size,2044 constructions in total, were checked exactly. None has finite DD_m>alpha. This specifically tests whether a small dense gadget repairs existence without lowering the required swap size.

A prospective ordinary proof starts with a minimum matched pair and tries to delete one matched edge. Deletion is legal only if both reduced sides still dominate; private dependents on either side block this move. Choosing an independent transversal of matched edges also need not be possible in an arbitrary induced union. Neither minimality alone nor the alpha bound supplies the needed alternating exchange controlling all private dependents. No universal exchange lemma was proved; the computational failures do not replace it. No Lean endpoint or new mathematical credit.

## Source-known and wording exclusions

337025 is already refuted by its own source Section7. For even m>=4 there are m double-star components, each with m/2 leaves at each center. Central edges are all blue; each component's m leaf edges have a component-specific color. Every one of the m+1 colors has m edges, Delta=m/2+1, and any blue matching edge prevents representing that component's leaf color. Therefore every color occurs at least Delta+1 times and a full rainbow matching is impossible. This is the source's own construction, not a new discovery.

337309 is already contradicted by source Corollary1.5, giving O(n^2 lambda1) tropical circuit complexity. 337000 has a known exact solution in the inspected successor's introductory theorem statement. 336802,336941,337106,337158,337159 already report prior solutions/refutations literally; their proof bodies are not certified here. 337212 corrupts the intended Delta>=3 premise; low-degree counterexamples to the malformed text receive no credit. 336920's rank8 indefinite Heawood realization is not a PSD counterexample. Other parked targets and their exact obstacles are individually recorded in results.json.
