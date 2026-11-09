# MathDB 370334: complete ordinary refutation, source/subsumption HOLD

Credit 0. No acceptance or Pi authorization. This is a complete mathematical endpoint with incomplete qualification, not CANDIDATE.md.

## Exact binding and source chronology

The literal statement is preserved with original raw newline, chunk path/line and SHA bindings in provenance/records.json and provenance/370334.jsonl. Hosking arXiv:2509.10473v3, Section 4, Conjecture 1 states gamma(G) <= 2 ceil(n/k) for every k-regular bipartite graph with n vertices on each side. The normalized density clause is exactly equivalent since |V|=2n. v1 and v2 discuss a different high-degree regime; v4 and latest v5 omit this conjecture. All five bodies were retrieved; comparisons were targeted to definitions, degree assumptions and the bound, not full audits of unrelated Vizing arguments. v3 says no known counterexamples. No explanation of the removal, explicit correction, or current journal counterpart was found in the bounded check. Its omission does not itself prove a public refutation or novelty.

## Construction

Let U={1,...,8}, and let P be its 2-element subsets. The vertex set is {A,B} x P, with (A,S) adjacent to (B,T) exactly when S and T are disjoint; there are no edges within either side. This is a finite undirected simple bipartite graph. Each side has binomial(8,2)=28 vertices. Each vertex has exactly binomial(6,2)=15 neighbours. Thus k=15, n=28, and 2 ceil(28/15)=4.

The graph is connected even if connectedness is imposed: any two same-side pairs S,T admit a common opposite-side neighbour, since U minus (S union T) has at least four elements. Any opposite-side pair can be linked by an edge or a three-edge path, by applying the same complement argument twice. Every vertex has a neighbour.

## Complete domination lower bound

Suppose D dominates and |D|<=4. Write X,Y for its chosen pairs on sides A,B. Exchange the two sides if necessary so |Y|<=|X|. Then |Y|<=2.

If Y is empty, all 28 A-vertices have no neighbour in D, so all would have to lie in X, contradicting |X|<=4.

If Y consists of one pair {a,b}, consider the seven different pairs {a,c}, c in U minus {a}. Each intersects {a,b}, so none of the corresponding A-vertices has a neighbour in D. All seven must belong to X, contradicting |X|<=3.

If Y consists of two distinct pairs T1,T2, then |X|<=2. If T1 and T2 share an element a, the same seven pairs containing a intersect both; they cannot all belong to X. If T1 and T2 are disjoint, the four pairs {a,b} with a in T1 and b in T2 are distinct and intersect both; they likewise cannot all belong to X. In each case an A-vertex outside X has no neighbour in Y. Contradiction.

Therefore every dominating set has size >=5. The domination number exists since the full vertex set dominates. Consequently gamma(G)>4=2 ceil(28/15); both literal inequalities fail. No graph enumeration, solver, numerical search or Lean was used. Exact gamma(G) and minimality are not claimed.

## Subsumption and significance gate

The graph is the bipartite double of KG(8,2), equivalently the usual bipartite Kneser graph whose right vertices are 6-subsets, under complementation of right labels. This identification is explicit: S disjoint T iff S is contained in U minus T. Existing domination literature for this family may already imply the lower bound. Searches retrieved a 2022 Kumar-Kumar paper on regularity and vertex domination, a thesis on Kneser domination, and a 1990s q-analogue paper. Abstracts/titles do not establish that they contain ordinary domination of this exact graph. The full relevant proof bodies were not all obtained/read. No exclusion based on ease, no literature clearance, and no significance PASS is claimed. The source's removal by v4 also needs root adjudication. The current bounded registry checks are routing only; they cannot clear all public results.

## Dormant semantic Pi plan, conditional on root qualification and authorization

Do not execute now. Use spark/GLM-5.3-Flash-EXL3 through Pi, high thinking, only after root clears qualification and authorizes formalization. Define Pair8 as {s : Finset (Fin 8) // s.card=2}; vertices Bool x Pair8; graph adjacency opposite Bool and Disjoint underlying finsets. Prove symmetry and irreflexivity, the two side cardinalities 28, and neighbour equivalence with pairs of the six-element complement yielding degree 15. Define domination semantically: every vertex is selected or adjacent to a selected vertex. Prove the above three cases for arbitrary D, using constructive seven/four-element pair families and cardinality injection lemmas. Include connectedness if the source endpoint requires it, finite minimum existence and normalized density bridge, with an actual negation of the all-graphs statement. No proxy certificate is sufficient. A bounded analytic proof should suffice; exhaustive domination-set checking is unnecessary. Pin Lean/mathlib, audit every transitive dependency with #print axioms (only propext, Classical.choice, Quot.sound), independent fidelity review, then fresh extracted rebuild. No work on this plan was executed.

## Later primary follow-up

Cambridge supplied the actual Kumar-Kumar 2023 journal HTML body. Definition 2.2 confirms the inclusion-graph identification. Theorem 1.2 is induced matching number; Proposition 4.2 bounds vertex-wise domination beta from above. These different invariants do not directly prove ordinary gamma>4. Selected actual proof passages were read, without a complete-paper or citation audit. Other closest domination bodies remain unread.
