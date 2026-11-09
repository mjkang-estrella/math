# Mathematical routes and remaining gaps

## 352038 — full refutation candidate

First considered deriving the rank bound from source A.3's integer norm bound. This controls each coefficient through a nonzero integer norm, but it does not supply distinct ordered norm values corresponding to distinct coefficients. Thus the attempted pigeonhole proof has a genuine missing implication. Exact complete-quotient diagnostics instead produced the trace55/norm-6 witness at rank7. The diagnostic stops at that first witness, so `cf-output.json` is not a census through trace300. `short-witness.py` separately completed a trace<=300 search for shorter certificate blocks; its best block had length81 and trace61. The final proof retains the first canonical witness, length85/trace55. No minimality in trace, rank or period is asserted.

Beyond finite search, the real square-root inequalities, the algebraic-integer and irrationality arguments, all85 cyclic recurrence checks, an all-natural-number induction to mathlib's actual stream, and the distinct-value ranking were fully formalized. See PROOF.md, Candidate.lean and fresh-extracted/. No missing mathematical bridge is left in the declared source endpoint. Independent validation of the endpoint's chosen source encoding and significance/novelty remains required.

## 352443 — largest-mode stability, held

Read primary dominating-set and largest-mode definitions and Conjecture4.1. Root a tree and use generating polynomials S,D,U for selected root, unselected root dominated by a child, and unselected root requiring the parent. Products over children give

S=x*product(S_child+D_child+U_child),
U=product(D_child),
D=product(S_child+D_child)-product(D_child).

The domination polynomial is S+D. The recurrence was independently checked against brute enumeration of every subset on one deterministic tree of each order2 through10. The first search then tested1600 deterministic random/structured trees of orders5..100, sampling up to3 leaves per tree:4782 leaf-deletion pairs, no eligible violation; the largest observed gap was1. These are neither an exhaustive tree census nor a proof.

Second mechanism: derive an exact formula for a double star with r,s>=1 pendant leaves at the two hubs:

D_(r,s)(x)=x²(1+x)^(r+s)+x^(r+1)(1+x)^s+x^(s+1)(1+x)^r+x^(r+s).

The four terms partition by hub selections. A separate script checks the1<=r,s<=80 grid (6400 unimodal pairs, maximum mode gap1), handles the r=1 deletion boundary separately, and cross-checks the formula against the tree DP on a4x4 parameter grid. This adds an independent structured-family mechanism beyond random trees. It still leaves the all-tree statement open.

The precise obstruction to an all-tree proof is that the leaf-root recurrence mixes two adjacent coefficients of different S,D,U polynomials. Unimodality of the two total domination polynomials does not immediately order the component ratios or prevent their largest modes from moving. A sufficient missing lemma would establish that the two adjacent difference sequences change sign at indices at most one apart, for the total polynomials of any rooted tree and a leaf removal. No such lemma is asserted. Polynomial tables are diagnostics, not certified Lean semantics.

## 352413 — realizability with minimum covers, held

Read source multidigraph/simple-cycle definitions and Theorem3.1 proof. The cycle-intersection graph is encoded by membership of each cycle in the cliques associated to underlying digraph vertices. For each nonempty subset W of an n-cover, the source system requires that the number of cycles with exactly this support equals the sum of products of arc multiplicities over cyclic permutations of W. A cover by maximal cliques can fail even when a nonmaximal cover of the same minimum size succeeds, exactly as source Remark2 illustrates. Thus a naive infeasibility test on maximal covers is invalid.

First mechanism: one-cover connected cases are realized by loops at one vertex. Two-cover cases (with every isolated vertex also covered) have disjoint exclusive classes of sizes a,b and overlap c. Use a loops at vertex1, b loops at vertex2, and c parallel arcs1->2 with one arc2->1 (omit cross arcs if c=0). The cycle-intersection graph is the desired union of two cliques, so this does not offer a nontrivial refutation.

Second mechanism: for a specified three-cover, let p12,p23,p31 be the exact pair-support cycle counts and t the triple-support count. When all pair products are positive, the six directed multiplicities give two oriented triangle products u,v with uv=p12*p23*p31 and u+v=t. Thus t²-4*p12*p23*p31 must be a nonnegative square, a sharper integer obstruction than the easy AM-GM inequality. But this is an obstruction to this **specified** cover only. A true counterexample requires an independently realizable graph, its exact minimum cover size, and a proof excluding *every* minimum cover, including nonmaximal ones. No such graph was found or exhaustive search claimed. The source's seven-vertex enumeration is inherited primary evidence, not reproduced here.

The remaining global mechanism would contract/rearrange an arbitrary realization while preserving all simple-cycle intersections until minimum cover size is reached; source Section3 itself identifies this as the difficult step. We have neither that theorem nor a finite witness. No easy isolated-vertex/edge-cover wording defect is credited.
