# Sustained ordinary mechanisms and precise gaps

No mathematical enumeration or execution was used. These are reasoning attempts, not established results unless explicitly marked complete.

## 370334: finite domination obstruction

First considered sparse high-girth/regular constructions: naive counting only gives 2n/(k+1), below the proposed 2n/k and therefore cannot refute it. Cycle blow-ups do not automatically help because domination can choose vertices on both sides. A one-sided covering obstruction alone is insufficient, exactly the issue raised by the source's v3 example. Switched to two-subset intersection transversals: the bipartite double of KG(8,2) has a dense degree large enough to make the claimed bound four, but every split 0+4, 1+3 or 2+2 leaves a common nonneighbour outside the selected vertices. The full proof, including mixed-side compensation, is in ORDINARY-PROOF-HOLD.md. All-n or classification is unnecessary for this universal claim: this single exact graph is in scope. Qualification remains HOLD.

## 371304: population preservation

Read actual asymptotic definition (1.1), the class examples with zero-density patterns, Conjecture 5.1, and selected proofs in Sections 3 and 4, including the fixed-point estimate and the saddle-point bound. The source's successful examples use detailed structure, not a general conditioning principle.

Attempt 1: identify uniform B_n with uniform A_n conditioned on X_p=0. For a length-m pattern q, its normalized count lies in [0,1]. The difference of expectations is at most Pr_A(X_p>0); Markov only bounds this by E_A X_p=o(n), not o(1). The factor n is fatal. Even X_p=1 deterministically has zero limiting density but makes the conditioning event empty. That observation is a counterexample to the proposed proof principle, not a permutation-class counterexample.

Attempt 2: delete or locally repair the o(n) bad windows. If a map to B_n changed o(n) local comparisons and had asymptotically uniform image, q-density would be preserved. But repairing one occurrence can create others, can violate original forbidden patterns, and can bias image fibers exponentially. No invariant controls these effects. A proof requires a repair map with quantitative distortion or a conditional concentration estimate uniform in every fixed avoidance basis. Neither is supplied.

Attempt 3: encode allowed consecutive order types by a directed overlap graph and apply Perron-Frobenius theory. This works for finite-alphabet words with product weights, where zero stationary transition probability excludes that edge from a maximal component. Permutations have consistency constraints across sliding windows and nonuniform extension weights; the finite adjacency matrix is not their exact counting operator. Even multiple maximal components can be reweighted by a subexponential perturbation. Missing: an exact weighted representation plus control of conditioning and phase weights. No finite witness was produced; park the infinite/asymptotic endpoint rather than request a solver task.

## 368459 and its stronger sibling 368458: prescribed left ends

Read Definitions 4.1/4.3 (a_j=a_i+2 and perfect matching), actual Definition 5.1 (irreducible crossing), actual recursive Definition 5.18, Theorem 5.6 proof start, Theorem 5.20 induction cases, Lemma 5.23 proof, Conjectures 11.13/11.14, Example 5.19's printed recursive module paths. Figures in Example 11.15 were not visually audited; their TikZ expansion is not evidence of a counterexample.

Attempt 1: uncross an irreducible matching with the same left ends, choosing a lexicographically extremal right-end assignment. Swapping right ends preserves legality only for arcs of the same colour, since each right letter must be two larger than its own left letter. Irreducible crossings can involve different colours. Therefore generic uncrossing is invalid; a colour-compatible exchange that lowers an invariant is missing.

Attempt 2: apply the steady recursion directly to an irreducible configuration. Moving a nonadjacent letter through the distinguished segment transports ends by a permutation sigma; injectivity of mu on steady configurations does not prove an arbitrary irreducible left-end set stays in the image. At the a=2m+2 split, the contraction branch prescribes an adjacent plus/minus pair while the extension branch changes which letter is inside the segment. Need a dichotomy proving every irreducible sign word lifts through one branch without changing its original sign labels after inverse transport. No such lemma was established.

Attempt 3 for 368458: Gaussian elimination on the singular-vector basis. The source constructs linearly independent vectors whose leading terms are irreducible left ends, giving mu(IConf) subset Pvt. The known dimensions |IConf|<=h<=|SConf| do not give either desired set inclusion. Even an injection of finite sets by size need not preserve signs. Need a spanning/triangular reduction of every singular vector to steady pivot columns; this is stronger than the purely combinatorial 368459 and is unproved. No promotion of the weaker helper.

## Explicit zero-credit correction 367940

The j=2 literal contradiction and Stirling witness in results.json are complete, and the printed source table makes the inconsistency visible. It is a formula/index correction. It does not solve the intended maximal-run enumeration; no attempt to reselect a nearby conjecture.
