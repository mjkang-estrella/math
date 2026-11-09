# Mathematical investigations (zero proposed credit)

## 346856: complete-graph minimum action — rank 1, unresolved

Primary body read: Huang–Stoica–Xia–Zhong, 2006.06716v1, Definitions 1–4, Definition 14, Section 4.4 including Lemmas 13–14 and Theorem 8 proof, Conjecture 2. Here P is shortest-path distance, not necessarily the assigned edge length. Transition weights are P_ij^(-2)/d_i, d_i=sum_j P_ij^(-2). Curvature is the t→0 Lin–Lu–Yau derivative, not fixed-idleness Ollivier curvature. The perfect-matching setting is a SEQUENCE tending to zero on matched edges. Thus nonattainment at positive lengths does not refute the intended conjecture.

Mechanism 1: use finite transport duality. Normalize a dual function by f(i)=0, f(j)=P_ij; curvature is the minimum of 1+sum_k(p_ik-p_jk)f(k)/P_ij over metric-Lipschitz f. This finite LP expression was implemented, with Floyd closure before computing transition probabilities. It is a diagnostic implementation; no formal soundness certificate is claimed. 60 seeded random assignments at each n=4,6,8 gave no S<n. Values and full minimizing assignments are retained in action_diagnostic.log. The first run failed only while serializing numpy.bool_; its complete error is action_diagnostic.failed.log. Corrected run finished.

Mechanism 2: solve the symmetric matched-pair metric algebraically. Let matched distances be epsilon in (0,1], other distances 1, q=epsilon^(-2), D=q+n-2. For a matched edge, coefficients cancel outside its pair and kappa=1+q/D. For a cross-pair edge, remaining coefficients are ±(q-1)/D at the two partners, plus the fixed endpoint contribution 1/D. Lipschitzness of those partners gives their difference >=-1, attained by assigning all of i's pair value 0 and all of j's pair value 1 (other pairs can have value 0). Thus kappa=n/D. Hence

S = n/2*(1+q/D) + n(n-2)/2*n/D
  = n + n(n-2)(n-1)/(2D) > n for n>2.

This verifies approach to n from above in this symmetric family. It is an ordinary finite-LP argument conditional on the standard transport derivative identity, not a complete source theorem. The family computation is already suggested explicitly by the source and receives no separate credit.

Hard gap: prove sum_{i<j} kappa_ij >= n for EVERY positive complete-graph metric (and the appropriate limiting statement), or find an exact rational metric violating it. Pairwise LP lower bounds need not sum sharply; no aggregate inequality found. Required Lean bridges: finite transport LP duality, stability/derivative at t=0, metric closure and limiting matching semantics. No source-level endpoint exists.

## 346766: Minimizer-start enclaveless game — rank 2, unresolved

Primary definitions and actual proofs read: 2006.02829v1, Section 1, Observations 1–3, Proposition 3 proof, Theorem 3 and Proposition 4 proofs. A selected set S is legal iff every v in S has a neighbor outside S. Min starts; terminal payoff is |S|. diagnostics.py implements exactly this finite minimax recurrence, with legality checked for ALL selected vertices, not only the new vertex. Both random min-degree-two graphs and every complete bipartite K_{a,n-a}, 2<=a<=n-2, were tested for n=4..14. No counterexample; this is a bounded diagnostic, not formal semantics or an exhaustive graph search.

Mechanism 1 (failed): bound every maximal legal S by n/2. This is false even at minimum degree two: in K_{2,m}, m>2, the two vertices in the small part form a maximal legal set of size 2<n/2 for m>2. Each selected center has an unselected leaf neighbor, but adding any leaf would enclose that leaf. Thus a strategy argument is essential; static domination bounds alone cannot solve the conjecture.

Mechanism 2 (structured strategy): K_{2,m}, m>=2, has Min-start value m. If Min first plays a center, Max plays a leaf, preventing the other center from ever being played (that leaf would become enclosed). Thereafter exactly m-1 leaves and that center are selected, payoff m. If Min first plays a leaf, Max plays a center, with the same terminal count. Every terminal set in this graph has size either 2 (both centers) or m (all leaves, or one center and m-1 leaves), so m is also a universal upper bound. No new credit: a special family does not resolve the source claim.

Mechanism 3: inspect the primary private-neighbor proof. For regular graphs it pairs D1 with external private neighbors and bounds k|D2|<=k|C2|. For arbitrary minimum-degree-two graphs the upper bound on the number of D2 neighbors of C2 is unavailable; K_{2,m} exhibits why. A potential invariant based on available private neighbors would have to exploit Max's previous responses and cannot be inferred from minimum degree alone. No invariant proving the half bound was established.

Hard gap: a legal Max response maintaining an injective charge of every eventual unplayed vertex to selected vertices, or an exact min-degree-two graph with a winning Min strategy below half. Full Lean would additionally need game-tree semantics and a sound recurrence/strategy certificate. No dummy predicate or bounded theorem is supplied.

## 347229: Kruskal–Katona displayed inequality — excluded formulation-level inconsistency

Read primary squashed order, shadow definitions, Definition 2.1, KKT formula, concluding Conjecture 5.1, and the corresponding later institutional manuscript concluding Conjecture 6.2. The latter corrects a surrounding strict inequality in prose, but RETAINS the displayed conjecture. It is a line-numbered manuscript, not independently authenticated publisher version.

Let N=binom(n,n/2). Substituting a=N in the displayed inequality cancels kappa(N), demanding kappa(k)<=kappa*(k). But kappa*(k)=min_{0<=j<=k} kappa(j). At n=4,k=1 the first colex 2-set is {1,2}, whose lower shadow is {{1},{2}}. Thus kappa(1)=2-1=1, whereas kappa*(1)=min(0,1)=0. Also kappa(6)=4-6=-2. The conjecture reads -1<=-2. This witness is entirely within the defined domain; no extrapolation beyond N is used.

Independently derived binomial-shadow calculations up to n=14 reproduce this defect. The first diagnostic output is NOT novelty evidence and no exhaustive classification is claimed. It is an immediate contradiction between the displayed conjecture and its own definitions, plausibly a placement-of-star/wording problem. The campaign excludes wording/endpoint corrections and routine definition-level consequences. Accordingly this is NOT nominated, not formalized, and not counted. No corrected source conjecture is invented or investigated under this ID.

## 347356: primary full-scope prior resolution

Kim's primary source defines DIRECTED cycles and in-neighbors, unlike the incomplete MathDB prose. Van Bommel, 2011.01078v1, explicitly repeats Kim's conjecture as Conjecture 1.17 and proves Theorem 2.4. Read the entire six-page body, including Lemmas 2.1–2.3 and Theorem 2.4 proof. Its even m / odd n branch is m(n+1)/2; setting m=4 gives 2n+2 for every intended odd n>=3. The proof removes adjacent zeros without increasing weight, uses the independent-set maximum, then assigns 0 to an independent set and 1 elsewhere. The journal publication is DAM299(2021)82–86, DOI10.1016/j.dam.2021.04.023 (publisher abstract seen; publisher proof body not independently read). This is an exact earlier resolution, not a new result or an undirected counterexample opportunity.

## Other primary contexts

346855: Section 4.3 imposes the strong boundary condition (Definition 16, constant lengths up to two edge steps beyond the boundary); Conjecture 1 follows there. Infinite lattice sums and boundary contributions cannot be replaced with arbitrary finite grids or tori. No full-scope total-action argument or diagnostic attempted; parked.

347273: read numerical setup and Conjecture 5.1. Source is finite differences for a normalized quartic/Bose–Einstein energy, with alpha scaled as beta*n^d and positive harmonic potential in experiments. Non-nested finite-difference meshes do not provide variational monotonicity automatically. No arbitrary-matrix counterexample is source-faithful. Eventual eigenvalue and optimum monotonicity remain unproved; beta=.5 numerical evidence is not a proof.

347595: read Theorem 1, Theorem 9 proof and beginning of Theorem 10 proof of 2008.06577. The exact odd and 2 mod4 upper theorems are already stated and proved by that source; the supplied record itself reports settlement. Not a candidate; dependencies and divisible-by-four lower bound not independently re-proved.

347675: read Definition 6, Theorem 7, Corollary 8, and selected proof body (maximal octi reduction and Lemmas 3.2/3.3 context), not the entire ear-addition proof. Cycle orientations are cacti, hence the exact claim is an explicitly stated same-source corollary. Not new.

347401: read original source Conjecture 1.1 and its explicit attribution of resolution to Chvatal–Rodl–Szemeredi–Trotter. Original 1983 proof unread. Treat as prior-resolution lead, not an independently verified proof body.

347596,347676,347665,347666: read primary definitions and exact conjecture context, no complete proof attempt. General cycle-density maximization, linear Mader-perfect size, and colored Hamiltonicity/pancyclicity remain hard; no favorable finite certificate selected. 347385 and347665 have the same literal claim; only347665's primary context was read, and neither gains duplicate credit.
