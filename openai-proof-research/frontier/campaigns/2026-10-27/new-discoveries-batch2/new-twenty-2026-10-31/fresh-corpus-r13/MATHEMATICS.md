# Additional mathematical work and failed routes

## 333722: degree-associated reconstruction

I read the original Theorem 4.2 two-case proof before searching for blockers. The first case modifies a different component H to H+f, while leaving H-e in place. Its degree sum forces s=r-2. A second compatible deleted edge would leave a vertex of degree s+1 absent from H, so this case is impossible even for s=2. The second case modifies the damaged component H-e by adding a different edge. Degree sums force either r=s+2 (both new endpoints formerly have degree s) or r=s+1 (one formerly has degree s-1). The printed proof assumes s>=3.

For s=2,r=4, the new edge joins two degree-2 vertices. Each originally has two degree-4 neighbors. A second deletion compatible with the original card degrees must involve the unique original damaged degree-4 vertex and one of the raised degree-3 vertices. An unaffected degree-4 neighbor should still detect the forbidden adjacency. This is a plausible elementary extension, not a completed independently checked proof for every blocker configuration.

For s=2,r=3, the obstruction is subtler: the original semiregular graph is an incidence subdivision of a cubic multigraph. A possible second deletion can remove the only high-high adjacency by lowering its other endpoint's degree. Tracking the induced subgraph on degree-2 vertices then points to a parallel-edge configuration. A full edge-transitivity argument would have to reduce that configuration to K2,3; it was not completed as a formal theorem. Moreover, Anu–Monikandan 2025 recalls an earlier Theorem 7 that already bounds dern by 2 for bidegreed graphs with mutually nonadjacent higher-degree vertices, except the named K2,3/P3 cases. This covers the prospective (2,3) endpoint. Its cited earlier proof body was not read, so record subsumption as a material hold rather than certified clearance.

The diagnostic enumerates all connected graph-atlas components up to seven vertices whose edge-cards are isomorphic, and several subdivided edge-transitive examples. For G=2H, it generates every candidate supergraph of a chosen da-card by adding a nonedge of the correct degree sum, then counts compatible deletion multiplicities up to isomorphism. Only H=K1,2,K1,3,K2,3 have blockers of multiplicity at least two in the tested list. These are floating-free combinatorial diagnostics implemented with NetworkX isomorphism, not Lean certificates or a proof over all graphs. No global graph census is claimed. The initial run failed because NetworkX was absent; it was installed only inside this lane and rerun successfully.

## 333535: immediate source bridge, excluded

Theorem 5's actual proof gives a Choi matrix with diagonal entries a,1-a,f,1-f and off-diagonal parameters d,e. Set d=e=0. The matrix is positive and has the channel constraints, and its displayed contraction is max(|d+e|,|d-e|,|a-f|)=|a-f|. Any channel over the fixed classical channel has contraction at least |a-f| by the pair of diagonal basis input states. Therefore the infimum is attained. This is already an immediate same-object specialization of the preceding source construction and the definition of contraction. It is excluded under the campaign standard; there is no Lean-polishing investment.

## 333161: known exact regular counterexample bridge

The full proof in Ramsey-nice families, Section 5, takes d=4, m=6, A={1,2,3,4}, B={5,6}. For each i in A,j in B it adds (i,i,j),(i,j,i),(j,i,i), with coordinates in three distinct parts. Every vertex has degree 4. Assign an edge to its repeated index i in A; any two edges assigned to the same i intersect, so every matching has size at most 4. The demanded lower bound is (4-1)6/4=9/2. Thus the first asymmetric clause is false, already by this public 2018 construction. This is not a new solution, even if a smaller finite Lean witness were constructed. The stronger perfect-matching clause has not been refuted by this example.

## 333715: known counterexample family, excluded

The later primary proof replaces leaves of odd-depth binary trees by K4 with a subdivided edge. Its induction simultaneously bounds the number of initially black vertices inside a gadget and shows its root cannot be internally forced in the equality case. That second invariant makes the lower bound recursive rather than a mere sum of gadget bounds. The printed recurrence t1=2,t(n+1)=4t(n)+2 yields Z(G_n)=t_n+1, while |G_n|=6*4^(n-1)-1. Already n=2 gives 11 versus the conjectured 23/3+2. The full Lemma 1 and Proposition 3 proofs were read. No new credit.

## 333569: retained lead

The complete ordinary argument, direct finite-entropy bridge, differentiation justification, and exact formal gaps are in PROOF-333569.md. The accompanying diagnostics verify the finite identity through length seven and sample local perturbations; none of those finite computations is used as the proof. Target333569.lean contains only definitions of the literal finite-cylinder functional and an existence predicate, with no theorem asserting it. The strict compiler pass does not establish the endpoint.
