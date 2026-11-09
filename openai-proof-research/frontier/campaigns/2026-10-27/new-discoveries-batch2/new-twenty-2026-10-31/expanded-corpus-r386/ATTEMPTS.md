# Sustained routes and parked routes

See CANDIDATE.md for full derivations, precise source qualifications and dormant plans for 344084 and 343790. Those are the two strongest full-scope mechanisms sustained here. A third serious attempt was 373856.

## 373856 packing coloring

Exact source: arXiv:2603.25113v1, definitions lines 50–69 and 107–123; Theorem 6 lines 689–725; Conjecture 6 lines 1284–1294. Finite simple undirected subcubic graph; heavy means a degree-three vertex all of whose neighbors have degree three; (3,0) means the heavy vertices form an independent set. The formula g3=max{g(v):degree(v)=3}=3 requires EVERY degree-three vertex to lie on a triangle. The adjacent prose calls this a smallest length, but this investigation uses the displayed max; no weakening to one triangle. Source proves (1,1,2,4), not the target (1,1,2).

Exact equivalent mechanism: find X with pairwise distances at least three such that G-X is bipartite. The other two color classes are a bipartition. Conversely every desired coloring gives precisely such X. Hence X must meet every odd cycle, and at most one vertex from each triangle can lie in X (triangle distances are 1).

Shortcut failure: selecting an arbitrary vertex from each triangle kills those triangles, but can put selected vertices at distance two across an external edge/path, and need not meet longer odd cycles. Heavy independence is not independence of all triangle vertices. Paying the local triangle condition alone is insufficient.

Structural continuation: two distinct triangles sharing an edge form a diamond unless K4 occurs. K4 violates heavy independence, so a diamond is the only shared-edge possibility. Its two shared-edge vertices already have degree three. If both tips also have degree three, the two shared-edge vertices are adjacent heavy vertices, forbidden. Therefore at least one tip has degree two. Choosing one shared-edge vertex hits both triangles, but this does not settle its distance-two conflicts with choices in neighboring triangle blocks. Distinct disjoint triangles can be joined by edges or paths through degree-two vertices. Contracting triangle blocks leaves parity constraints: after removing one selected vertex per block, the surviving paths through the block have specific endpoint connections; cycles involving several blocks can still be odd. Thus a transversal of local triangles is not automatically an odd-cycle transversal.

Second continuation: the source's Theorem 6 uses a maximum weighted packing pair (X,Y), with X a 2-packing, Y a 4-packing, and G-(X union Y) bipartite. Each selected vertex is on a triangle, at most one is selected per triangle. Its local exchanges force the residual graph to be bipartite, but do not prove Y empty. Simply recoloring Y as X can create an X-Y pair at distance <=2. Recoloring a Y-vertex into a bipartition class can recreate an odd cycle. A full route now requires a simultaneous exchange lemma eliminating all Y while preserving both distance constraints and every odd-cycle hit, or an explicit source-admissible obstruction to any such X. Neither has been proved. No finite sweep, witness, or claimed counterexample. Park with this exact gap.

## Other routing

368163 is the same all-bridgeless 7/5 target as held IDs 331437 and 338648 in exact authorized completed history, not a new family. Existing sharp cubic constructions or cycle double-cover promises do not bound the total length for every bridgeless graph. Preserve their hold.

338344 includes lambda=1,m odd, exactly a transversal of an arbitrary odd-order Latin square (source Conjecture 9 and its stated Ryser specialization). Small m results, blow-ups and averaging the lambda occurrences do not construct the required row/column/symbol transversal. Park.

342774: primitive graph, existence of quadratic n-invariant and dimension bound ALL together. Source Conjecture 55 is actual target; metadata's refuted phrase concerns another conjecture. Odd-prime-power point counting or the preceding model does not pay the even-prime/minimal-model dimension bridge. Park, not excluded.

343281: optimal max-min 3M-DAP value with both denominator and strict st inequalities. An average allocation cannot prove strict improvement or matrix feasibility. The metadata Cui/Theorem20 quote is not a checked proof of this target; exact source target passage needs fuller definition/feasibility read. Park with source gate HOLD; source-family 343283 proved recurrence is not this inequality.

343651: source Conjecture1 exactly matches. Catlin's disproof of Hajos via LEXICOGRAPHIC products is not a refutation of DIRECT-product immersion. The paper's Theorem20 needs a complete subgraph in one factor; uniform-parity immersed paths do not cover mixed parity. Need globally edge-disjoint product routing for arbitrary immersed paths. Park.

343714: actual source prints Conjecture4, but preceding projective examples have generically n+2 transitivity. An at-least-four interpretation is suspect when higher transitivity is allowed. No correction-only PGL4 example is promoted; rank/classification and precise maximum-versus-at-least semantics remain unpaid. No finite-group substitute.

343847: trivial word has zero exponent sums but source's surrounding surjectivity problem implicitly uses nontrivial words. Treat that as an endpoint/wording defect only. For nontrivial zero-degree words, source Lemma5.20 handles semisimple classes; production of nonidentity unipotent remains the exact unpaid condition. Characteristic-zero and quotient by +/-1 must be retained. Park.

344087: infinite H includes infinite finite-exponent groups; an infinite-order-element reduction covers only a subclass. Need uniform interpretation yielding undecidable MS0 on rank3 H-gain-graphic matroids for every infinite H. Park undecidability route.

344089: source known three-connected efficient classes do not automatically extend algorithms uniformly through all separations. Must prove BOTH bicircular and each finite-H gain-graphic classes efficiently pigeonhole with one fixed polynomial exponent and computable refinement bounds under the source representation. Park; no full glue algorithm.

344295: already source-resolved by Singh Theorem1.2. A caterpillar is a tree hence a forest; setting every vertex capacity lambda_v=k identifies bounded-degree faces exactly with k-matchings. Theorem1.2 therefore gives the whole literal conclusion, not a parameter-only result. Its actual proof uses Lemma3.1 forest leaf deletion/link cone, Proposition2.1 grapes and Lemma3.2 excluding two nontrivial components via a 4-cycle. Read lines214–278. Isolated graph vertices do not change the edge complex. This is an exact public prior theorem, no new credit; not excluded because topology tools are standard.

344664: source Corollary8 STATES the exact all-2-connected triangle-free subcubic alpha>=3n/8-1/4 conclusion. Hypotheses and n are identical; this direct identity is a full bridge. Metadata Heckman–Thomas quote is only the planar theorem6 and is not the justification. Existing same-source ID344665 is the six-exception classification; do not recount.

338362: source Theorem11 states Conjecture3 true with exactly 4-uniform linear scope and n/4+m/6. Actual induction read: if maximum degree<=6, 4m<=6n and Theorem7 gives 60tau<=12n+12m<=15n+10m. Otherwise delete degree>=7 vertex and extend transversal by that vertex; 1+(n-1)/4+(m-7)/6<n/4+m/6. Isolated vertices harmless; disconnected graphs handled componentwise, edgeless case tau=0. Full statement identical to literal target, publicly proved 2018; no new credit. Complement-Fano obstruction in source is NONLINEAR and not a target refutation.

341980: all simplicial arrangements, strict h2>sum higher entries. Source Conjecture2; checking known irreducible tables or splitting-polynomial assumptions cannot cover every arrangement. Need a universal incidence inequality or an actual admissible arrangement violating it. Park.

338685: full combinatorial invariance of freeness defect across all complex line arrangements with isomorphic incidence data. Terao-level special cases do not settle nonfree splitting types. Need compare actual syzygy/minimal-degree invariants for all pairs or an explicit same-lattice pair with unequal defect; no polynomial computation run. Park.

339114: connectivity for every triangulation under the specifically defined nearly-admissible-permutation flips. Cyclic-polytope triangulations and one dimension do not give the general amplituhedron graph or all flips; need a decreasing invariant or full connected induction. Park.

339198: NP-hardness in rational dimension THREE requires a polynomial-size reduction with correct bit complexity and exact translation objective. A six-dimensional reduction or projection may lose feasible lattice-count information. No such reduction produced. Park.

339425: all odd n>5 with p,q=2 mod3, primes r. For n=0 mod3, necessarily r=2 mod3; for n=1 mod3, r=3; for n=2 mod3, r=1 mod3 (including handling prime2 parity). In particular n=1 mod3 forces binary prime sums n-3 with both primes 2 mod3. General ternary Goldbach does not imply this binary progression problem; asymptotics/finite checks cannot settle all n. Park analytic target.
