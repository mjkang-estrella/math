# Ordinary proof attempts and precise gaps

This is source/discovery work only. No Lean, solver, numerical search, permutation enumeration, graph enumeration, or Pi task was run. No candidate is qualified. The three most concrete finite mechanisms were pursued symbolically below; none closes its full target. These are failed approaches, not new helper results offered for credit.

## 320192 — maximal even-path packing

Literal goal: for every positive k choose c_k independent of G and d, so every d-degenerate G has an inclusion-maximal edge-disjoint collection of simple paths of exactly 2k edges, with endpoint multiplicity at most c_k d. Source 1007.4287v1–v3 final conjecture; v3 Proposition 9 proves the star analogue, hence k=1. The source says k=2 may also be within its methods. Neither case would answer the all-k question.

First approach: orient edges along a degeneracy ordering, with at most d edges charged to each vertex. If every selected path has its two endpoints on the uncharged side of an incident edge, the charge bounds endpoint multiplicity by d. But arbitrary paths in the residual graph need not admit the required endpoint orientation: a simple path can have alternating rises and falls in the degeneracy order. Restricting to paths monotone toward a central vertex therefore loses maximality among ALL 2k-paths. The star proof has a single centre and does not supply the missing general path lemma.

Second approach: choose a packing minimizing a convex potential of endpoint counts among maximal packings. A local rerouting through an overloaded endpoint can lower the potential only if one can replace a path while retaining length, simplicity, edge disjointness, and maximality. Splicing two paths at an intersection may repeat vertices or create paths of the wrong length. Re-extending the packing can recreate the original endpoint overload. No exchange lemma preventing this was established. An induction removing a low-degree vertex has the same problem: each of its at most d incident edges can force a new path whose other endpoint already saturates its allowance; repeating the deletion induction allows an unbounded accumulation at a high-degree vertex.

Required next mathematical step: an all-k bounded exchange/charging lemma with explicit O_k(d) endpoint bound and P_(2k+1)-free residual graph. This is not an executable finite certificate plan: the target is uniform over all finite graphs and all k. No claimed counterexample, and no justification for large blind enumeration.

## 368886 — arbitrary three real edge weights

Literal goal is adjacent weighted-degree separation for every nice graph and every distinct triple of real numbers. Source v3–v8 Conjecture 7 states this exact extension; the paper's uniform-span total-weighting theorem includes vertex weights and cannot be substituted. Earlier versions discuss the stronger edge-list question; target placement differs across versions.

First approach: transport a {1,2,3}-weighting by an affine map. Write w'(e)=alpha*w(e)+beta. Then s'(u)-s'(v)=alpha*(s(u)-s(v))+beta*(deg(u)-deg(v)). Thus even when alpha is nonzero, a proper old weighting can create equality at an edge of unequal endpoint degrees. Moreover an arbitrary three-point set is not an affine image of {1,2,3} unless its middle point is the midpoint. On a regular graph the translation term cancels, but that observation answers neither arbitrary graphs nor arbitrary triple spacings. It earns no credit.

Second approach: the graph polynomial product over edges uv of (sum_(e incident u) x_e - sum_(e incident v) x_e) encodes the constraints, with the shared x_uv cancelling in each factor. A nonzero monomial having every individual exponent at most 2 and the necessary total degree would give a Combinatorial Nullstellensatz route for arbitrary three-element edge lists. This is stronger than the assigned common-list question and is not proved here. Writing down the polynomial is a restatement/solver encoding, NOT a candidate. A greedy edge choice affects both endpoints and may undo previously separated neighbours; the fact that each constraint forbids at most one value does not bound how many already imposed constraints a single edge must satisfy.

Required step: a structural global choice argument for arbitrary triples, or an explicit graph and exact real triple with a complete impossibility proof. No graph/triple obstruction was obtained, and none is routed for Pi execution. No attempt to count an endpoint convention such as permitting loops or an isolated edge.

## 369524 — excedance/antiexcedance commutativity

Source Definitions 3.10.18–20 and Conjecture 3.10.22, pp105–106, read. The author already checked n<=8. Coefficient comparison in the source is already known and cannot be credited as a reduction.

First approach: invert every permutation. exc(w^-1)=anxc(w) and anxc(w^-1)=exc(w), so inversion sends X_(a,b) to X_(b,a) and reverses multiplication. It does not fix each factor. Conjugation by the reversing permutation w0 also interchanges the statistics. Combining the two gives an anti-automorphism tau(w)=w0*w^-1*w0 which fixes each X_(a,b). For A and B in this family, tau(AB)=BA; this proves commutativity only if AB is itself tau-fixed. That closure/invariance is exactly the unpaid step. It cannot be assumed from tau(A)=A and tau(B)=B.

Second approach: centrality is false for individual general X_(a,b). In S4, cycles (1234) and (1243) are conjugate, yet have statistics (3,1) and (2,2), respectively. Thus the coefficient function of X_(3,1) is not constant on conjugacy classes. X_(1,1) IS the sum of all transpositions and central, which explains a small family but does not generalize. Invariance under cyclic relabeling, even if used, would give a centralizer of a cyclic subgroup, not a proven commutative algebra. No simultaneous diagonalization or multiplicity-free representation theorem covering these elements was established.

Required step: an explicit coefficient-preserving bijection between the two factorization sets in the source, or a proved commutative ambient subalgebra containing every X_(a,b), or a concrete nonzero coefficient of a commutator for some n>8. No such witness is known here. No factorial search or blanket execution assignment is justified. Ring characteristic must also be retained: an integer discrepancy needs a nonzero image in a specified coefficient ring, with characteristic zero a safe existential refutation target if the source quantifier permits it.

## Additional full-scope barriers

320955: a single finite graph cannot refute existence of h(k); would need fixed k and arbitrarily high connectivity with no suitable vertex-prescribed induced cycle. Edge deletion (source Mader theorem) is not vertex deletion. No such family or uniform proof.

322704: finite Ramsey bounds do not give an ordinal rank/homeomorphic-embedding theorem; 'reasonably simple' is not an exact formal predicate. No least-bound construction claimed. v1 Question4/v2 Conjecture4 do not yet state the explicit F formulation of v3 Conjecture3.

376778: source Theorem3.1/Proposition4.5 remove the Neumann–Dirichlet component only. Eliminating noncompactly supported pure-point eigenfunctions requires an extra spectral bridge; treating the two components as identical begs the question. No spectral proof.

388094: unrestricted infinite indegree makes the distance-two coverage condition an infinite disjunction, so the naive finitary compactness proof fails. Source Corollary2.1 covers finite indegrees, and the source's two independent sets covering vertices via paths in G need not provide paths INSIDE the two induced partition pieces. The source itself states this limitation at the end. No infinite-graph construction.

388681: orientation-state expansion with 24 die states gives a standard NP verifier for a Hamiltonian traversal; no polynomial algorithm or hardness gadget for a FULL rectangle. The free-cell and blocked-cell reductions read in Rolling.pdf do not preserve the assigned board class. Printed figure gadgets not exhaustively visually compared; no gadget proposed.

388673: stripe constructions for a restricted triangle family do not prove existence for every prescribed congruence class; finite local checks do not certify all rigid motions of the plane. No universal construction or finite non-3-colourable congruent-triangle hypergraph.

377342: a fractional vertex of the counting polytope shows a possible quasiperiod, not that the actual Ehrhart period exceeds one (period collapse must be ruled out). The known H_3^3 case does not lift automatically to every n,d>=3 by taking a face. Need an uncancelled root-of-unity pole or another uniform exact argument, not finite fitting.

351630: source Theorem3.5 handles a single bag; it does not imply domination of arbitrary unions, since taking unions adds edges and changes the exponent-normalized homomorphism-density inequality. Need a conditional gluing inequality for overlapping selected bags. No full proof or graphon witness.

334042: standard 3-winding has cyclic domain, hence is no tree counterexample. Source Conjecture3.2 reports an announced positive proof [FK] whose completeness is disputed by some posers. That proof body and later resolution status were not cleared here; no new candidate can bypass it.

365142: source permits multiple brushes per arc, and parallel firing is explicitly outside its main sequential model. A generic optimization encoding over schedules is not a solution; simultaneous minimization of brush count and time also needs a precise joint-objective convention. No efficient uniform rule or proved incompatibility example.

345448: choose a point for each codeword atom, and replace each convex set by the convex hull of its selected points. This preserves selected witnesses but may uncover new atoms: a containment U1 subset U2 union U3 need not be preserved after the two covering sets are shrunk separately. The source concerns OPEN convex sets/interiors of polytopes; treating closed hulls as the endpoint is a convention correction, not a refutation. Dimension-two results do not solve all dimensions.

388029: arXiv1806.03426 Theorems8/10 already give NP-completeness for the first problem, including k=ell=2. Its 'Problem2' is a degree-constraint problem, NOT the MathDB second two-terminal problem. Do not conflate the numbering. Full two-terminal complexity remains unpaid here.

388116: the 2024 journal body proves hardness of SSCOH (mutual reachability on a specified terminal set, the k=1 case) and WBOH. These already exclude rediscovering a polynomial general orientation characterization, conditional on P!=NP. NP-completeness is not a literal structural characterization for every k/symmetric requirement, so a full affirmative/negative classification answer is not claimed.
