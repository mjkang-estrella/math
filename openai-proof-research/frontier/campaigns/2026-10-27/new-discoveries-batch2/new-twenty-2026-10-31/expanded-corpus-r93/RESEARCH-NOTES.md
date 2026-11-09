# r93 research notes

This is an investigator packet, not an acceptance decision. All computations are diagnostics, and no formal endpoint has been obtained. The metadata selection's first-stated-year field does not reliably identify the original posing date: several statements are explicitly older conjectures in the actual sources.

## Source fidelity and exclusions

373707 has an inherited exclusion in the earlier matrix discovery lane, reproduced in history-matches.txt. The previous report calls the claimed extension a routine application of the source's proof. That historical exclusion is retained without a new mathematical claim or a repeated search. Some historical reviews also qualify the old source-proof assertion; this lane does not adjudicate it.

373809: arXiv:2603.23164, Conjecture 1.1, is followed immediately by Remark 1.2 explicitly refuting the printed rank-1 range. Corollary 1.4 proves the intended rank-at-least-2 statement. The complete corollary proof was read: in odd rank r=2s-1, the estimates for A and its complementary sequence V give 2|A| <= 2T+(k-2s+2)n, and |A|=T+n forces k>=r+1. In even rank r=2s, they give 2|A| <= 2T+(k-2s)n, and |A|=T+n/p forces k-2s>=1 by integrality. No wording correction or rank-1 refutation qualifies.

374128: the current primary paper, Colour-balanced subgraphs, expressly resolves the conjecture in Theorem 1.2. Section 3.1 proves the vector matching theorem from an almost representative balanced bipartition (Lemma 3.1) and the complete-bipartite matching result (Theorem 1.9); assigning standard basis vectors to edge colours proves Theorem 1.2. Section 2 derives Theorem 1.9 by fractional matching cycle elimination and signed necklace splitting. This is an existing full-scope resolution, not a new route.

373963: the immutable current OpenAI/math manuscript has a theorem for every nonempty finite oriented graph, with exactly the required distance-two convention. The final proof combines counterexample reduction with the incompatibility proposition, whose proof uses the pruning lemma. Taking its vertex with |N2|>=|N1| gives the approximate inequality for every positive epsilon, since |N1|>=0. Per ancestor instructions, upstream theorems are accepted without a new upstream truth audit. This is a routine subsumption, zero credit.

373862: both the live abs page and live HTML body for the supplied arXiv:2603.25407 identify 'Groups with a conjugacy class that is the difference of two normal subgroups.' The body develops character criteria for g^G=M\N; it does not supply the quoted common-zero independence conjecture or its definitions in that form. Do not silently replace the source or assert a solution. This is a material provenance gap. No finite character-table search is claimed.

## Sustained finite routes

### 373609, domatic first-player gap

The source Introduction fixes the game: both players may assign any palette colour to any uncoloured vertex; Alice needs every colour class to dominate. The finite solver uses exact alternating minimax, colour-permutation canonicalization and irreversible failure pruning. It computes all palette sizes up to the Proposition 2.1 upper bound, rather than assuming monotonicity in palette size. All labeled graphs through n=6 are either solved or excluded as possible gap-2 witnesses by minimum degree. Complete graph K6 gives values (3,4), a useful first-player sanity check. Random extensions and a separate multiplicity-state solver for complete multipartite graphs extend the search beyond this sweep. The logs distinguish completed orders from interrupted prefixes.

A tempting simulation changes the starting player by treating an initial move as an exceptional colour. It does not immediately produce a strategy: future choices depend on the precoloured vertex, and collapsing an exceptional colour does not preserve domination of the other classes. A missing sufficient lemma would convert a winning k-colour Alice strategy in one starting convention to a winning (k-1)-colour strategy in the other, including every adversarial initial vertex/colour. The source's score-game inequalities give weaker bounds, not this conversion. No such lemma is proved here.

### 373741, reduced bumpless pipe dreams

The enumeration uses six local directed-pipe tiles, with south and west as inputs, north and east as outputs; pipes enter each south boundary location and leave each east boundary location. At a cross both labels continue straight. Repeated crossings of the same unordered pipe pair are rejected. A local adjacency groups all reduced grids agreeing outside one 2 by 2 window. Boundary compatibility makes these exactly the allowed local replacements. The independent counts 7,41,393 at sizes 3,4,5 match the source's Table 3. The enumerated graphs have one connected component through size 7, including 150371 states at size 7.

The source proves connectivity after adding rectangular droops and undroops; that theorem does not prove the reserved claim. A full proof by reducing each droop to local flips would require a reducedness-preserving simulation, potentially with detours. Simple monotone simulation is blocked by the source's stuck configurations at size 8, not an implementation error. The source already observes non-monotone escape there. Neither these known traps nor finite connectivity is a new resolution.

### 373928, closed-neighborhood ideals

The source Theorem 3.6 and proof identify v via private-neighbour domination. The computation independently enumerates squarefree monomials x_A: the colon ideal is prime precisely when its nonzero residual generators N[v]\A all contain one of the singleton residual generators. It minimizes |A|. For regularity, it uses Hochster's formula over GF(2), computes reduced homology of every induced Stanley-Reisner restriction by exact binary boundary ranks, and maximizes homology degree plus one. The coefficient field limitation is explicit: absence of a GF(2) violation does not clear every characteristic.

The source already proves v<=tau and reg>=tau for certain classes. The generic missing lemma is not supplied by the matching lower bound reg>=a(G), because v can exceed a(G), as the source's complete-graph example shows. One sufficient genuinely general statement is: for a minimum prime-colon witness A of size v, some induced restriction has nonzero reduced homology in degree at least v-1 over the specified coefficient field. No general construction of this cycle or obstruction to it was found. Random graphs and cycles, complements of cycles, wheels and named symmetric examples were tested beyond the exhaustive sweep; consult exact completed coverage in outputs and logs.

### 373577, arbor word enumerator

All rooted trees with positive vertex weights summing to n encode arbors up to relabeling. Descendant blocks are placed in depth-first order. Two independent exact methods were used at small orders: direct lattice-point enumeration and a subtree convolution for Ehrhart counts. For tQ, each subtree contributes a polynomial counting total coordinate sums, truncated at t times subtree size. Multiply child polynomials by the stars-and-bars polynomial of the root block. Recover h* with the (1-t)^(n+1) coefficient transform. Enumerate every length-n word to compute the other side. Agreement through size 6 includes all 108 weighted rooted-tree shapes at that size.

A prospective full proof could exploit the consecutive descendant intervals after depth-first relabeling and an alcoved triangulation in cumulative coordinates. The unresolved bridge is an exact bijection from the half-open simplices, with shelling degrees, to the constrained words with degree n-1-des(w). Merely observing integral interval inequalities proves neither that bijection nor the h* identity. Existing parking-function/Ehrhart frameworks would also require a prior-art comparison before claiming significance.

### 373965 and 373966, symmetric orientations

Small cyclic and dihedral connection sets are exhaustively enumerated, with the disjoint-inverse condition enforced. Tightness is |S*S\(S union {1})|=|S|. The small positive classifier recognizes empty graphs, regular tournaments, powers of directed cycles and recursively certified equal-module lexicographic decompositions. Separate nonabelian searches in Q16, the order-21 semidirect product, and the order-27 Heisenberg group screen for prime-module tight orientations that cannot be base factors. This latter screen is only a necessary obstruction search; decomposable graphs are not all positively classified by that script. No counterexample is claimed from an unrecognized state.

All strict orientations on at most five labeled vertices are tested for the distance-transitive route. Equal in/out-degree and strong connectivity prune the search; all permutations are checked as automorphisms on the surviving graphs, and their action on ordered pairs at each directed distance is tested. This covers the strongly connected interpretation, not disconnected/infinite variants or digraphs with digons. The latter would be a source-domain issue, not a qualifying counterexample.

### Other finite diagnostics and hard dispositions

373586: literal impartial game trees of birthday at most 3 generate truncated disjunctive-sum tests through six components (and one extra star for twin outcomes). Membership in a hypothetical evilly normal kernel is an OR of generator memberships. Every eligible truncated sample admits such a choice. This neither verifies closure for all sums nor treats all partizan games; it cannot qualify as an endpoint. A global extension theorem or finite quotient certificate would be necessary.

373673: exact GF(2) rank-3 generator matrices are searched up to column permutation via all multiplicity vectors including zero columns. Dynamic programming on the finite subspace lattice evaluates the with-replacement stopping expectation as rational numbers for file dimensions (1,2). No violation appears through ten columns. This is a diagnostic, despite the broader coded-retrieval route being hard; it gives no uniform field/rank theorem.

373770 concerns compact quantum subgroups, not merely the finite subgroup lattice of S_N. The primary paper identifies exotic intermediate Tannaka categories and proves low-moment/easiness restrictions. An enumeration of ordinary subgroups would not test the original statement. No such surrogate computation is offered.

373840 retains the planar multigraph circular-flow conjecture; nonplanar counterexamples to Jaeger's conjecture do not refute it. The current source's 10-edge-connected results do not cover every 4k-edge-connected range. 373912 retains the maximal-code commutative-equivalence conjecture, whereas Shor's printed code refutes the unrestricted version only. 374139 is the asymptotic zero-column-dominance conjecture, not a claim that every finite singular matrix has a zero column. 374144 reduces its strict critical-parameter comparison to dimension one, but requires a uniform argument in gamma. 374147 generalizes the principal-branch bound to every analytic branch on every bounded Lipschitz domain; the ball calculation already known in the source is not full scope. These routes remain parked, with no fake bounded endpoint.

## Access and novelty limits

All access in this lane succeeded except local missing Python bs4 and missing C++ compiler, both retained in logs/source code. No denied network route was retried. The arXiv search API, general search connector, Crossref and challenged publisher routes described in TASK were not used. Source HTML and abs pages were fetched directly once each, with dated status and byte hashes. Version histories were inspected; the fetched unversioned HTML bodies are recorded exactly rather than presumed identical to arbitrary earlier versions.

The registry screen covers complete path trees, followed by actual Seymour manuscript reading; it does not read every registry proof. No worldwide novelty clearance is asserted. Later citing works and author bibliographies have not been comprehensively searched, and a new candidate would need that investigation. The source mismatch is parked rather than repaired speculatively. No Lean packet is made because no new exact full-scope endpoint was proved. No credit is requested.

## Additional reproducibility and trust details

The pinned NetworkX atlas supplies 1044 order-7 isomorphism representatives. The McKay graph8.g6 dataset supplies 12346 order-8 representatives. Dataset bytes, source URL/status/time/hash and the NetworkX HEAD pin are retained. These datasets are trusted as enumerations for diagnostic coverage; this lane does not provide a formal certificate that the graph lists are isomorph-free and exhaustive. The private-neighbour formula and independent prime-colon computation agree on all 1252 nonempty atlas graphs through order 7. This validates the implemented finite invariant calculations against a separate formulation, not a new theorem.

The supervisor restricts affinity to the same two available CPUs and each computational child to 120 CPU seconds, with sampled RSS monitoring. It originally triggered at wall time 140 seconds; two killed calls report approximately 140.05 and 140.09 seconds because of sampling/termination overhead. Later calls use a 139-second trigger to allow a margin. The retained receipts report actual observations, not a cgroup guarantee. No process exceeded the 6 GiB sampled RSS cap. Aborted minimax runs preserve only completed orders and recorded prefixes; an interrupted order is not silently counted complete.

No Lean or mathlib compilation was performed. The listed Lean/mathlib cache is not an asserted trust dependency of a proof from this lane. There is no formal packet, no axiom audit, no strict rebuild and no claim to have supplied one. A failed local C++ compiler attempt was replaced by Python; no dependency installation was attempted.
