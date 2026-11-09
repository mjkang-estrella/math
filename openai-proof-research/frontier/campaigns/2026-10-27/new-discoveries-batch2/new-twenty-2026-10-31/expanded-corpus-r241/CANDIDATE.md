# No qualifying candidate

Zero new exact solutions and zero Lean endpoints. No acceptance or campaign count change is requested. The strongest remaining routes are below, ordered by plausible finite certificate cost. No surrogate theorem was manufactured.

## 348952: matching deletability

The source means that there exists ONE orientation D such that D-e is strongly connected for EACH matching edge e separately. Deleting the entire matching simultaneously is a different and unnecessarily strong requirement.

For a fixed graph, matching and orientation, the exact cut criterion is: every proper nonempty vertex set has at least one outgoing arc; if that outgoing cut has size one, its unique arc must not belong to M. Applying this criterion to complementary sets also checks incoming cuts. `graphs.py` encodes both directions on all cuts, and checks all 3-edge cuts for matching eligibility. `lazy_matching.py` repeatedly solves an orientation model and obtains violated cuts from SCC decompositions of D and every D-e. A SAT result is checked directly by those SCC computations. An UNSAT model would still need an independently checked certificate and Lean semantic bridge; none occurred.

The second search uses a separate exact eligibility test. In a 3-edge-connected graph, two fixed edges belong to a 3-edge cut iff deleting both leaves a bridge. A greedy maximal matching is rejected when any such pair exists. This does not discard eligible matchings, but sampling one matching per graph is far from exhaustive.

All-cut runs: all matchings for the eligible atlas inputs through order 6, three greedy matchings per order-7 input, and samples at orders 8,10,12. There were 1441 SAT cases and 73 ineligible cases. Larger lazy-cut runs: cubic samples at orders 14,16,20,24,30,40,50,60; 122 SAT, 61 ineligible and 23 unknown. Unknown instances are not evidence of nonexistence. Remaining lemma: a full orientation construction for arbitrary eligible M, or a genuinely eligible graph with a proved unsatisfiable cut system. No such mechanism survived this pass.

## 348689: surveillance uniqueness

For a loop-free path strategy let x_i/8 be the right transition probability at internal vertex i, with deterministic transitions at the two leaves. Absorb the target endpoint. Start with integer mass 1 at the opposite endpoint and multiply every transition by 8 at each time step. After t steps the absorbed mass is exactly 8^t times the hitting probability. Reverse the path and complement the internal probabilities for the reverse hitting probability. `surveillance.py` compares the minimum of these two exact integers against the uniform internal strategy. This reduction is source-dependent and is not an independently formalized proof of the full surveillance model.

Every tuple x_i in {1,...,7} was tested for n=3..6, for every n-1<=t<=2n-3. Orders 7..14 used 1000 seeded tuples each. No improvement or nonuniform tie occurred. A second pass used denominator 64 and reflection-symmetric near-uniform strategies at orders 8,10,12,16,20,30,40. There were 17000 duration/strategy tests, with no strict improvement. Symmetry forces the forward/reverse endpoint probabilities to agree on that restricted subspace; this tests directions the nonsmooth minimum might otherwise hide. It does not establish uniqueness.

Remaining lemma: global strict optimality, uniformly in n and t, including self loops and boundary transition probabilities. The source already proves the minimum-duration case by the product inequality in Remark 12; repeating that case or its one-step periodic extension earns nothing. No general strict inequality was proved.

## 373826: stronger packing colouring

Use four colours with exclusion distances 1,1,2,3. For each pair at distance d, prohibit common colour c when d<=r_c. `graphs.py packing` solves this exact finite CSP. The source's (1,1,2,2) theorem is strictly weaker and cannot settle the reserved target.

All 113 connected subcubic atlas graphs through order 7 and 598 eligible seeded cubic samples through order 30 were SAT. No Petersen exception was misreported as a new witness. The prior r218 and r215 lanes were read before this search. Remaining lemma: a uniform stronger recolouring argument or a new non-Petersen obstruction, compared with the actual printed/cited constructions. No such object was found.

## Other finite diagnostics

* 349110: all 256 switching-equivalence representatives on a 3x3 triangular patch were SAT. Both the signed target on six vertices and the vertex switches were variables. Failure for one fixed signed target would not suffice. These are per-instance targets, not one common universal target.
* 348734: exact linear-real SMT for all 155 nonisolated atlas graphs of orders 2..6, with nearest-neighbour radii and strict sup-norm ball intersections, was SAT at ceil(2n/3) coordinates.
* 341665: all decompositions of |G|-1 into parts 3,4,5 were tested for G=Z2×Z2×Z3, Z2×Z2×Z5, Z2^3×Z3, Z4×Z2×Z3, Z2×Z2×Z7. All 30 cases were SAT. Every integer >=3 can be written using 3,4,5, so these finite checks cover arbitrary allowable part sizes for these five groups by merging zero-sum blocks. This elementary finite reduction is not a new uniform theorem. The published Hall–Paige theorem only certifies sufficiently large groups; its introductory phrase “confirms” does not remove that qualification.
* 350309: direct chord-pairing enumeration through eight chords tests connected chordal intersection graphs. The literal printed Catalan index already fails at order 2. That is zero credit; only a substantive resolution of the intended corrected enumeration could be considered. The published body remains inaccessible after403.

No numerical script is a Lean theorem. No Lean compiler or checker was run because no new full ordinary endpoint survived. Body, version and prior-art clearance remains bounded, particularly for unsearched/unread citing works and the protected chord-diagram neighbourhood.
