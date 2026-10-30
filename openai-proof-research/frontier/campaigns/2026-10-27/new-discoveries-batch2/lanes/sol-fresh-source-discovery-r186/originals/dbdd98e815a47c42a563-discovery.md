# Signed-diagonal group-Steiner compression for the same C57 candidate

Status: complete alternative **computer-assisted** proof, independently checked by lower-bound certificates. No ordinary all-cases geometric proof, Lean proof, acceptance, novelty claim, or additional credit. Same candidate a(11)≤57 only. The inherited exhaustive proof remains valid.

## Literal endpoint and dependencies

For every finite edge-connected P⊂Z² of cardinality 11 there exists an integer translation t with P+t⊂C, where C={|x|+|y|≤5} minus {(±2,±2)}. Orientations are fixed; holes in P are allowed. The argument below uses only connectivity and cardinality. Container cardinality/connectivity and source interpretation are inherited from the frozen discovery and independently reviewed in the supplied preliminary review. Investment and prior-adoption decisions retain credit 0 and counts 5/30 additional, 35 total. This lane is helper work, not a new outcome or a new prior-art investigation.

The independent verifier does not read the original animal certificate or its enumeration code. It constructs finite group problems directly in ordinary (x,y) coordinates, checks 31 potential tables, and checks four tiny forced-cell cases. No source-formal worker files were read or written. No new classical theorem or network source is used.

## Exact geometric reduction

Put u=x+y and v=x−y. Integer cells correspond exactly to pairs (u,v) of equal parity. Grid adjacency becomes |Δu|=|Δv|=1. Also |x|+|y|=max(|u|,|v|).

Let a=max u−min u and b=max v−min v. Each is between 1 and 10: choose occupied cells achieving its two extrema; connectivity provides a simple path with at most 10 edges, each changing that coordinate by one. A connected set with more than one cell has positive spans. Reflecting y swaps u,v, so assume a≥b. Translate by an integer vector to normalize min u=0 and min v=e∈{0,1}. Such a translation exists because e can be chosen congruent to min v−min u modulo 2. Then every occupied cell lies in

    V(a,b,e) = { (u,v): 0≤u≤a, e≤v≤e+b, u≡v mod 2 }.

The set meets all four boundary lines u=0,u=a,v=e,v=e+b.

There are 110 nominal triples 1≤b≤a≤10, e∈{0,1}. When either span is odd the parity cases are equivalent. Explicitly, for e=1 and a odd use (u',v')=(a−u,v−1); for e=1 and b odd use (u',v')=(u,b+1−v). These preserve the integer grid and are a D4 map followed by an integer translation, and normalize to e=0. If both spans are even keep both parities. Exactly 70 triples remain.

For a center c=(s,t) in u,v coordinates, containment in the radius-5 diamond is equivalent to

    a−5≤s≤5,    e+b−5≤t≤e+5,    s≡t mod 2.

Call this finite set S. No claim that an arbitrary center or only five centers suffice is made. The four deleted cells have signed-diagonal coordinates (±4,0),(0,±4). For each c∈S define

    F_c = V ∩ { c+(4,0), c−(4,0), c+(0,4), c−(0,4) }.

A set P with these exact extrema fails every placement into C iff it meets F_c for every c∈S. This equivalence enumerates every possible diamond center, so boundary failures introduce no extra cases. A placement centered at c corresponds to translation by −c in x,y coordinates.

Thus a counterexample would be a connected ≤11-vertex subset of V meeting each of four extremal-line groups and every F_c. Retaining ≤11 rather than exactly 11 strengthens the finite obstruction statement. Delete duplicate groups and any group containing another group: meeting the smaller group implies meeting the larger. This simplification preserves the hitting condition exactly. If a group is empty, no counterexample is possible. This immediately resolves 35 of the 70 triples. An empty center set S is also handled correctly: only the extremal-line groups remain, and connectivity/cardinality must exclude that domain.

D4 is used solely in this proof reduction. If Q=gP+d is normalized and Q−c⊂C, then P+g⁻¹(d−c)⊂g⁻¹C=C. The final operation on the original P is a translation.

## Four tiny forced-cell cases

Every singleton group forces its vertex into any counterexample. In four domains there are at least eight such vertices. The independent verifier tests all supersets of those forced vertices with at most 11 vertices, checking connectivity and group coverage directly:

| (a,b,e) | forced cells | supersets checked | connected supersets | satisfying all groups |
|---|---:|---:|---:|---:|
| (7,3,0) | 16 | 0 | 0 | 0 |
| (7,4,0) | 10 | 11 | 0 | 0 |
| (8,3,0) | 10 | 9 | 0 | 0 |
| (8,4,0) | 8 | 576 | 3 | 0 |

This is 596 small subset checks, not an 11-animal enumeration. In the last row it would be false to assert that every allowed superset is disconnected: three are connected and fail an additional group.

## Lower-bound potential certificates for the other 31 domains

Let G₁,…,G_k be the remaining nonempty groups and write M for a nonempty subset of their indices. A table L(M,z) assigns an integer between 1 and 12 to each M and vertex z∈V. Its meaning is a lower bound on the number of vertices in any connected set containing z and meeting all groups in M. It is enough to verify the following inequalities:

1. If z belongs to every group of M, then L(M,z)≤1.
2. If z and w are adjacent, L(M,z)≤L(M,w)+1.
3. If A,B are disjoint nonempty group masks, L(A∪B,z)≤L(A,z)+L(B,z)−1.

These are certificate inequalities, not assumptions about an optimizer's answer. They imply the meaning above as follows. Take any connected vertex set T, a root z∈T, a spanning tree, and assign each required group to one chosen vertex of T meeting it. Prune branches with no assigned group, except retain the path to the root. Induct through the rooted tree. A singleton carrying assigned groups uses (1). A root carrying no group with one relevant branch uses (2). At a root with multiple relevant branches, extend each branch to the root by (2), include any groups assigned at the root using (1), and combine disjoint assigned group masks using (3). Each added branch contributes its vertices once; the shared root is subtracted at each merge. The resulting inequality is L(M,z)≤|T|. This proof requires neither optimality of a DP recurrence nor a solver trust claim.

In every retained table the checker verifies L(all groups,z)≥12 for every z. Therefore a connected hitting set of size at most 11 cannot exist. Together with the 35 empty-group and four forced-cell cases this proves the literal universal containment endpoint for every connected 11-cell set.

The generator computes capped group-Steiner dynamic-programming values: initialize one-vertex masks, merge disjoint masks with subtraction of the shared root, and close under graph shortest paths. Generation correctness is unneeded for the proof because verify_certificate.py separately checks all three inequalities and the endpoint, reconstructing domains/groups in x,y rather than importing generator data/functions. Integers are uint8 with all sums at most 198 in the generator and at most 24 in the verifier, so no arithmetic overflow occurs. No floating point arithmetic is involved in mathematical checks.

## Reproduction, coverage and compression

Run from any directory, with this lane substituted for L:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 180 python L/verify_certificate.py

The checker needs Python, NumPy, the 31 files in certificate-files.json, and no original animal data. It imposes hard AS 536870912 bytes, CPU 160/165 seconds, and alarm 175 seconds. The successful final checker took about 1.8 seconds. Regenerate using make_domains.py then group_steiner.py with the same environment/outer timeout. All generated cases and values are deterministic; no random seed or solver is used. The final full regeneration and replay are recorded in the run logs.

Proof coverage is all fixed connected 11-cell subsets, including holes, through 70 complete span/parity domains: 35 immediate + 4 small subset checks + 31 potential tables. This is not merely a match of counts with a known animal sequence.

The 31 necessary tables contain 1,874,144 one-byte potential entries, occupying 238,227 bytes under gzip level 9. The inherited animal certificate is 10,880,385 raw bytes and 475,654 bytes under the same gzip level. Thus raw payload shrinks by 5.806× and equally compressed payload by 1.997×. Comparing original raw with new compressed would give 45.67×, but is not a like-for-like compression ratio. The number 135268/70=1932.4 compares animal cases with geometric domains only; it is not an operation-count or entry-count ratio. The new certificate actually has more scalar entries than the old certificate has animal rows. Its principal gain is a fixed geometric obstruction interface, 31 tables, and fast local lower-bound checking, rather than a dramatic equal-compression byte saving. The initial 35-table prototype was 540,631 compressed bytes, larger than the original compressed certificate; four small checks removed this regression.

There is no ordinary geometric all-cases proof and no kernel-checked theorem here. For that reason no PROOF.md is supplied. The complete argument is computer-assisted with the Python/NumPy/runtime trust boundary; it does not claim to replace the formal worker's implementation or establish formal PASS.

## Falsifiers and failed shortcuts

The five centers {(0,0),(±1,0),(0,±1)} around a radius-4 placement do not suffice. An explicit connected 11-cell falsifier is

    {(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2),(0,-2),
     (1,-2),(1,-1),(1,0),(1,1),(2,1)}.

It lies in D4 and its u-span is 7, so its minimum integer radius is exactly 4. It hits a deleted cell relative to each of the five centers. Its unique good radius-5 center is (1,−1), checked independently over all centers. Thus even exact radius four and exact size eleven do not repair the heuristic. The seven-cell subset consisting of the first seven listed cells already blocks the five shifts. Small hole-collision sets need not force more than eleven connecting cells.

Supplementary explore.py checks only the 1024 signed-diagonal-monotone ten-step paths, not every animal. All embed, with 680 having one good center and 344 having two. If a connected 11-cell set has a signed-diagonal span 10, a path between its extreme cells has at least ten edges and therefore uses all its vertices monotonically; up to D4 it is one of those paths. This partial certificate is optional and unused by the full group-Steiner proof.

An attempted C++ implementation could not compile because g++ is absent. A Node implementation failed at startup under the required 512 MiB address-space cap (SegmentedTable allocation); the cap was not relaxed. These implementations are unused. The actual generator and independent verifier are bounded Python/NumPy scripts. No solver UNSAT answer, full animal regeneration, or duplicated Lean implementation is used.

Decisive falsifiers are: a group reconstruction or parity/symmetry error; a violated base/edge/merge inequality; a missed forced-cell superset; an incorrect root-tree induction; or a connected 11-cell set with no center passing the exact formula. Any such error invalidates this alternate certificate inference, without invalidating the inherited independently verified exhaustive proof. No broader n, optimality, first-failure, novelty, or acceptance conclusion follows.
