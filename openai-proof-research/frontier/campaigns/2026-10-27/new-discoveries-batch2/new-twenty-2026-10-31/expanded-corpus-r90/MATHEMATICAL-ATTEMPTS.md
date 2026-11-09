# Mathematical attempts and limits

No result in this lane is proposed for acceptance. All computational statements below are diagnostics, not Lean endpoints. The exact per-ID scope is in results.json.

## Square-grid fractional general position (366902)

A shortest path in an n by n grid is monotone in each coordinate. Every such path extends to a path between one of the two opposite-corner pairs. For nonnegative weights it therefore suffices to constrain those maximal paths. Reflection and rotation preserve feasibility and total weight; averaging over the dihedral group justifies using orbit variables for an optimization diagnostic.

The separator in scripts/grid.py computes the heaviest opposite-corner path by dynamic programming in both orientations. It adds a violated constraint and resolves the finite LP. After convergence it reconstructs all orbit weights as rational numbers, recomputes maximum path weights using Fraction arithmetic, and records the full weights and orbit map. Every n from 3 through 50 gives a feasible rational labelling whose objective equals the best printed bound. This does not certify an upper bound: the LP upper certificates were not reconstructed, and none of these programs is formalized.

The first run was unbounded because the initial few path constraints did not cover every orbit. It was corrected by imposing the valid coordinate bound 0 <= weight <= 2. The failed log is retained. This is an initialization error, not a counterexample.

A full proof needs an explicit positive measure on monotone paths whose vertex coverage yields the conjectured objective. Recovering different finite dual bases at successive n does not give a uniform construction. Symmetry and exact path feasibility remove two implementation uncertainties, but do not close this missing dual theorem. Further brute-force orders have sharply diminishing discovery value.

## Lexicodes (367213)

The greedy construction can be implemented by banning all (k-2)-subsets of accepted (k-1)-subsets: a new vertex shares an edge in the Johnson graph with an earlier vertex precisely when one of these cores repeats. We exhaust the lexicographic vertex list at k=2,4,8 and directly check overlap of every accepted pair.

A tempting shortcut is to identify the code with a zero-XOR syndrome class. At k=4, with labels 1 through 8, this works. At k=8 it fails: the greedy code has 715 vertices whereas the zero-XOR class with labels 1 through 16 has 435. The accepted vertex (1,2,3,4,8,12,16) has nonzero XOR. Thus a count based only on translations of a Hamming syndrome is not a proof of this lexicode conjecture. A full route would have to use the actual Welter-game characterization cited in Remark 4.14 and prove its cardinality and overlap consequences uniformly. We did not establish those lemmas. Already-known k=16 computations were not repeated.

## Reverse-response permutation game (373644)

The program records a permutation only by the set of length-k patterns it contains. This quotient preserves every legal move and every follower, since choosing p removes exactly the surviving masks containing p. Exhaustive permutation generation therefore permits exact exploration of every reverse-response state for k=3 and k=4 in the reported ranges. The k=5 trajectory sampling is explicitly not exhaustive state exploration.

A failed reverse reply at a small n cannot refute the target: n0(k) is existential. Because there are finitely many forbidden-pattern sets for fixed k, a possible full proof would establish a finite witness threshold for every reachable reverse-closed forbidden set F and nonmonotone p: if p stays legal arbitrarily far out, then a long permutation avoiding F and p but containing reverse(p) must exist. Corollary 2.13 and the monotone endgame then supply the game-theoretic conclusion. Conversely, a refutation needs a repeatable unbounded family of reverse-reply failures. We have neither implication at k >= 5; the small failures are expected and are not candidates.

## XOR-magic graphs (372205)

The source requires a connected simple graph and a bijective vector labelling with zero neighborhood sum, not just a constant neighborhood sum. Relabeling vertices by their vector labels makes identity labels exhaustive for a fixed order. The MILP has one binary variable per unordered edge, integer parity quotients per vertex and bit, degree equations, and zero-XOR equations. Connectedness is checked on returned witnesses. No solver timeout is interpreted as nonexistence.

Connected exact witnesses were found at order 16, degrees 5 and 7, and order 32, degrees 5 and 9. Order 32 degree 7 timed out after 20 seconds with no incumbent. Complements of the open witnesses give closed zero-XOR examples: the total XOR of all labels is zero at these orders, so XOR of a closed complement neighborhood equals XOR of the original open neighborhood. Connectedness of a complement is not inferred automatically.

The most immediate Cayley shortcut fails. For the identity labelling of a Cayley graph on F2^n with connection set S of odd size, the neighborhood sum at x is x + XOR(S), which varies with x. This rules out that particular construction, not arbitrary Cayley labelings. The source's product induction yields existence for certain degree families but does not interpolate every allowed degree. No full parameter construction was found; individual finite graphs are uncredited parameter instances.

## Multipath complexes (372471)

BP_n has n+1 polygon vertices. Faces are edge subsets with indegree and outdegree at most one, no opposite 2-cycle, and no full directed polygon. The recursion enumerates these faces, including the empty face; the chain calculation performs exact F2 elimination on simplicial boundary columns. All n=2 through 14 were computed.

At n=7 the f-vector is (15,84,221,288,187,60,9), so Euler characteristic is 0. The printed conjecture's branches predict ranks 1,2,1 in degrees 0,4,6, giving Euler characteristic 4. The computed ranks instead occur in degrees 0,3,6, consistent with removing the extra +1 in the n=3 mod 4 branch. The contradiction in Euler characteristic already follows over Q or Z; interpreting the F2 calculation as an integral homology classification would be unjustified.

This is recorded as an apparent source indexing defect. It is not proposed for credit, in keeping with the assignment's exclusion of endpoint corrections. No dummy Lean theorem was created for it.

## Remaining finite routes

Schur positivity: source-exact midpoint hook slopes, all triangular partitions through size 30, all subpartitions, symmetry and two-variable coefficient differences; no violation. This extends the source's cited numerical size range 28 by two sizes only and is not a theorem.

Grothendieck positivity: multivariate divided differences, every proper permutation subword, all permutations through order 7; no negative coefficient. Source reports checks through 9, so this is diagnostic replication.

Hook biases: all odd/distinct partitions through n=60 and hook lengths 2 through 10; printed thresholds survive. Distinct-partition residue biases: symmetric residue pairs for moduli 3 through 12, all n through 150, exact dynamic counts; printed thresholds survive.

Hypergraph orientations: every simple 3-uniform hypergraph on at most 5 vertices. Every graph satisfying the report's crossing-cut condition has the required orientation packing. This omits larger graphs, other uniformities, and multiplicities; it proves nothing general.

Positive descendent matroids: the exact GW/QM definition was read, but a verified coefficient model was not obtained. The advertised author-code file was not exposed by the fetched homepage. No honest exact-matroid sweep was possible here; this requested computation remains missing. Full-rank U_(r,r+1) minors can only arise by restriction after deleting loops, since contracting a nonloop lowers rank; so a verified rank-r coefficient matrix would reduce the first search to spanning (r+1)-circuits.
