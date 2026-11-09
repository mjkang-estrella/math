# Dormant only —338806
No dispatch or execution authorized in this lane. No code, compiler, checker or formal API was run.

Prospective exact endpoint: exists epsilon:Real, epsilon>0 and exists Delta:Nat, Delta>0 and forall g:Nat, g>0 implies exists finite simple undirected graph G with maxDegree<=Delta, no simple cycle of length<g, and nu_ur(G)<(1-epsilon)*nu(G). Bind epsilon=1/4 and Delta=100; derive the negation of the original full quantifiers with all finite vertex types covered.

Definitions must match actual source: a matching is a set of pairwise disjoint unordered edges; uniquely restricted forbids every distinct matching on exactly the same covered vertex set; girth condition means no cycle below g (including forests), and maximum degree is the total undirected degree. Preserve original token/decoded statement hashes from originals.json.

Required new proofs, all presently UNIMPLEMENTED:
1. Finite DAG topological ordering by induction and directed-cycle-to-distinct-covered-matching replacement, preserving injectivity of vertices and matching edges.
2. Uniform finite probability on tuples of100 permutations of Fin N; avoidance probability via falling factorials; independent-colour product; union bound over both subset spaces. Could replace exp bounds by rational finite-count bounds to minimize analytic dependencies, but that conversion must itself be proved, not asserted.
3. Coloured simple-cycle witnesses, including distinct-colour parallel2-cycles. Bound count of witnesses and each event, including conflicts within one permutation and repeated pair constraints.
4. Markov/first-moment deletion with an explicit sufficiently large multiple-of4 N for every g; finite sum B_h and chosen N need no graph enumeration. Prove all deleted vertices form a bounded union.
5. Induced surviving simple graph, max degree, girth, inherited no-hole property, and first-permutation matching losing at most the total deleted vertex count.
6. Maximum existence for both matching classes, empty-rectangle obstruction and strict rational ratio arithmetic, then exact negation bridge.

An arbitrary existence witness is allowed mathematically; a small concrete graph certificate is not presently supplied. The all-g proof is finite probabilistic combinatorics rather than a finite search. Feasibility requires substantial infrastructure; no short implementation estimate claimed. Only propext, Classical.choice, Quot.sound may occur in eventual axioms. No sorry/admit/extra axiom/unsafe/native_decide. Independent ordinary proof and source-fidelity/significance/final/prior review must precede any root-authorized formal lane. Then audit full transitive bodies, paper and fresh extracted strict replay. Credit remains0.
