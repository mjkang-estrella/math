# R21 mathematical checkpoint: connected self-dual counterexamples

Myeongjin Kang; no affiliation. Original prose CC BY 4.0, code MIT.
No full target frozen and no contribution verdict or count at this checkpoint.

Let M_0,M_1 be the exact family-185 source pair at pin
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Define N_i=(M_i^+)^-, where
M^+ has bases B+f for a basis B of M and f outside B, and P^- has bases
A-e for a basis A of P and e in A. These are standard infinite-matroid
elongation and truncation. The source pair has all finite sets independent,
all bases and cobases infinite, and M_i=M_i^* on the same labels.

**Proposed deduction with full proof route:** N_0,N_1 are connected,
self-dual on the same labels, and admit no independent covering, no
packing/covering partition, and no intersection witness. Every finite set
is independent in each, as well as in each dual. This is not yet nominated;
the operations may be technical relative to the source.

1. The bases of N_i are exactly B itself and B-e+f, for B a source basis,
e in B and f outside B. Indeed remove f or a point of B from B+f.
Conversely all such sets occur, and B occurs since its complement is
nonempty. Complementation takes B-e+f to (E minus B)-f+e, another such
basis because M_i is identically self-dual. Thus N_i=N_i^*.

2. Every M_i-independent set remains N_i-independent because every M_i
basis is an N_i basis. In particular every finite set is independent.
For distinct e,f extend {e,f} to a basis A of M_i^+. Every proper subset
of A is contained in A-a for some a in A, hence is N_i-independent.
A itself is N_i-dependent: if contained in an N_i basis A'-b, it would
be properly contained in an M_i^+ basis A', contradicting maximality of A.
Thus A is an N_i circuit containing e,f. Every pair lies in a common
circuit, proving connectedness. Dual connectedness is automatic here.

3. Every N_i-independent J is contained in a basis B-e+f or B of N_i,
so deletion of at most one point from J yields an M_i-independent set.
Suppose J_0,J_1 cover E. Shrink J_1 to E minus J_0 to get a partition;
finite-error independence is hereditary. At each double-ray vertex the
assigned elements differ by finitely many points from a Q-independent
set. Extend that independent part to a local Q basis B.

Write x for the assigned labels on the inward bundle and z on the
outward bundle. Up to finite exceptions, x is contained in B_L and z
in B_R. If x is ultrafilter-large, so is B_L, since the ultrafilter
avoids finite sets. The source basis inequality gives

    rho(B_L) > rho(D minus B_R).

The source Lemma rank in 03-filters says both largeness and rho are
invariant modulo K, which contains all finite sets, and rho is antitone
under inclusion modulo K. Therefore D minus z is large and

    rho(x) >= rho(B_L) > rho(D minus B_R) >= rho(D minus z).

The next vertex's inward assignment is exactly D minus z. The central
bundle gives one large inward assignment, and outward propagation
produces an infinite strictly decreasing sequence of ordinals. This is
impossible. Thus no such finite-error covering exists. The same argument
actually allows a separate finite error at every local Q component; no
uniform total error bound is used.

4. The source self-dual reduction (02-matroids, Lemma
lem:selfdual-reduction) now excludes packing/covering partitions for
N_0,N_1. The standard Bowler–Carmesin equivalence between intersection
of (N_0,N_1) and packing/covering for (N_0,N_1^*) excludes intersection,
since N_1=N_1^*. No replacement by finitary or tame matroids is asserted.

**Primary operations already read:** Bowler, Infinite Matroids habilitation,
Section 1.7.2, defines both operations, identifies old bases as circuits
of truncation, and identifies elongation-independent sets as sets becoming
old-independent after deleting at most one point. Gollin–Joó 2504.05064v1
introduction repeats standard finite truncation and distinguishes it from
wild generalized truncation. No new truncation theorem is claimed here.
The only interaction to assess is the complement-symmetric one-exchange
basis family plus preservation of the source descent under finite errors.
