TROPICAL ving dimension i and j vertices. We already know the
f -vector j fij which is the sum of columns in the f -matrix. The following
result in [2] was obtained by counting regular triangulations of ∆r−1 ×∆n−1 .
Proposition 11 ([2, Corollary 25]). All tropical convex hulls of r generic
points in TPn−1 have the same f -vector. The number of faces of dimension
i is equal to the multinomial coefficient
                                    
                 r+n−i−2                        (r + n − i − 2)!
                                       =                                  .
             r − i − 1, n − i − 1, i     (r − i − 1)! · (n − i − 1)! · i!
8                      FLORIAN BLOCK AND JOSEPHINE YU

A Combinatorial Algorithm for Building the Face Poset. Given the
vertex labels of P, we can compute the whole face poset of P combinatorially.
The following result follows from [2, Corollary 14] and Corollary 8.
Lemma 12. Let F be a face of P with grid aF and let b be a grid arising from
aF by unshading one box such that no row or column is completely unshaded.
Then there is a face G ⊃ F with label aG = b and of one dimenstion higher.
   Conversely, every face can be obtained this way starting from the vertices.
So, instead of computing the free resolution, we can build the fact poset
combinatorially if we know the vertex labels, i.e., the minimal generators
of I ∗ . We have an implementation of this algorithm using Macaulay 2 [3],
Maple [5], and JavaView [8].
Remark 13 (Non-generic Input Vertices). When the input vertices V are
not in generic position, the initial ideal I is not monomial. In that case, we
can replace the weights V with any refinement which makes I a monomial
ideal and proceed as before to build the face poset. We can then compute
the coordinates of the vertices using Lemma 9 and identify vertices with the
same coordinates. We suggest this algorithm without having a proof.
Tropical Halfspaces. Tropical halfspaces introduced in [4] give us an ex-
terior description of tropical polytopes. We can extend our algorithm to
find such a description.



                                C2         C1
             a                       0                  a
                                         C3
                 (a)                 (b)                    (c)

       Figure 3. (a) Tropical hyperplane in TP2 with apex a.
       (b) The sectors at apex 0 in TP2 . (c) Tropical halfspace
       (a, {1, 2}) in TP2 .

   The tropical hyperplane at the apex a ∈ TPn−1 is the set which is the
union of boundaries of theSsectors a + Ci (see Figure 3). For a ∈ TPn−1 ,
∅ 6= A ( [n], the set a + i∈A Ci is a closed tropical halfspace (see Figure
3(c)). Tropical halfspaces are tropically convex, and a tropical polytope
P is the intersection of the inclusionwise minimal halfspaces containing it
[4]. The apex of such a minimal halfspace must be a vertex of P on the
boundary [4, Lemma 3.6]. Recall that the box (i, j) in the grid label of a
                   if and only if vi ∈ v + Cj . Hence P is the intersection of
vertex v is shaded S
the halfspaces v + i∈A Ci such that v is a vertex of P and A is a minimal
subset of columns in the corresponding grid of v such that the shaded boxes
             TROPICAL CONVEXITY VIA CELLULAR RESOLUTIONS                      9

in those column cover all the rows. This description is redundant in general.
We may be able to refine this result as follows.
Conjecture 14. InSthe generic case, a minimal half space with respect to
P has the form v + i∈A Ci where v is a vertex of P and in the grid label of
v the shaded boxes in the columns in A form a partition of [r].
  The converse of the conjecture above is not true, i.e., there are non-
minimal halfspaces of the form described.
Experiments with Computation Time. We experimented with com-
puting tropical cyclic polytopes Cr,n (which will be defined in the next
section) with r input vertices in n − 1 (projective) dimensions. We used
Macaulay 2 [3] on a Sun Blade 150 (UltraSPARC-IIe 550MHz) computer
with 512MB memory. The computation became infeasible when rn > 80
or so, although r = 30, n = 3 worked. The main problem was the insuffi-
cient amount of memory. Some sample computation times for tropical cyclic
polytopes are given in Table 2. We see from the data that computing the
Alexander dual can be a problem. This can be made faster using the Monos
Language for Monomial Decompositions [7].

           n r Initial ideal Alexander dual Free resolution
           3 30         74              433                  2
           4 21         64              944                 23
           6 10         15              221                 27
           8 10         70             4169              1106
       Table 2. Computation times (in seconds) for I, I ∗ , and the
       free resolution for tropical cyclic polytopes Cr,n .


                     4. Tropical Cyclic Polytopes
   Define tropical cyclic polytopes as Cr,n = tconv{v1 , . . . , vr } ⊂ TPn−1 ,
where vij = (i−1)(j−1) for i ∈ [r], j ∈ [n]. Since (i−1)⊙(j−1) = (i−1)(j−1),
this is tropical exponentiation. The Cr,n are generic because the minimum in
any k × k minor of the matrix [vij ] is attained uniquely by the antidiagonal.
An example of a tropical cyclic polytope is shown in Figure 4(a).
   The 2 × 2 minors of [xij ] form a Gröbner basis with respect to V , and the
initial ideal I is the diagonal initial ideal generated by the binomials which
are on the diagonals of the 2 × 2 minors. This correspond to the staircase
triangulation of ∆r−1 × ∆n−1 .
   Consider a path in an r × n grid representing indeterminates xij , which
goes from the lower left corner to the upper right corner, only moving ei-
ther right or up at each step as in Figure 4(b). Such paths are precisely
the maximal sets, with respect to inclusion, that do not contain diagonal
pairs. Hence their complements correspond to the minimal generators of the
Alexander dual I ∗ , which are the monomial labels of the vertices of Cr,n .
10                                              FLORIAN BLOCK AND JOSEPHINE YU

            (0,3,6,9)




                                       (0,2,4,6)                                                                                            1111
                                                                                                                                            0000
                                                                                                                            x11 x12 ... 0000 1111
                                                                                                                                1111
                                                                                                                                0000  1111110000
                                                                                                                                      000000 1111
                                                                                                                                               x1n
                                                                                                                                              000
                                                                                                                                              111
                                                                                                                                              000
                                                                                                                                              111
                                                                                                                                1111
                                                                                                                                0000
                                                                                                                            x210000
                                                                                                                                1111  111111
                                     
PEDIGREE REMAINDER  construction of non-reconstructible pedigrees.
   It is clear that G and H are non-isomorphic, since each of them has
  n−1
2     vertices, but G has the isolated vertex 0, while H has no isolated
vertex. What is an isomorphism between G − gi and H − hi ? An edge
order preserving isomorphism from G − gi to H − hi must map vertices
in a region of the Venn diagram of ∪j|j6=i gj to the corresponding region
of the Venn diagram of ∪j|j6=ihj . Consider any k ∈ [2n ]. The vertex
k(i ← 0) is in gj for some j 6= i if and only if the vertex k(i ← 1) is in
hj , because the two vertices differ only in their i’th digit. Therefore, if
k(i ← 0) is in G, then an edge order preserving isomorphism between
G−gi and H −hi must map the vertex k(i ← 0) to the vertex k(i ← 1).
Similarly, if the vertex k(i ← 1) is in G, then an edge order preserving
isomorphism between G − gi and H − hi must map the vertex k(i ← 1)
to the vertex k(i ← 0). Moreover, this isomorphism is unique. On
the standard hypercube on [2n ], each vertex in G − gi is mapped to its
neighbour along the i’th axis, which is in H − hi .
                        COMBINATORICS OF PEDIGREES                                  7

Example 1. Let n = 4, and let the hypergraphs G and H be defined
on vertex sets [24 ]e and [24 ]o as follows:
      g1 = {0011, 0101, 1001, 1111}, g2 = {0011, 0110, 1010, 1111},
      g3 = {0101, 0110, 1100, 1111}, g4 = {1001, 1010, 1100, 1111},
      h1 = {0001, 0111, 1011, 1101}, h2 = {0010, 0111, 1011, 1110},
      h3 = {0100, 0111, 1101, 1110}, h4 = {1000, 1011, 1101, 1110},
where gi are the edges of G and hi are the edges of H. The isomorphism
π1 from G − g1 to H − h1 that preserves the edge order is given by
π1 (0000) = 0001, π1 (0011) = 0010, π1 (0101) = 0100, π1 (1001) = 1000,
π1 (0110) = 0111, π1 (1010) = 1011, π1 (1100) = 1101, π1 (1111) = 1110.
Observe that π1 (g2 ) = h2 , π1 (g3 ) = h3 , and π1 (g4 ) = h4 under this
map.
Construction of Ti and Ui
    As stated earlier, for each i, pedigrees Ti and Ui must be so con-
structed that (the unique) edge order preserving isomorphism between
G − gj and H − hj extends to an isomorphism between Ti and Ui for
all j 6= i.
    Let a balanced binary tree Ti be defined so that xi is its root and gi
is its set of leaves. By convention, the root xi is the lowest vertex (at
depth 0) in Ti , and the leaves are the highest vertices (at depth n − 2)
in Ti . For a vertex t in Ti , let Ti (t) be the subtree of Ti induced by t
and all vertices in Ti that are above t. Let t0 and t1 be the parents of
t. The subtree Ti (t) is a union of subtrees L(t) and R(t), where L(t)
is induced by vertices t, t0 , and all vertices above t0 , and the subtree
R(t) is induced by vertices t, t1 , and all vertices above t1 . We call L(t)
the left subtree at t, and R(t) the right subtree at t.
    Let i1 , i2 , . . . , in−1 be the integers 1 ≤ j ≤ n; j 6= i in arbitrary order.
The vertices in gi are grouped in such a way that for each vertex t
at depth k; 0 ≤ k ≤ n − 3, if a vertex p ∈ gi is a leaf of L(t) then
p(ik+1 ) = 0, and if a vertex p ∈ gi is a leaf of R(t) then p(ik+1 ) = 1.
    The vertices in hi are partitioned, and a binary tree Ui is constructed
analogously for the same ordering ij ; 1 ≤ j ≤ n − 1.
    For n = 5 and i = 5 and the ordering i1 = 2, i2 = 3, i3 = 1, i4 = 4,
the trees T5 and U5 are shown in Figure 2.
    We show that for every j 6= i, the unique isomorphism between G−gj
and H − hj extends to an isomorphism between Ti and Ui .
    Let b̄ = (b1 , . . . , bj ); 0 ≤ j ≤ n − 2 be a j-tuple of 0’s and 1’s.
Extending a notation introduced earlier, let gi (b̄) denote the set {k ∈
gi |k(i1 ) = b1 , k(i2 ) = b2 , . . . , k(ij ) = bj }, which is the set of leaves of a
binary subtree of Ti rooted at the vertex t(b̄) at depth j. For example,
8                       BHALCHANDRA D. THATTE

                                                            g5

    11000   10001   10100      11101        10010   11011   11110    10111



                                  i3 = 1



                                  i2 = 3
     T5

                                  i1 = 2


                                       x5

                                                            h5

    10000   11001   11100      10101        11010   10011   10110    11111



                                  i3 = 1



                                  i2 = 3
     U5

                                  i1 = 2


                                    x5




            Figure 2. Binary pedigrees T5 and U5 for n = 5

when b̄ = (0), gi (b̄) is the set of leaves above the left parent of xi ,
and t(b̄) is the left parent of xi . The set hi (b̄) and the vertex u(b̄) are
analogously defined for Ui . By convention, an empty tuple b̄ defines
the sets gi and hi , and the trees Ti and Ui , rooted at xi ; and a tuple b̄
of length n − 2 defines singleton subsets {t(b̄)} of gi , and {u(b̄)} of hi .
                     COMBINATORICS OF PEDIGREES                            9

A tuple b̄ of length n − 2 also uniquely determines the digits t(b̄)(in−1 )
and u(b̄)(in−1 ), since we know that #1(t(b̄)) is even and #1(u(b̄)) is
odd. Also, if t(b̄(in−1 )) = 1 then u(b̄(in−1 )) = 0, and if t(b̄(in−1 )) = 0
then u(b̄(in−1 )) = 1. Therefore, the map t(b̄) −→ u(b̄) for all tuples of
length at most n − 2 extends the isomorphism between G − gin−1 and
H − hin−1 .
    Let b̄ be a tuple as above. Extending the notation k(i ← 0) to b̄, we
define b̄(i ← 0) to be the tuple obtained by setting bi = 0 in b̄, and
b̄(i ← 1) to be the tuple obtained by setting bi = 1 in b̄.
    Let b̄ be a tuple of length n − 2 and j ≤ n − 2. By an argument as
in the above paragraph, we have
     (1) if t(b̄(j ← 0)(in−1 )) = 1 then u(b̄(j ← 1)(in−1 )) = 1;
     (2) if t(b̄(j ← 0)(in−1 )) = 0 then u(b̄(j ← 1)(in−1 )) = 0;
     (3) if t(b̄(j ← 1)(in−1 )) = 1 then u(b̄(j ← 0)(in−1 )) = 1;
     (4) if t(b̄(j ← 1)(in−1 )) = 0 then u(b̄(j ← 0)(in−1 )) = 0.
    Therefore, for each j; 1 ≤ j ≤ n − 2, the map defined by
     (1) t(b̄) −→ u(b̄) for all tuples of length at most j − 1;
     (2) t(b̄(j ← 0)) −→ u(b̄(j ← 1)) for all tuples of length at least j;
          and
     (3) t(b̄(j ← 1)) −→ u(b̄(j ← 0)) for all tuples of length at least j
extends the isomorphism between G − gj and H − hj . Observe that
this map sends the vertices in the left subtree L(t(b̄)) in Ti to the
vertices in the right subtree R(u(b̄)) in Ui , and the vertices in the right
subtree R(t(b̄)) in Ti to the vertices in the left subtree L(u(b̄)) in Ui ,
for each tuple b̄ of length j. Since the trees Ti and Tj (and trees Ui and
Uj ) are disjoint except for their founders for all i 6= j, the isomorphism
between G−gj and H−hj extends to an isomorphism between pedigrees
T (X0 \{xj }) and U(X0 \{xj }) for all j.
    An isomorphism between G − gi2 and H − hi2 that extends to an
isomorphism between Ti and Ui ; i 6= i2 is schematically shown in Fig-
ure 3.                                                                     

Remark 1. The pedigrees constructed above do not admit a valid gen-
der labelling. That is, we cannot assign labels m (male) and f (female)
to all vertices so that each vertex (except founders) has one male par-
ent and one female parent. For example, in the n = 3 case, K3 is not a
bipartite graph, so a valid gender labelling is impossible. But the exam-
ples can be easily modified to create non-reconstructible pedigrees that
also admit valid gender labels. Each vertex in a pedigree constructed
above may be duplicated, and one vertex may be treated male and the
other female, as shown in Figure 4. At the bottom of the tree Ti (or
10                    BHALCHANDRA D. THATTE

                            {k ∈ gi |k(b1 ) = 1, k(b2 ) = 0}
                                            {k ∈ gi |k(b1 ) = 1, k(b2 ) = 1}




                                                                     i3



                                                                     i2
Ti


                                                                     i1

                                              {k ∈ hi |k(b1 ) = 1, k(b2 ) = 0}

                                                {k ∈ hi |k(b1 ) = 1, k(b2 ) = 1}




                                                                     i3



                                                                     i2
Ui


                                                                     i1




       Figure 3. Isomorphism between G − gi2 and H − hi2
       extends to an isomorphism between Ti and Ui

                                                      f
Ui ), the vertex xi is duplicated as vertices xm
                                               i and xi , and the new
                                f
vertex xi is a child of xm
                         i and xi .


Remark 2. Let k, k ′ ∈ [2n ] be any two adjacent vertices on the hyper-
cube. From Equation (1), if a(k) − b(k) = p > 0 for some p, then
                        COMBINATORICS OF PEDIGREES                         11




m                   f




     Ti


                         xm
                          i                         xfi

                                                    xi




          Figure 4. Construction of a pedigree with a valid gen-
          der labelling

b(k ′ ) − a(k ′ ) = p, regardless of which digit k and k ′ differ at. In fact,
by connectivity of the hypercube, we have a(r) − b(r) = p for all ver-
tices r ∈ [2n ] that are at even distance from k on the hypercube, and
b(r) − a(r) = p for all vertices r ∈ [2n ] that are at odd distance from k
on the hypercube. This further implies that the hypergraphs G and H
constructed in the above counter example have a special structure: for
each i; 1 ≤ i ≤ n, |gi | = |hi | ≥ 2n−2 . Let G(d) be the hypergraph with
edge set {gi (d); 1 ≤ i ≤ n}, where gi (d) is the set of grandparents of xi
at depth d in the pedigree T (X0 ), and let H(d) and hi (d) be similarly
defined for the pedigree U(X0 ), then the hypergraphs G(d) and H(d)
must be isomorphic whenever d < n − 2.
   We end this subsection with a conjecture motivated by the observa-
tions made in Remark 2.
Conjecture 1. The counter example constructed in Theorem 1 is min-
imal. In other words, if a pedigree T (X0 ) of order n is not (n − 1)-
reconstructible then it has depth at least n − 2, and there are at least
2n−1 ancestors at depth n − 2.
12                      BHALCHANDRA D. THATTE

Remark 3. Let G and H be simple graphs with edge sets E(G) =
{gi ; 1 ≤ i ≤ m} and E(H) = {hi ; 1 ≤ i ≤ m}, respectively, such that
G − gi ∼ = H − hi for all 1 ≤ i ≤ m. Then the edge reconstruction
conjecture states that G ∼= H provided m > 3. The condition m > 3 is
required since K1,3 and K3 - the graphs used as the base case of our con-
struction of non-reconstructible pedigrees - are not edge reconstructible.
Although no counter examples are yet known, Nash-Williams [2] proved
a characterisation of (hypothetical) counter examples to edge recon-
struction. His characterisation was based on a generalisation of ideas
earlier introduced by Lovász [1]. Without going into details, we note
that the counter examples presented here have certain similarities with
the characterisation by Nash-Williams. It may be possible to exploit
such similarities to prove Conjecture 1.
2.2. A positive result. Let T (X0 ) be a discrete generation pedigree
on X0 of order n > 2. Let Sn−1 (T ) = {T (Y )|Y ⊂ X0 , |Y | = n − 1}.
Consider the edge labelled (multi) graph G1 whose vertex set is X1
(that is, the vertices at depth 1), and vertices x, y ∈ X1 are joined by
an edge ei if they are the parents of xi .
Lemma 1. If there are vertices xi and xj in X0 that have the same
parents, then T (X0 ) is uniquely determined by Sn−1 (T ).
Proof. The situation in the lemma is recognised by looking at T (X0 \xk ),
where xk 6∈ {xi , xj }. Now T (X0 ) is uniquely obtained from T (X0 \xi )
by joining xi to the parents of xj .                                  
Lemma 2. If n > 3 and if G1 contains a cycle then T (X0 ) is uniquely
determined Sn−1 (T ).
Proof. Let ei be an edge in a cycle in G1 . The end vertices of ei are the
two parents of xi . Since the set of half brothers of xi is known from the
collection Sn−1 , the parents of xi are uniquely recognised in T (X\xi ).
Note that we need the condition n > 3 because otherwise we would get
a counter example based on G1 ∼    = K3 or G1 ∼ = K1,3 .
                                                                        
Corollary 1. If |X1 | ≤ n and n > 3 then Sn−1 (T ) determines T (X0 )
up to congruence.
Proof. If no two vertices in X0 have the same two parents then G1 has
n simple edges (that is no two edges are parallel edges), and there is a
cycle in G1 .                                                         
     We end this section with another conjecture.
                     COMBINATORICS OF PEDIGREES                            13

Conjecture 2. Discrete generation pedigrees of order n that have a
constant population in each generation are r-reconstructible for r >
log n.
   This conjecture is true if Conjecture 1 is true. For suppose that
Conjecture 1 is true but Conjecture 2 is not true, and that there is
a pedigree of order n that is not r-reconstructible for some r > log n.
Therefore, for some r > log n, there is a sub-pedigree of order r +1 that
is not r-reconstructible. Such a sub-pedigree must have depth at least
r − 1, and must have at least 2r
DEFINITION − 2) oriented triangle inequalities OTij,k
and n(n − 1) non-negativity inequalities NNij on n points; it is a full-dimensional cone in
Rn(n−1) .
    Note, that in the semi-metric case, the triangle inequalities imply non-negativity of the
distance; it is not the case in our oriented case.
    Through all paper we will represent vectors in Rn(n−1) as square matrices of order n with
zeroes on the main diagonal. It is easy to see that

                                 METn = {a + aT , with a ∈ QMETn }

where aT denotes the transpose matrix. Moreover, any extreme ray e of METn has a form
e = g + g T , where g is an extreme ray of QMETn (in fact, e is a sum of extreme rays of
QMETn with non-negative coefficients, and e = (e + eT )/2).

    Consider now the notions of oriented cut and oriented multi-cut quasi-semi-metrics. Given
                                                                                          ′
an ordered partition (S1 , . . . , Sq ) (q ≥ 2) of Vn , the quasi-semi-metric δ (S1 , . . . , Sq ) is called
                                 ′                                                          ′
an oriented multi-cut, if δ (S1 , . . . , Sq )ij = 1 for i ∈ Sα , j ∈ Sβ , α < β and δ (S1 , . . . , Sq )ij = 0,
otherwise. This notion was considered, for example, in [ShLi95]. Given a subset S of Vn , the
                          ′                                 ′                                       ′
quasi-semi-metric δ (S) is called oriented cut, if δ (S)ij = 1 for i ∈ S, j 6∈ S and δ (S)ij = 0,
otherwise. Clearly, an oriented cut is the case q = 2 of an oriented multi-cut. The full-
dimensional cone in Rn(n−1) , generated by all non-zero oriented multi-cuts on Vn , is denoted by
OMCUTn .
    Given a partition (S1 , . . . , Sq ) of Vn , the semi-metric δ(S1 , . . . , Sq ) is called a multi-cut, if
δ(S1 , . . . , Sq )ij = 1 for i ∈ Sα , j ∈ Sβ , α 6= β and δ(S1 , . . . , Sq )ij = 0, otherwise. Given a subset
S of Vn , the semi-metric δ(S) is called a cut, if δ(S)ij = 1 if |S ∩ {i, j}| = 1 and δ(S)ij = 1 = 0,
otherwise. Clearly, cuts are multi-cuts with q = 2. The n(n − 1)/2-dimensional cone in Rn(n−1) ,
generated by all non-zero cuts on Vn , is denoted by CUTn .
    Note, that in the semi-metric case, the multi-cuts with q > 2 are not extreme rays (they
are interior points) of CUTn ; it relies on the formula:
                                                                  q
                                                                  X
                                        δ(S1 , . . . , Sq ) = (         δ(Si ))/2
                                                                  i=1

On the other hand,
                                                    ′                       ′
                            δ(S1 , . . . , Sq ) = δ (S1 , . . . , Sq ) + δ (Sq , . . . , S1 )

and so,

                                CUTn = {a + aT , with a ∈ OMCUTn } .
                                                                                      ′
The number of all oriented cuts on n points is 2n and the number p (n) ofP  all oriented multi-cuts
                                                                  ′       1
on Vn is the number of all ordered partitions of n. In fact, p (n) = 2 π∈Sym(n) x1+d(π) with
d(π) := |{i ≤ n|ai > ai+1 }| for the permutation π = (a1 , . . . , an ) ∈ Sym(n). So, p′ (3) = 13,
p′ (4) = 75, p′ (5) = 541, p′ (6) = 4683, p′ (7) = 47293, p′ (8) = 545835. The number of ex-
treme rays of OMCUTn is p′ (n) − 1, since we excluded 0; the number of orbits of those rays is
2, 5, 9, 19, 35, 71 for n = 3, 4, 5, 6, 7, 8.
                                                           Pn
     Let C be a cone in Rn . Given v ∈ Rn , the inequality
                                                  Pn        i=1 vi xi ≥ 0 is said to be valid for C,
if it holds for all x ∈ C.PThen the set {x ∈ C| i=1 vi xi = 0} is called the face of C, induced
by the valid inequality ni=1 vi xi ≥ 0. A face of dimension dim(C) − 1 is called a facet of C; a
face of dimension 1 is called an extreme ray of C.
   Two extreme ray
