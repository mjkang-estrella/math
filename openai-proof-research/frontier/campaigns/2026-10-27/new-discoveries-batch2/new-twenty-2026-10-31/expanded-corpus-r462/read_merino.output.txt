                               Advances in Mathematics 446 (2024) 109674



                                  Contents lists available at ScienceDirect


                                Advances in Mathematics
                              journal homepage: www.elsevier.com/locate/aim




The Merino–Welsh conjecture is false for matroids ✩
Csongor Beke a , Gergely Kál Csáji b , Péter Csikvári c,d,∗ ,
Sára Pituk e
a
  Trinity College, University of Cambridge, CB2 1TQ, United Kingdom
b
  Institute of Economics, Centre for Economic and Regional Studies, Hungary,
H-1097 Budapest, Tóth Kálmán u. 4, Hungary
c
  HUN-REN Alfréd Rényi Institute of Mathematics, H-1053 Budapest, Reáltanoda
utca 13-15, Hungary
d
  ELTE: Eötvös Loránd University, Mathematics Institute, Department of
Computer Science, H-1117 Budapest, Pázmány Péter sétány 1/C, Hungary
e
  ELTE: Eötvös Loránd University, H-1117 Budapest, Pázmány Péter sétány 1/C,
Hungary



a r t i c l e      i n f o                 a b s t r a c t

Article history:                           The matroidal version of the Merino–Welsh conjecture states
Received 9 November 2023                   that the Tutte polynomial TM (x, y) of any matroid M without
Received in revised form 16                loops and coloops satisﬁes that
February 2024
Accepted 27 March 2024
Available online xxxx                                    max(TM (2, 0), TM (0, 2)) ⩾ TM (1, 1).
Communicated by Y. Zhao
                                           Equivalently, if the Merino–Welsh conjecture is true for
MSC:
primary 05C30                              all matroids without loops and coloops, then the following
secondary 05C31, 05C70                     inequalities are also satisﬁed for all matroids without loops
                                           and coloops:
Keywords:
                                                           TM (2, 0) + TM (0, 2) ⩾ 2TM (1, 1),

 ✩
   Péter Csikvári is supported by the MTA-Rényi Counting in Sparse Graphs “Momentum” Research Group
and by the Dynasnet ERC Synergy project (ERC-2018-SYG 810115). Gergely Kál Csáji is supported by the
Hungarian Scientiﬁc Research Fund, OTKA, Grant No. K143858, by the Momentum Grant of the Hungarian
Academy of Sciences, grant number 2021-1/2021 and by the Ministry of Culture and Innovation of Hungary
from the National Research, Development and Innovation fund, ﬁnanced under the KDP-2023 funding
scheme (grant number C2258525). Sára Pituk is supported by the Ministry of Culture and Innovation
and the National Research, Development and Innovation Oﬃce within the Quantum Information National
Laboratory of Hungary (Grant No. 2022-2.1.1-NL-2022-00004).
 * Corresponding author.
   E-mail addresses: bekecsongor@gmail.com (C. Beke), csaji.gergely@krtk.hun-ren.hu (G.K. Csáji),
peter.csikvari@gmail.com (P. Csikvári), pituksari@gmail.com (S. Pituk).

https://doi.org/10.1016/j.aim.2024.109674
0001-8708/© 2024 The Authors. Published by Elsevier Inc. This is an open access article under the CC
BY-NC-ND license (http://creativecommons.org/licenses/by-nc-nd/4.0/).
2                  C. Beke et al. / Advances in Mathematics 446 (2024) 109674


Tutte polynomial                         and
Merino–Welsh conjecture

                                                       TM (2, 0)TM (0, 2) ⩾ TM (1, 1)2 .

                                         We show a counter-example for these inequalities.
                                          © 2024 The Authors. Published by Elsevier Inc. This is an
                                                open access article under the CC BY-NC-ND license
                                               (http://creativecommons.org/licenses/by-nc-nd/4.0/).




1. Introduction

   For a connected graph G, let τ (G), α(G) and α∗ (G) denote the number of spanning
trees, the number of acyclic orientations and the number of strongly connected orien-
tations, respectively. Merino and Welsh [18] conjectured that if G is a connected graph
without loops and bridges, then

                                  max(α(G), α∗ (G)) ⩾ τ (G).

Note that α(G), α∗ (G), and τ (G) are all evaluations of the Tutte polynomial, namely,
TG (2, 0) = α(G), TG (0, 2) = α∗ (G), and TG (1, 1) = τ (G), where the Tutte polynomial
TG (x, y) is deﬁned as
                                 
                   TG (x, y) =         (x − 1)k(A)−k(E) (y − 1)k(A)+|A|−v(G) ,
                                 A⊆E


with k(A) denoting the number of connected components of the graph (V, A), see [22].
There is a vast amount of literature on the properties of the Tutte polynomial and its
applications, for instance, [2,5,6,23], or the book [7].
   Conde and Merino [4] also suggested the following “additive” and “multiplicative”
versions of the conjecture:

                              TG (2, 0) + TG (0, 2) ⩾ 2TG (1, 1),

and

                                 TG (2, 0)TG (0, 2) ⩾ TG (1, 1)2 .

It is easy to see that the multiplicative version implies the additive version which in turn
implies the maximum version.
    The Merino–Welsh conjecture and its variants triggered considerable attention.
Thomassen [21] proved that the conjecture is true if the graph G is suﬃciently sparse
or suﬃciently dense. Lin [15] proved it for 3-connected graphs satisfying certain de-
gree conditions. Noble and Royle [19] proved the multiplicative version for series-parallel
graphs.
                   C. Beke et al. / Advances in Mathematics 446 (2024) 109674                3



    The Tutte polynomial naturally extends to matroids. Recall that a matroid M is a
pair (E, I) such that I ⊆ 2E , called the independent sets, satisfying the axioms (i) ∅ ∈ I,
(ii) if A ⊆ A ∈ I, then A ∈ I, and (iii) if A, B ∈ I such that |B| < |A|, then there
exists an x ∈ A \ B such that B ∪ {x} ∈ I. Given a set S ⊆ E, the maximal independent
subsets of S all have the same cardinality, and this cardinality is called the rank of the
matroid, denoted by r(S). The maximum size independent sets of M are called bases,
and their set is denoted by B(M ). The dual of a matroid M is the matroid M ∗ whose
bases are {E \ B | B ∈ B(M )}. For further details on matroids, see for instance [20]
    Given a graph G = (V, E), the edge sets of the spanning forests of G form the in-
dependent sets of a matroid MG called the cycle matroid of G. If G is connected, then
the basis of MG is the spanning trees of G. One can deﬁne the Tutte polynomial of a
matroid as
                                    
                      TM (x, y) =         (x − 1)r(E)−r(S) (y − 1)|S|−r(S) ,
                                    S⊆E


where r(S) is the rank of a set S ⊆ E. When M = MG , then TMG (x, y) = TG (x, y). A
loop in a matroid M is an element x ∈ E such that r({x}) = 0, that is, {x} ∈      / I, and
a coloop is an element that is a loop in the dual M ∗ of the matroid M . Equivalently, a
coloop is an element that is in every base of M . For a cycle matroid MG, loops correspond
to loop edges and coloops correspond to bridges in the graph G.
   Hence it was suggested that the inequalities

                            max(TM (2, 0), TM (0, 2) ⩾ TM (1, 1),
                             TM (2, 0) + TM (0, 2) ⩾ 2TM (1, 1),
                               TM (2, 0)TM (0, 2) ⩾ TM (1, 1)2

may hold true for all matroids M without loops and coloops. (These versions appear
explicitly in [10], but were treated much earlier without explicitly calling them conjec-
tures.) Note that for general matroids, all these versions are equivalent in the following
sense: if one of them is true for all matroids, then the others are also true for all matroids.
Applying the maximum version to M ⊕ M ∗ with M ∗ being the dual of M leads to the
multiplicative version of the conjecture. (Here M ⊕ N denotes the disjoint union of the
matroids M and N .)
   Knauer, Martínez-Sandoval, and Ramírez Alfonsín [13] proved that the class of lattice
path matroids satisﬁes the multiplicative version. Ibañez, Merino and Rodríguez [16]
proved the maximum version for some families of graphs and matroids. Chávez-Lomelí,
Merino, Noble and Ramírez-Ibáñez [3] proved the additive version for paving matroids
without coloops. In fact, they showed that the polynomial TM (x, 2 − x) is convex on
the interval [0, 2] for these matroids. Recently, Ferroni and Schröter [10] proved the
multiplicative version of the conjecture for split matroids. Kung [14] proved the additive
version for some special matroids based on their size and rank. Jackson [11] proved that
4                 C. Beke et al. / Advances in Mathematics 446 (2024) 109674



                               TM (3, 0)TM (0, 3) ⩾ TM (1, 1)2

for matroids without loops and coloops. He phrased it for graphs but he also noted that
his proof extends to matroids.
   The aim of this short note is to give a counter-example for these inequalities for general
matroids.

Theorem 1.1. There are inﬁnitely many matroids M without loops and coloops for which

                              TM (2, 0)TM (0, 2) < TM (1, 1)2 .

   In fact, we show the following slightly stronger result. Let x0 be the largest root of
the polynomial x3 − 9(x − 1). We have x0 ≈ 2.22668...

Theorem 1.2. If 0 ⩽ x < x0 , then there are inﬁnitely many matroids M without loops
and coloops for which

                              TM (x, 0)TM (0, x) < TM (1, 1)2 .

  It is interesting to compare this result with the above inequality of Jackson. In the
paper [1], the authors of this paper show that 3 can be improved to 2.9243.

  Organization of the paper. In the next section, we prove Theorems 1.1 and 1.2. Then
we give some insight into where the counter-example came from. We end the paper with
some concluding remarks.

2. Counter-examples

   The counter-example for the multiplicative version of the Merino–Welsh conjecture
is surprisingly simple. Let Un,r be the uniform matroid on n elements with rank r. Let
  (2)
Un,r be the 2-thickening of Un,r , that is, we replace each element of Un,r with 2 parallel
                                                         (2)
elements. We will show that if x < x0 , then Mn = Un, 2 n satisﬁes the theorem for large
                                                           3
enough n if n is divisible by 3, hence concluding Theorems 1.2 and 1.1.
                                                     (2)
   The computation of the Tutte polynomial of Un,r relies on two well-known lemmas.

Lemma 2.1 (Formula (2.24) in [17]). The Tutte polynomial of the matroid Un,r is the
following:

                                   r            n−r      
                                        n−i−1 i  n−j−1 j
                  TUn,r (x, y) =               x +             y
                                   i=1
                                        n−r−1      j=1
                                                         r−1

if 0 < r < n, and TUn,n (x, y) = xn and TUn,0 (x, y) = y n .
                     C. Beke et al. / Advances in Mathematics 446 (2024) 109674                      5



Lemma 2.2 (Jaeger, Vertigan and Welsh [12], formula (3.47) of [17]). Let M be a ma-
troid, and let M (k) be its k-thickening, that is, we replace each element of M with k
parallel elements. Then
                                                             k−1                              
                                                             y     + y k−2 + · · · + y + x k
      TM (k) (x, y) = (y k−1 + y k−2 + · · · + 1)r(M ) TM                                  , y   .
                                                             y k−1 + y k−2 + · · · + y + 1

By Lemma 2.2 we have

                                       TM (2) (x, 0) = TM (x, 0),
                                                                       
                                                                  x
                           TM (2) (0, x) = (x + 1)r(M ) TM          , x2 ,
                                                               x+1

and

                                   TM (2) (1, 1) = 2r(M ) TM (1, 1).

Clearly, these expressions together with the exact formula for TUn,r (x, y) make the com-
putation of TUn,r
                (2) (x, y) very fast for speciﬁc values of n, r, x, y.

   The matroid with the smallest number of elements that we are aware of being a
counter-example to the multiplicative version of the Merino–Welsh conjecture is M =
  (2)
U33,22 with 66 elements. For this matroid, we have TM (2, 0) = 8374746166, TM (0, 2) =
64127582356390782814, TM (1, 1) = 811751838842880, and

                                   TM (2, 0)TM (0, 2)
                                                      ≈ 0.815...
                                      TM (1, 1)2

  To prove Theorem 1.2, our next goal is to understand the exponential growth of
TUn,r (x, 0).

Lemma 2.3. Let r = nα and x > 1, then
                                         
                                          f (n) exp(nH(α))           if x < α1 ,
                        TUn,r (x, 0) =
                                          f (n)(x(x − 1)α−1 )n       if x ⩾ α1 ,

where nK > f (n) > n−K for some ﬁxed K, and H(α) = −α ln(α) − (1 − α) ln(1 − α).

Proof. We can determine the dominating term of TUn,r (x, 0) by comparing two neigh-
boring terms:
                                     
                 n−i−1 i       n − i − 2 i+1                               n−i−1
                         x ⩾              x            if and only if            ⩾ x.
                 n−r−1         n−r−1                                        r−i
6                     C. Beke et al. / Advances in Mathematics 446 (2024) 109674


         n−i−1  i                  
                                       xr−(n−1)
Hence,           x  is maximized  at             . If the right-hand side is negative, then
         n−r−1
                                         x−1       n 
the dominating term is at i = 1 and n−r−1 ∼ n−r
                                           n−2
                                                           ∼ exp(nH(α)), where ∼ means
the estimation is valid up to some n . When x = α , then exp(H(α)) = x(x − 1)α−1 ,
                                       K                1

so we can assume that x ⩾ α1 in the rest of the proof since then on the whole interval
 1
 1, α we have TUn,r (x, 0) ∼ exp(nH(α)).
   For the sake of simplicity, we carry out the estimation of the dominating term at

                                           xr − n   xα − 1
                                      i=          =        n
                                            x−1      x−1

and we drop the integer part. All these changes aﬀect our computation up to a term n−K .
                                                           m               √
In the forthcoming computation, we also estimate m! ∼ m     e  as the terms 2πm(1 +
o(1)) can be integrated into f (n):
                                 
                   n−i−1 i      n−i i
                          x ∼         x
                   n−r−1        n−r
                                   n−i n−i
                                ∼      
                                          e
                                                x
                                                     i
                                     n−r n−r r−i r−i
                                      e       e

                                                                      n 1− xα−1
                                                                            x−1
                                               n 1 − xα−1
                                                      x−1
                                =                                                          xi
                                                                              n α− xα−1
                                                                                    x−1
                                    (n(1 − α))n(1−α) n α − xα−1
                                                            x−1
                                    ⎛             x(1−α)
                                                         ⎞ n
                                           x(1−α)      x−1
                                 ⎜                                    ⎟ i
                                =⎜                                    ⎟ x
                                            x−1
                                 ⎝                           1−α
                                                             x−1
                                                                      ⎠
                                     (1 − α)1−α       1−α
                                                      x−1

                                      x(1−α)                 n
                                = x x−1 (x − 1)α−1               xi
                                      x(1−α)                 n     xα−1
                                = x x−1 (x − 1)α−1               x x−1 n

                                = (x(x − 1)α−1 )n ,

and the result follows. 

Lemma 2.4. Let r = αn and assume that x ⩾ α1 and x2 ⩾ 1−α
                                                       1
                                                          . Then for the matroid
         (2)
M = Un,r , we have
                                                                                 n
                         TM (1, 1)2                       22α          x−1
                                        = g(n)                       ·                 ,
                     TM (x, 0)TM (0, x)              α (1 − α)
                                                      2α      2(1−α)    x3

where nK > g(n) > n−K for some ﬁxed K.
                       C. Beke et al. / Advances in Mathematics 446 (2024) 109674                                7



Proof. We have
                                                                           n
                                                           n          2α
                TM (1, 1) = 2r TUn,r (1, 1)) = 2r            ∼                   .
                                                           r    αα (1 − α)1−α

Furthermore,

                               TM (x, 0) = TUn,r (x, 0) ∼ (x(x − 1)α−1 )n

as x ≥ α1 . Finally,
                                                                                  
                       r             x                                         x                           
TM (0, x) = (x + 1) TUn,r               , x2                 r
                                                   = (x + 1) TUn,r                , 0 + (x + 1)r TUn,r 0, x2 .
                                    x+1                                       x+1

Here, the second term will dominate the ﬁrst one as TUn,r                                x
                                                                                        x+1 , 0   < TUn,r (1, 1) ∼
exp(nH(α)), while
                             
                   TUn,r 0, x2 = TUn,n−r (x2 , 0) ∼ (x2 (x2 − 1)(1−α)−1 )n

as x2 ⩾ 1−α
         1
            . Putting everything together, we get that
                                                       n
       TM (1, 1)2                         22α
                      ∼                                      (x(x − 1)α−1 (x + 1)α x2 (x2 − 1)−α )−n
   TM (x, 0)TM (0, x)              α2α (1 − α)2(1−α)
                                                                    n
                                          22α          x−1
                           ∼                         ·                    .    
                                   α2α (1 − α)2(1−α)    x3
                                                                                   2α
                                                        2                    2
Proof of Theorem 1.2. The maximum of the function α2α (1−α) 2(1−α) is at α = 3 , where

it takes value 9. We can assume by monotonicity that 2 ⩽ x < x0 . Then x ⩾ α1 = 32 and
                                 (2)
x2 ⩾ 1−α1
           = 3, whence for M = Un, 2 n , we get that
                                               3

                                                                                n
                                TM (1, 1)2                           9(x − 1)
                                               ⩾ n−K                                  >1
                            TM (x, 0)TM (0, x)                          x3

for large enough n as 9(x−1)
                        x3   > 1.           

3. Intuition behind the counter-examples

   In this section, we try to explain the underlying intuition behind the counter-examples.
   It turns out that the Merino–Welsh conjecture is strongly related to the “local struc-
ture” of a matroid. To make this statement more precise, we need the concept of the
local basis exchange graph. This is a bipartite graph associated with a basis B ∈ B(M )
of the matroid M whose parts are the elements of B on one side, and the non-elements
on the other side. We connect an element b ∈ B with c ∈ E \ B if (B \ {b}) ∪ {c} is again
8                 C. Beke et al. / Advances in Mathematics 446 (2024) 109674



a basis. Let us call this bipartite graph HM [B]. It turns out [1] that one can associate a
polynomial THM [B] (x, y) to each local basis exchange graph such that
                                               
                               TM (x, y) =           THM [B] (x, y).
                                               B∈B


We call the polynomial TH (x, y) the permutation Tutte polynomial of the graph H in
the paper [1]. We do not go into details about the actual deﬁnition of this polynomial
as we only need one key observation about it: if for all B ∈ B(M ) we have

                        THM [B] (2, 0)THM [B] (0, 2) ⩾ THM [B] (1, 1)2 ,

then

                              TM (2, 0)TM (0, 2) ⩾ TM (1, 1)2 .

For the balanced complete bipartite graph Kn,n , we have

                               TKn,n (2, 0)TKn,n (0, 2)   nπ
                                                          ≈    ,
                                    TK (1, 1)2
                                         n,n
                                                             4

which shows that the required inequality holds, but the ratio is not exponential in n.
Most probably, the same is true for every suﬃciently dense balanced bipartite graph.
   It turns out that gluing pendant edges to one side of a bipartite graph may actually
decrease the studied ratio. So it is natural to study bipartite graphs that are obtained
from balanced complete bipartite graphs by gluing a pendant edge to each vertex on
one side. For suﬃciently large n these bipartite graphs indeed violate the inequality
TH (2, 0)TH (0, 2) ⩾ TH (1, 1)2 .
   The next question is whether we can construct a matroid M with the desired local
basis exchange graphs. For the matroid Un,r , the local basis exchange graph is Kr,n−r .
When we apply the 2-thickening transformation to any matroid M , then we obtain
HM (2) [B] from HM [B] as follows: each vertex b ∈ B gets a pendant edge, and each
c ∈ E \ B gets a twin c , i.e. a vertex that is connected to the same vertices as c. So in
this way Kr,n−r is transformed into Kr,2(n−r) with a pendant edge attached to each of
the r basis elements. If we choose r = 23 n, then we get a balanced complete bipartite
graph with a pendant edge attached to each vertex on one side of the graph. This is
exactly the bipartite graph that we needed, and we get this graph as the local basis
exchange graph associated with every basis.
   Let us mention that there are graphical matroids where some of the local basis ex-
change graphs are isomorphic to the above bipartite graphs, but unfortunately, not all
of them.
   We believe that the theory of the permutation Tutte polynomial developed in the
paper [1] can attack successfully variations of the Merino–Welsh conjecture, or help
identify critical structures.
                     C. Beke et al. / Advances in Mathematics 446 (2024) 109674                         9



4. Concluding remarks

   Ferroni and Schröter [9] lists ﬁve major open problems concerning invariants of ma-
troids on the fourth page. The ﬁfth one is the matroidal version of the Merino–Welsh
conjecture. Interestingly, another conjecture of this list has been disproved too, Ferroni
[8] provided counter-examples for the Ehrhart positivity of matroids. This shows that
one should be careful with these conjectures, matroids are much more versatile than we
may expect them, and small examples may be misleading. The program initiated by
Ferroni and Schröter [9] generating many examples may lead to more counter-examples
for various conjectures.
   Though the counter-examples given in this note are not graphical matroids, they still
advise caution concerning the Merino–Welsh conjecture. It is also important to note that
the three forms of the Merino–Welsh conjecture are not equivalent for graphs, and it may
occur, for instance, that the original version is true, while the multiplicative version is
false. Below we collected several variants of the conjecture that are still open, including
the original conjecture for graphs.

Problem 4.1 (Graphs). Is the Merino–Welsh conjecture true for graphs?

Problem 4.2 (Binary matroids). Is the Merino–Welsh conjecture true for binary ma-
troids?

Problem 4.3 (Simple and cosimple matroids). Is the Merino–Welsh conjecture true for
matroids that are simple and cosimple at the same time?

   In all these cases it would be interesting to determine the smallest x for which

                                  TM (x, 0)TM (0, x) ⩾ TM (1, 1)2

for every matroid M in the given class.

Acknowledgment

   The authors thank the anonymous referees for their constructive and helpful remarks;
especially, for their encouragement to create the section on the intuition behind the
counter-examples.

References

 [1] C. Beke, G.K. Csáji, P. Csikvári, S. Pituk, Permutation Tutte polynomial, arxiv preprint arXiv:
     2311.01936, 2023.
 [2] T. Brylawski, J. Oxley, The Tutte polynomial and its applications, in: Matroid Applications, vol. 40,
     1992, pp. 123–225.
10                  C. Beke et al. / Advances in Mathematics 446 (2024) 109674



 [3] L.E. Chávez-Lomelí, C. Merino, S.D. Noble, M. Ramírez-Ibáñez, Some inequalities for the Tutte
     polynomial, Eur. J. Comb. 32 (3) (2011) 422–433.
 [4] R. Conde, C. Merino, Comparing the number of acyclic and totally cyclic orientations with that of
     spanning trees of a graph, Int. J. Math. Comput. 2 (2009) 79–89.
 [5] H.H. Crapo, The Tutte polynomial, Aequ. Math. 3 (3) (1969) 211–229.
 [6] J.A. Ellis-Monaghan, C. Merino, Graph polynomials and their applications I: the Tutte polynomial,
     in: Structural Analysis of Complex Networks, Springer, 2011, pp. 219–255.
 [7] J.A. Ellis-Monaghan, I. Moﬀatt, Handbook of the Tutte Polynomial and Related Topics, CRC Press,
     2022.
 [8] L. Ferroni, Matroids are not Ehrhart positive, Adv. Math. 402 (2022) 108337.
 [9] L. Ferroni, B. Schröter, Valuative invariants for large classes of matroids, arXiv preprint arXiv:
     2208.04893, 2022.
[10] L. Ferroni, B. Schröter, The Merino–Welsh conjecture for split matroids, Ann. Comb. 27 (3) (2023)
     737–748.
[11] B. Jackson, An inequality for Tutte polynomials, Combinatorica 30 (2010) 69–81.
[12] F. Jaeger, D.L. Vertigan, D.J.A. Welsh, On the Computational Complexity of the Jones and Tutte
     Polynomials, Mathematical Proceedings of the Cambridge Philosophical Society, vol. 108, Cam-
     bridge University Press, 1990, pp. 35–53.
[13] K. Knauer, L. Martínez-Sandoval, J. Luis Ramírez Alfonsín, A Tutte polynomial inequality for
     lattice path matroids, Adv. Appl. Math. 94 (2018) 23–38.
[14] J.P.S. Kung, Inconsequential results on the Merino-Welsh conjecture for Tutte polynomials, arXiv
     preprint arXiv:2105.01825, 2021.
[15] F. Lin, A note on spanning trees and totally cyclic orientations of 3-connected graphs, J. Comb.
     4 (1) (2013) 95–104.
[16] C. Merino, M. Ibañez, G. Rodríguez, A note on some inequalities for the Tutte polynomial of a
     matroid, Electron. Notes Discrete Math. 34 (2009) 603–607.
[17] C. Merino, M. Ramírez-Ibáñez, G. Rodríguez-Sánchez, The Tutte polynomial of some matroids, Int.
     J. Comb. (2012) 2012.
[18] C. Merino, D. Welsh, Forests, colorings and acyclic orientations of the square lattice, Ann. Comb.
     3 (2–4) (1999) 417–429.
[19] S.D. Noble, G.F. Royle, The Merino–Welsh conjecture holds for series–parallel graphs, Eur. J. Comb.
     38 (2014) 24–35.
[20] J. Oxley, Matroid Theory, Oxford University Press, 1992.
[21] C. Thomassen, Spanning trees and orientations of graphs, J. Comb. 1 (2) (2010) 101–111.
[22] W.T. Tutte, A contribution to the theory of chromatic polynomials, Can. J. Math. 6 (1954) 80–91.
[23] D. Welsh, The Tutte polynomial, Random Struct. Algorithms 15 (3–4) (1999) 210–228.

