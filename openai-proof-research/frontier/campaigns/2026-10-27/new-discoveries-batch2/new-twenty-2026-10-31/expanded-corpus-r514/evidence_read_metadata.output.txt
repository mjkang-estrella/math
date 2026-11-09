          <td class="tablecell label">Comments:</td>
          <td class="tablecell arxivdoi">              <a href="https://doi.org/10.48550/arXiv.1205.4293"  id="arxiv-doi-link">https://doi.org/10.48550/arXiv.1205.4293</a><div class="button-and-tooltip">
      <h2>Submission history</h2> From: Brendon Rhoades [<a href="/show-email/180b413d/1205.4293" rel="nofollow">view email</a>]      <br/>            <strong><a href="/abs/1205.4293v1" rel="nofollow">[v1]</a></strong>
    <strong>[v2]</strong>
                                                                   EVIDENCE FOR PARKING CONJECTURES

                                                                                       BRENDON RHOADES


                                                   Abstract. Let W be an irreducible real reflection group. Armstrong, Reiner, and the author
                                                   presented a model for parking functions attached to W [2] and made three increasingly strong
                                                   conjectures about these objects. The author generalized these parking objects and conjectures to




arXiv:1504.06869v2 [math.CO] 15 May 2015
                                                   the Fuss-Catalan level of generality [26]. Even the weakest of these conjectures would uniformly
                                                   imply a collection of facts in Coxeter-Catalan theory which are at present understood only in a
                                                   case-by-case fashion. We prove that when W belongs to any of the infinite families ABCDI, the
                                                   strongest of these conjectures is generically true.




                                                                                        1. Introduction
                                              The purpose of this paper is to announce evidence supporting a family of conjectures appearing
                                           in [2] and [26] related to generalizations of parking functions from the symmetric group Sn to
                                           an irreducible real reflection group W . Our most important result is that the strongest of these
                                           conjectures holds generically whenever W is not of exceptional type. Let us give some background
                                           on and motivation for these conjectures, deferring precise statements of definitions and results to
                                           Section 2.
                                              A (classical) parking function of size n is a length n sequence (a1 , . . . , an ) of positive integers
                                           whose nondecreasing rearrangement (b1 ≤ · · · ≤ bn ) satisfies bi ≤ i for all 1 ≤ i ≤ n. The set
                                           Parkn of parking functions of size n carries a natural action of the symmetric group Sn given
                                           by w.(a1 , . . . , an ) := (aw(1) , . . . , aw(n) ) for w ∈ Sn and (a1 , . . . , an ) ∈ Parkn . Parking functions
                                           were introduced by Konheim and Weiss in computer science [18], but have received a great deal of
                                           attention in algebraic combinatorics [3, 12, 16].
                                              Parking functions have a natural Fuss generalization. Throughout this paper, we fix a choice
                                           k ∈ Z>0 of Fuss parameter. A (classical) Fuss parking function of size n is a length n sequence
                                           (a1 , . . . , an ) of positive integers whose nondecreasing rearrangement (b1 ≤ · · · ≤ bn ) satisfies bi ≤
                                           k(i − 1) + 1 for all 1 ≤ i ≤ n. The symmetric group Sn acts on the set Parkn (k) of Fuss parking
                                           functions by subscript permutation; when k = 1 one recovers Parkn (1) = Parkn .
                                              In [2], Armstrong, Reiner, and the author presented two generalizations, one algebraic and one
                                           combinatorial, of parking functions which are attached to any irreducible real reflection group W .
                                           Let h be the Coxeter number of W . The algebraic generalization Parkalg                W was defined as a certain
                                           quotient C[V ]/(Θ − x) of the coordinate ring C[V ] of the reflection representation V , where (Θ − x)
                                           is an inhomogeneous deformation of an ideal (Θ) ⊂ C[V ] arising from a homogeneous system of
                                           parameters Θ of degree h + 1 carrying V ∗ . The combinatorial generalization ParkN                 C
                                                                                                                                             W was defined
                                           using a certain W -analog of noncrossing set partitions [5, 24]. The combinatorial model ParkN                W
                                                                                                                                                           C

                                           is easier to visualize and has connections with W -noncrossing partitions, but the algebraic model
                                           Parkalg
                                                 W is easier to understand in a type-uniform fashion.
                                                                                                                                     alg
                                              The combinatorial parking space ParkN                C
                                                                                                 W and the algebraic space ParkW carry actions of not
                                           just the reflection group W , but also the product W × Zh of W with an order h cyclic group.
                                           Armstrong, Reiner, and the author made a sequence of conjectures (Weak, Intermediate, and
                                           Strong) of increasing strength about this action [2]. We refer to these collectively as the Main
                                           Conjecture.
                                             Key words and phrases. noncrossing partition, parking function, reflection group.
                                                                                                   1
2                                        BRENDON RHOADES

          type            k=1          k≥1              type            k=1            k≥1
         A1 , A2         Strong       Strong           A1 , A2         Strong         Strong
      An , n ≥ 3          Weak         Weak         An , n ≥ 3      Generic Strong Generic Strong
         Bn /Cn       Intermediate Intermediate        Bn /Cn       Generic Strong Generic Strong
           Dn         Intermediate Intermediate          Dn         Generic Strong Generic Strong
    I2 (m), m ≥ 5        Strong    Intermediate   I2 (m), m ≥ 5        Strong      Generic Strong
    F4 , H3 , H4 , E6     Weak         Open       F4 , H3 , H4 , E6     Weak           Open
         E7 , E8          Open         Open            E7 , E8          Open           Open

          Table 1. The strongest version of the Main Conjecture known in each type, before
          this paper (left) and after (right). Here k ≥ 1 is our Fuss parameter.


   The Weak Conjecture gives a character formula for the (permutation) action of W × Zh on the
combinatorial parking space ParkN     C
                                     W . The Intermediate and Strong Conjectures assert a strong
                           NC ∼ Θ
form of isomorphism ParkW = V between the combinatorial parking space and a “parking locus”
V Θ attached to the algebraic parking space Parkalg W . The Intermediate Conjecture asserts that this
isomorphism holds for one particular choice of the “parameter” Θ, whereas the Strong Conjecture
asserts that any choice of Θ would give our isomorphism. Even the Weak Conjecture uniformly
implies a collection of uniformly stated facts in Coxeter-Catalan theory which are at present only
understood in a case-by-case fashion (see Subsection 2.6 for a statement of these facts).
   This setup was extended to the Fuss setting in [26]. The k-W -combinatorial and algebraic
                                      alg                                        NC           NC
parking spaces ParkN    C
                       W (k) and ParkW (k) were defined and specialize as ParkW (1) = ParkW and
     alg           alg            NC              alg
ParkW (1) = ParkW . Both ParkW (k) and ParkW (k) carry actions of the product group W × Zkh .
The definition of Parkalg                                                           ∗
                        W (k) depends on a h.s.o.p. Θ of degree kh + 1 carrying V and to any such
h.s.o.p. Θ we have an associated parking locus V Θ (k). The Fuss analog of the Main Conjecture
(in its Weak, Intermediate, and Strong incarnations) is presented.
   The prior progress on Main Conjecture is presented on the left of Table 1. The assertions for
k = 1 are proven in [2] and the assertions for k ≥ 1 are proven in [26]. While these proofs are (of
course) case-by-case, uniform evidence for the Main Conjecture in any type W has been discovered
which identifies certain “components” of ParkN    C            Θ
                                                W (k) and V (k).
   Perhaps the most striking feature of the left of Table 1 is that only the Weak Conjecture is known
in type A whereas stronger forms are known for the other infinite families BCDI. That is, the state
of knowledge for the symmetric group is lacking relative to all other infinite families. The reason
for this is that relevant h.s.o.p.’s Θ in type A are harder to write down, making the parking loci
V Θ (k) attached to symmetric groups harder to access. This is a rare instance where the case of the
symmetric group is the most difficult among the real reflection groups! The first main contribution
of this paper will remedy this situation.
Theorem 1.1. The Intermediate Conjecture is true in type A for any Fuss parameter k ≥ 1.
   The basic idea in the proof of Theorem 1.1 is to pick an arbitrary h.s.o.p. Θ of degree kh + 1
carrying V ∗ such that the corresponding parking locus V Θ (k) is reduced. While V Θ (k) is hard to
understand explicitly, it can be understood indirectly by considering an augmented version of the
intersection lattice L attached to W which includes eigenspaces E(w, ξ) of elements w ∈ W for
eigenvalues ξ 6= 1.
   Our next contribution is yet another layer of the Main Conjecture which we term the Generic
Strong Conjecture. The four flavors of the Main Conjecture are related by
                        Strong ⇒ Generic Strong ⇒ Intermediate ⇒ Weak,
so that the Generic Strong version sits between the Strong and Intermediate versions.
                               EVIDENCE FOR PARKING CONJECTURES                                       3


   The Generic Strong Conjecture is easy to conceptualize. The Strong Conjecture states that
for any h.s.o.p. Θ of degree kh + 1 carrying V ∗ , we have our ‘strong isomorphism’ ParkN     C    ∼
                                                                                             W (k) =
V Θ (k). The Intermediate Conjecture asserts that there exists a choice of Θ so that our isomorphism
ParkN C     ∼ Θ
     W (k) = V (k) holds. The Generic Strong Conjecture states that for a generic choice of Θ
(understood in an appropriate Zariski sense), we have ParkN    C    ∼ Θ
                                                              W (k) = V (k). While these are three
a priori distinct conditions, we will prove the following statement uniformly.

Theorem 1.2. The Intermediate and Generic Strong Conjectures are equivalent for any reflection
group W and any Fuss parameter k ≥ 1.

   The current status of the Main Conjecture is summarized on the right of Table 1. The entries
come from combining Theorems 1.1 and 1.2. Our proof of Theorem 1.2 will also show that the
only obstacle to proving the Strong Conjecture given the Intermediate Conjecture is the proof of a
purely algebraic statement having nothing to do with the combinatorics of noncrossing partitions.
Namely, one would only need to show that for any h.s.o.p. Θ of degree kh + 1 carrying V ∗ , the
parking locus V Θ (k) is reduced. This gives significant evidence for the Strong Conjecture itself.
   The proof of Theorem 1.2 is uniform, but not combinatorial. One uses topological and ana-
lytic arguments to show that a certain collection of “good” h.s.o.p.’s Θ can be identified with a
nonempty Zariski open subset U of the affine space HomC[W ] (V ∗ , C[V ]kh+1 ) which parametrizes
all W -equivariant polynomial functions Θ : V → V which are homogenous of degree kh + 1. As
a Zariski open subspace of an affine complex space, the set U is path connected in its Euclidean
topology. For any path γ : [0, 1] → U sending t to Θt , one gets a parking locus V Θt (k) for all
0 ≤ t ≤ 1. A continuity argument shows that one may “follow group actions along paths” to
identify the W × Zkh -set structures of these parking loci as t varies.
   The remainder of this paper is structured as follows. In Section 2 we review material on
reflection groups and Coxeter-Catalan Theory, recall the main constructions of [2, 26], and state
the four flavors of the Main Conjecture. In Section 3 we present a simple tool (Lemma 3.1) for
proving equivariant bijections of G-sets for any group G and give uniform enumerative and algebraic
results regarding the actions of W × Zkh on ParkN    C          Θ
                                                   W (k) and V (k). In Section 4 we specialize to
type A and study the action of Sn × Zkn on ParkN      C
                                                    Sn (k). Using the theory developed in Section 3,
this will allow us to prove Theorem 1.1. We return to general type W in Section 5 with a proof
of Theorem 1.2. In particular, all of the arguments appearing in this paper are type A or uniform,
and the only type A arguments appear in Section 4.


                                          2. Background
2.1. Notation for group actions. Let G be a finite group and let S and T be finite G-sets.
We write S ∼  =G T to mean that there is a G-equivariant bijection ϕ : S → T . If V and W
are finite-dimensional C[G]-modules, we write V ∼  =C[G] W to mean that there is a G-equivariant
linear isomorphism ϕ : V → W . If S and T are finite G-sets, we have that S ∼     =G T implies
C[S] ∼=C[G] C[T ], but the converse does not hold in general.

2.2. Reflection groups. Let W be a reflection group acting on its reflection representation V . In
this paper, all reflection groups will be real and irreducible. It will be convenient to replace V with
its complexification VC = C ⊗R V and regard V as a complex vector space. We let n := dim(V ) be
the rank of W .
   Let Φ ⊂ V denote a root system associated to V and let Φ+ ⊂ Φ be a choice of positive system
within Φ. Let Π ⊆ Φ+ be the corresponding choice of simple system. For any α ∈ Φ, let Hα ⊂ V
denote the orthogonal hyperplane Hα := {v ∈ V : hv, αi = 0}. The hyperplane arrangement
Cox(W ) := {Hα : α ∈ Φ+ } is called the Coxeter arrangement of W .
4                                            BRENDON RHOADES


   For any α ∈ Φ+ , let tα ∈ W denote the orthogonal reflection through the hyperplane Hα . The
set S := {tα : α ∈ Π} of simple reflections generates W and turns the pair (W, S) into a Coxeter
system. Let T = {tα : α ∈ Φ+ } denote the set of all reflections in W , simple or otherwise.
   If S = {s1 , s2 , . . . , sn }, a Coxeter element in W is a W -conjugate of the product s1 s2 · · · sn (where
the simple reflections are taken in some order). It can be shown that any two Coxeter elements
in W are conjugate. We fix a choice of Coxeter element c ∈ W . We let h denote the order of the
group element c ∈ W ; the number h is the Coxeter number of W and is independent of our choice
of c.

Example 2.1. In type An−1 , we may identify W with the symmetric group Sn . The reflection
representation V is the (n − 1)-dimensional quotient V = Cn /h(1, 1, . . . , 1)i of the defining action
of Sn on Cn by the copy of the trivial representation given by constant vectors in Cn .
    If ei denotes the image in V of the ith coordinate vector in Cn , the root system Φ is given
by Φ = {ei − ej : 1 ≤ i 6= j ≤ n} ⊂ V . The standard choice of positive system Φ+ ⊂ Φ is
Φ+ = {ei − ej : 1 ≤ i < j ≤ n}. The corresponding simple system is Π = {ei − ei+1 : 1 ≤ i ≤
n − 1}. The Coxeter arrangement Cox(Sn ) is the image in V of the standard braid arrangement
{xi − xj = 0 : 1 ≤ i < j ≤ n} in Cn , where xi is the ith standard coordinate function.
    The reflection tαi,j ∈ Sn corresponding to a given positive root αi,j = ei − ej is the transposition
(i, j) ∈ Sn . We get that S = {(i, i + 1) : 1 ≤ i ≤ n − 1} and T = {(i, j) : 1 ≤ i < j ≤ n}. The
usual choice of Coxeter element is c = (1, 2)(3, 4) · · · (n − 1, n) = (1, 2, . . . , n) ∈ Sn . The Coxeter
number is h = n.

2.3. The algebraic parking space and parking loci. Let k ∈ Z>0 be a fixed choice of Fuss
parameter and let Zkh denote the cyclic group of order kh. We let g ∈ Zkh be a fixed choice of
                                      2πi
distinguished generator and let ζ = e kh ∈ C be a primitive khth root of unity.
   Let C[V ] denote the coordinate ring of polynomial functions V −→ C. If we fix a basis x1 , . . . , xn
of the dual vector space V ∗ = HomC (V,L C), we may identify C[V ] = C[x1 , . . . , xn ]. The ring C[V ] has
a natural polynomial grading C[V ] = d≥0 C[V ]d , so that C[V ]d can be thought of as polynomial
functions V −→ C of homogeneous degree d. We consider the graded W × Zkh -module on C[V ]
given as follows. The group W acts by linear substitutions. That is, we have (w.f )(v) := f (w−1 .v).
The distinguished generator g of the cyclic group Zkh scales by ζ d in homogeneous degree d.
   For a positive integer d, a homogeneous system of parameters (h.s.o.p.) of degree d carrying
  ∗
V is a sequence of polynomials θ1 , . . . , θn ∈ C[V ] (where n = dim(V ) is the rank) such that the
following conditions hold.

      • We have that θ1 , . . . , θn ∈ C[V ]d , i.e., the θi are homogeneous of degree d,
      • The zero locus cut out by θ1 = · · · = θn = 0 consists only of the origin {0}. Equivalently,
        the C-vector space C[V ]/(Θ) := C[V ]/(θ1 , θ2 , . . . , θn ) is finite-dimensional.
      • The C-linear span spanC {θ1 , . . . , θn } is stable under the action of W .
      • The C-linear span spanC {θ1 , . . . , θn } is isomorphic to V ∗ as a C[W ]-module.

   In this paper we will be interested in h.s.o.p.’s of degree d = kh + 1 carrying V ∗ . These are
uniformly known to exist by deep and subtle results from the theory of rational Cherednik algebras.
In fact, Cherednik algebras can be used to produce an h.s.o.p. Θ of degree kh + 1 carrying V ∗
which is unique up to scaling.
   More precisely, for any vector v ∈ V there is a certain differential operator Dv : C[V ] → C[V ]
called a Dunkl operator (see [2, Appendix] for its definition). If follows from Gordon’s work on
Cherednik algebras that there exists a W -equivariant linear map Θ : V ∗ ,→ C[V ]kh+1 whose image
is annihilated by all the Dunkl operators {Dv : v ∈ V } [13, 14]. Griffeth [15, Theorem 7.1]
                                    EVIDENCE FOR PARKING CONJECTURES                                                 5


proved that the map Θ is unique up to a nonzero scalar. 1 If x1 , . . . , xn is any basis of V ∗ , then
Θ(x1 ), . . . , Θ(xn ) gives a h.s.o.p. of degree kh + 1 carrying V ∗ .
   We make no explicit use of Cherednik algebras in this paper, taking the existence of our h.s.o.p.’s
as uniformly granted. We will refer to h.s.o.p.’s as in the above paragraph as “coming from Chered-
nik algebras”.
   Observe that in the above situation of degree d = kh + 1, the ideal (Θ) ⊂ C[V ] is stable under
the action of W × Zkh , so that the quotient C[V ]/(Θ) has the structure of a W × Zkh -module.
Bessis and Reiner [4] proved that the character χ : W × Zkh → C of the representation C[V ]/(Θ)
is given by the formula
                                                                          d
(2.1)                                     χ(w, g d ) = (kh + 1)multw (ζ )
Here multw (ζ d ) denotes the multiplicity of ζ d as an eigenvalue in the action of w on V .
   If θ1 , . . . , θn ∈ C[V ] form a h.s.o.p. of degree kh + 1 carrying V ∗ , there exists an ordered basis
x1 , . . . , xn of V ∗ such that the linear map induced by the assignment xi 7→ θi is W -equivariant. The
idea of an algebraic parking space comes from the inhomogeneous deformation given by replacing
the ideal (θ1 , . . . , θn ) with the ideal (θ1 − x1 , . . . , θn − xn ). The following definition appears in [2]
when k = 1 and [26] for general k.
Definition 2.2. Let θ1 , . . . , θn be a h.s.o.p. of degree kh + 1 carrying V ∗ . Fix an ordered basis
x1 , x2 , . . . , xn of V ∗ such that the linear map induced by xi 7→ θi is W -equivariant.
   The parking locus is the subscheme V Θ (k) of V cut out by the ideal
(2.2)                             (Θ − x) := (θ1 − x1 , . . . , θn − xn ) ⊂ C[V ].
The k-W -algebraic parking space Parkalg
                                     W (k) is the associated quotient representation of W × Zkh
given by
(2.3)                                     Parkalg
                                              W (k) := C[V ]/(Θ − x).

   In [2, Proposition 2.11] it is shown that we have a module isomorphism
(2.4)                         C[V ]/(Θ) ∼                               alg
                                        =C[W ×Zkh ] C[V ]/(Θ − x) = ParkW (k),
so that our neither our choice of Θ nor our ideal deformation affect module structure. 2 As a
result, the character W × Zkh → C of the algebraic parking space Parkalg      W (k) is also given by the
Equation 2.1.
   Parking loci will be most important for us when the deformed ideal (Θ − x) is reduced. In this
case, the parking locus V Θ (k) is a set V Θ (k) ⊂ V and may be identified with the set of fixed
points of the map Θ : V −→ V which sends a point with coordinates (x1 , . . . , xn ) to a point with
coordinates (θ1 , . . . , θn ). This fixed point perspective explains the superscript notation in V Θ (k).
The set V Θ (k) carries a permutation action of W × Zkh , where W acts by linear substitutions and
the distinguished generator g ∈ Zkh scales by ζ.
   If the parking locus V Θ (k) is reduced, we get a canonical identification V Θ (k) ∼       =C[W ×Zkh ]
     alg    3                                     Θ
ParkW (k). Therefore, the W × Zkh -set V (k) has permutation character given by Equation 2.1.
In particular, the parking locus V Θ (k) contains (kh + 1)n points. The following result of Etingof
shows that there exists a choice of Θ such that V Θ (k) is reduced.

   1The case of the symmetric group S = G(1,
TERM reducedness [24125, 79132, 87870, 88491, 89464, 99241]
TERM non-reduced []
TERM counterexample []
TERM h.s.o.p. [8732, 8787, 9701, 10176, 11050, 12273, 12573, 18056, 18723, 18934, 19651, 19784, 19834, 20504, 20966, 23722, 25596, 26333, 26639, 27364, 27944, 28083, 28152, 40931, 40983]
TERM Theorem 1.2. [11706, 13962, 93275, 93961]
