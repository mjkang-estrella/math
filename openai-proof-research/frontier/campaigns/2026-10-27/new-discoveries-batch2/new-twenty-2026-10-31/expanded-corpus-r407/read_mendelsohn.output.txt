                                            DISTRIBUTIVE MENDELSOHN TRIPLE SYSTEMS AND
                                                       THE EISENSTEIN INTEGERS




arXiv:1908.04966v1 [math.CO] 14 Aug 2019
                                                                           ALEX W. NOWAK

                                                                       Department of Mathematics
                                                                         Iowa State University
                                                                       Ames, Iowa 50011, U.S.A.

                                                   Abstract. We define a Mendelsohn triple system (MTS) with self-
                                                   distributive quasigroup multiplication and order coprime with 3 to be
                                                   distributive, non-ramified (DNR). We classify, up to isomorphism, all
                                                   DNR MTS and enumerate isomorphism classes (extending the work of
                                                   Donovan, Griggs, McCourt, Opršal, and Stanovský). The classification
                                                   is accomplished via the representation theory of the Eisenstein integers,
                                                   Z[ζ] = Z[X]/(X 2 − X + 1). Containing the class of DNR MTS is that
                                                   of MTS with an entropic (linear over an abelian group) quasigroup op-
                                                   eration. Partial results on the classification of entropic MTS with order
                                                   divisible by 3 are given, and a complete classification is conjectured. We
                                                   also prove that for any entropic MTS, the qualities of being non-ramified,
                                                   pure, and self-orthogonal are equivalent. We introduce the varieties RE
                                                   and LE of (resp. right and left) Eisenstein quasigroups, whose respective
                                                   linear representation theories correspond to the alternative presentation
                                                   Z[X]/(X 2 + X + 1) of the Eisenstein integers.




                                                                            1. Introduction
                                             The left self-distributive (LD) rule
                                           (1.1)                             x(yz) = (xy)(xz)
                                           is a well-studied phenomenon appearing in the theory of knots [21], Hopf al-
                                           gebras [1], symmetric spaces [27], term rewriting systems [10, Ch. V], quasi-
                                           groups [35], and combinatorial designs [13]. The results of this paper lie at
                                           the intersection of the latter two subjects, and what is more, bring algebraic
                                           number theory into the fold of disciplines connected by self-distributivity.
                                              E-mail address: anowak@iastate.edu.
                                              2010 Mathematics Subject Classification. 20N05, 05B07.
                                              Key words and phrases. quasigroup, Mendelsohn triple system, distributive, Eisen-
                                           stein integers, Moufang loop, congruence subgroup, orthogonal Latin square.
                                                                                       1
2                               A. W. NOWAK

  In varieties (we use variety in the universal algebraic sense: a class of
algebras defined by identities) of idempotent algebras, wherein

(1.2)                              x2 = x
holds, (1.1) follows from the entropic (sometimes referred to as medial )
identity

(1.3)                       (xy)(zu) = (xz)(yu).
The right self-distributive (RD) law
(1.4)                         (yz)x = (yx)(zx)
also follows from (1.2) and (1.3). Quasigroups in which both (1.1) and
(1.4) hold are referred to as distributive quasigroups. Idempotent, entropic
quasigroups are distributive. We shall concern ourselves with distributivity
in the variety of Mendelsohn quasigroups. Mendelsohn quasigroups realize
Mendelsohn triple systems as algebraic objects. The variety is specified by,
in addition to quasigroup axioms (v.i. Section 2.1), idempotence (1.2) and
the semisymmetric identity

(1.5)                            y(xy) = x.
A Mendelsohn quasigroup is left distributive if and only if it is right dis-
tributive, and an entropic Mendelsohn quasigroup is distributive.
   Distributive quasigroups admit linear representations over (in general,
nonassociative) commutative Moufang loops (v.i. Definition 2.4), while en-
tropic quasigroups are linear over abelian groups. Section 2 is, in part,
devoted to fleshing out the details of linear quasigroup theory. A result
due to Fischer [14], Galkin [15], and Smith [32] (reproduced below as The-
orem 2.10) breaks up the study of finite, distributive quasigroups into two
cases: those which are linear over abelian groups of prime power order (the
entropic case), and those which are linear over commutative Moufang loops
of order 3n for n ≥ 4 (distributive, nonentropic). This result allows us
to restrict our attention to abelian groups, and, in turn, to the realm of
entropic quasigroups, and yet still obtain a classification of all distributive
Mendelsohn quasigroups of order coprime to 3. This, our main result is a
direct product decomposition theorem. A (due to the absence of certain
technicalities, slightly weaker) statement of this theorem is the following:
Theorem. Every distributive Mendelsohn triple system of order coprime
with 3 is isomorphic to a direct product of systems defined on abelian groups
of the form (Z/pn )i , for i ∈ {1, 2}.
                    MTS AND THE EISENSTEIN INTEGERS                           3

   Entropic, Mendelsohn quasigroups are “essentially” –in a precise, cate-
gorical sense (v.i. Theorem 2.15)– the same as finite modules over the Eisen-
stein
   √ integers, the Euclidean domain consisting of the integral elements of
Q( −3). Section 2 surveys the algebraic structure of the Eisenstein in-
tegers. In Section 3, we will have enough context to explain our dubbing
distributive MTS of order not divisible by 3 distributive, non-ramified. We
then go on to exploit Eisenstein module structure (that of modules over a
PID) to obtain the aforementioned main result and enumerate the isomor-
phism classes described by this theorem. Section 4 presents progress on, and
complications related to, the case of 3-divisibility. In section 5, we further
leverage our direct product theorems to better understand combinatorial
properties (purity, self-orthogonality, self-conversity) in distributive MTS.
We obtain the following characterization of DNR MTS:
Theorem. An entropic Mendelsohn triple system has order coprime with 3
if and only if it is pure if and only if it is self-converse (orthogonal to its
converse).
Section 6 concludes the paper by considering varieties of quasigroups that
correspond to an alternative presentation for the Eisenstein integers.

                              2. Background
2.1. Quasigroups and Mendelsohn triple systems. A quasigroup
(Q, ·, /, \) is a (potentially empty) set Q equipped with three binary oper-
ations: · denoting multiplication, / right division, and \ left division; these
operations satisfy the identities
(2.1)                           y\(y · x) = x;

(2.2)                           y · (y\x) = x;

(2.3)                           (x · y)/y = x;

(2.4)                           (x/y) · y = x.
A homomorphism between quasigroups is a function that respects multi-
plication and the two divisions. These homomorphisms furnish a category
Q.
Remark 2.1. When appropriate, we convey multiplication of quasigroup
elements by concatenation, and in some instances, use both · and concate-
nation, our convention being that concatenation takes precedence over ·.
For example, xy · z ≡ (xy)z ≡ (x · y) · z.
4                               A. W. NOWAK

   The variety of Mendelsohn quasigroups, denoted MTS, is generated by
(1.2), (1.5), and (2.1)-(2.4). The homomorphisms between the objects in
this variety form a category, which we also denote by MTS.
   A finite Mendelsohn quasigroup Q gives rise to a Mendelsohn triple sys-
tem (Q, B), where B is a collection of blocks, or cyclic triples of points
from Q, satisfying the property that for any ordered pair of distinct points
(x, y) ∈ Q2 \ Q,b there is a unique block (x y xy) ≡ (xy x y) ≡ (y xy x) ∈ B.
Conversely, any Mendelsohn triple system (Q, B) corresponds to a finite
Mendelsohn quasigroup on Q: let x2 = x for any x ∈ Q, and xy be the ele-
ment in the block containing (x, y) when x 6= y (cf. [24, Th. 1]). Divisions
in the Mendelsohn quasigroup are given by the opposite of multiplication:
x/y = x\y = yx. That is, every Mendelsohn quasigroup takes the form
(Q, ·, ◦, ◦), where x ◦ y = y · x.
Remark 2.2. As the preceding lines indicate, Mendelsohn triple systems
are conventionally restricted to nonempty, finite point sets of cardinality
greater than 1. However, both the empty set and the trivial quasigroup
(containing one element) are Mendelsohn quasigroups. Moreover, there are
infinite Mendelsohn quasigroups; take C under the multiplication

                           xy = xeπi/3 + ye−πi/3 .
We do not directly deal with any infinite Mendelsohn quasigroups in this
paper, and the empty and trivial quasigroups are, as Mendelsohn quasi-
groups, classified, so in order to employ the convenient acronym MTS, we
will use the terms Mendelsohn quasigroup and Mendelsohn triple system in-
terchangeably. Any reference to isomorphism of MTS should be understood
as an appeal to the quasigroup structure.
2.2. Linearity and distributivity in quasigroups. This section recasts
[13, Sec. 1-2.1]. In the course of exposition, we will demonstrate the con-
nection between linearity, entropicity, and distributivity in quasigroups.
Remark 2.3. Throughout the paper, arguments will appear to the left of
their functions. For example, the image of a point x under the function f is
written xf, or even as xf . Exponentiation of an argument by its function can
help to curb the proliferation of brackets to which works in nonassociative
algebra are susceptible.
   Let (M, +, /, \, 0) be a loop –a quasigroup with a multiplicative identity–
where 0 denotes the neutral element. Assume, furthermore, that the multi-
plication is commutative. If, for all x, y, z ∈ M,
(2.5)              (x + x) + (y + z) = (x + y) + (x + z),
                    MTS AND THE EISENSTEIN INTEGERS                         5

then (M, +, /, \, 0) is a commutative Moufang loop (CML). The nucleus of
a CML M,

         N(M) = {x ∈ M | ∀y, z ∈ M (x + y) + z = x + (y + z)},

is the set of elements that associate with all of M. An automorphism R
of a CML M is nuclear if {x + xR | x ∈ M} ⊆ N(M). Notice that any
abelian group is a CML, and any CML-automorphism is also an abelian
group automorphism, and is therefore nuclear.
   Let ⊤ denote the trivial quasigroup, containing a single element. A quasi-
group Q with a pointed idempotent selected by a Q-morphism ⊤ → Q is a
pique, short for pointed, idempotent quasigroup.

Definition 2.4. Let (M, +) be a commutative Moufang loop. Fix nuclear
CML-automorphisms R, L ∈ Aut(M). The operation

(2.6)                          xy = xR + yL

endows M with the structure of a quasigroup, Lin(M, R, L). Moreover, the
map ⊤ → Lin(M, R, L) selecting 0 ∈ M gives Lin(M, R, L) the structure of
a pique, which is referred to as a CML-linear pique on (M, +). If (M, +) is
an abelian group, then we simply say that Lin(M, R, L) is a linear pique on
(M, +).

Remark 2.5. (a) We adopt the convention that Lin(M, R) denotes a CML-
linear pique in which L = 1 − R. This is because a CML-linear pique is
idempotent if and only if L = 1 − R, and, until Section 6, we are concerned
only with Mendelsohn quasigroups.
  (b) When referring to a linear pique Lin(M, R) that is Mendelsohn, we
will often employ the phrase linear MTS.
   (c) Readers familiar with the quasigroup literature may notice that we
have avoided the term affine quasigroup, one more frequently used to de-
scribe the structures of Definition 2.4. However, since our work deals en-
tirely with pointed structures, we felt it best to avoid the term affine and
any origin-free geometric connotations that go along with it.

   Any CML-linear pique of the form Lin(M, R) is idempotent and distribu-
tive. The Belousov theorem (v.i. Th. 2.9) establishes the converse for
nonempty quasigroups.
   What are the conditions necessary for a CML-linear pique Lin(M, R) to
be Mendelsohn? Well, as we have already noted in Remark 2.5(b), such a
structure is automatically idempotent. Furthermore, semisymmetry (1.5)
6                                 A. W. NOWAK

forces
                      xy · x = xR2 + yR − yR2 + x − xR
                             = y,
and setting y = 0 reveals R2 − R + 1 = 0. Conversely, any CML M
with nuclear automorphism R satisfying R2 − R + 1 = 0, or, equivalently,
1−R = R−1 furnishes an idempotent, semisymmetric quasigroup Lin(M, R)
(cf.[13, Prop. 2.2]).
Remark 2.6. Sade appears to be the first to have recognized the identity
X 2 − X + 1 in relation to the construction of semisymmetric, idempotent
quasigroups [31]. In Mendelsohn’s presentation of his eponymous triple sys-
tems, he used roots of this quadratic over finite fields to prove the existence
of simple systems (i.e., MTS with no subsystems), and systems with no
“repeated blocks” (v.i. pure MTS in Section 5.1) [24, Ths. 6, 7].
Example 2.7. Since X 2 − X + 1 ≡ X 2 + X + 1 splits in GF(22 ), we can
choose a root ζ, and define a Mendelsohn quasigroup Lin(GF(22 ), ζ) via
                              xy = xζ + y(1 − ζ).
An equivalent matrix characterization of this linear MTS is afforded by
Lin((Z/2 )2 , T ), where
                                       
                                    0 1
                           T =            .
                                    1 1
   We review some fundamental results on the classification of entropic and
distributive quasigroups. With them, we will be able to clearly state the
classification program initiated by Donovan et. al.
Theorem 2.8 (Bruck-Murdoch-Toyoda [4], [26], [36]). A nonempty quasi-
group (M, ·) is entropic if and only if there is an abelian group (M, +)
affording a linear pique representation Lin(M, R, L) of the multiplication ·,
and RL = LR.
Theorem 2.9 (Belousov [2]). A nonempty quasigroup (M, ·) is distribu-
tive if and only there is a commutative Moufang loop (M, +) affording a
(idempotent) linear pique representation Lin(M, R) of the multiplication ·.
Theorem 2.10 (Fischer-Galkin-Smith [14], [15], [32]). Let n = pr11 · · · prkk ,
where the p1 , . . . , pk represent pairwise distinct primes. Suppose Q is a
distributive quasigroup of order n. Then Q is isomorphic to a direct product
of distributive quasigroups Q1 × · · · × Qk so that |Qi | = pri i . Moreover, if Qi
is not a linear pique, then pi = 3, ri ≥ 4, and it is CML-linear.
                    MTS AND THE EISENSTEIN INTEGERS                          7

Remark 2.11. By Theorems 2.8 and 2.9, the reader should regard the
phrases “Mendelsohn linear pique,” “linear MTS,” and “nonempty, entropic
Mendelsohn quasigroup” as synonyms.
   In conjunction with the Chinese Remainder Theorem, Theorems 2.9 and
2.10 tell us that in order to classify distributive Mendelsohn triple sys-
tems of arbitrary order, it is enough to classify semisymmetric, idempotent
linear piques on abelian groups of prime power order and semisymmstric,
idempotent CML-linear piques over CML of exponent 3, with the former
class comprising all entropic MTS. The following theorem [22] of Kepka and
Němec characterizes isomorphisms of idempotent CML-linear piques.
Theorem 2.12 (Kepka-Němec [22]). Let M1 and M2 be commutative Mo-
ufang loops, and suppose R1 is a nuclear automorphism of M1 and R2 a
nuclear automorphism of M2 such that 1−R1 and 1−R2 are automorphisms
of M1 and M2 , respectively. Then Lin(M1 , R1 ) ∼
                                                = Lin(M2 , R2 ) if and only
if there is a loop isomorphism ψ : M1 → M2 such that ψ −1 R1 ψ = R2 .
Example 2.13. Both 3 and 5 are roots of X 2 − X + 1 mod 7. Thus,
right multiplications by these field elements yield linear MTS structures
Lin(Z/7 , 3), Lin(Z/7 , 3). Because Aut(Z/7 ) ∼
                                              = C6 is commutative, Theorem
2.12 tells us Lin(Z/7 , 3) ≇ Lin(Z/7 , 5).
   Now, we may understand the classification problem as determining the
conjugacy classes of CML automorphisms (for abelian groups of prime power
order and nonassociative CML of exponent 3) which are annihilated by
X 2 − X + 1.
   In [13], the authors classify distributive Mendelsohn quasigroups of orders
p and p2 , for any prime p. They also enumerate, using GAP [16], isomor-
phism classes for prime powers less than 1000. The following theorem is the
key to our improvement of these results. We employ the the presentation
Z[X]/(X 2 − X + 1) for the  √
                                Eisenstein integers. We denote them by Z[ζ],
               πi/3   1       3
where ζ = e         = 2 + 2 i. Algebraically, they may be specified as the
rank-2 free abelian group with basis {1, ζ}, inheriting Z-algebra structure
from complex multiplication.
   As a final matter of notation for the upcoming theorem, let us establish
that for a category with finite products V, we have Z ⊗ V standing for
the subcategory of abelian group objects in V. Whenever V is a variety of
quasigroups, the category Z ⊗ V is precisely the class of (homomorphisms
between) linear piques in V (cf. [33, Th. 10.4]).
8                                A. W. NOWAK

Lemma 2.14. Let S be a nonzero (not necessarily commutative), unital
ring, f (X) = X 2 − X + 1 ∈ S[X], and ζ ∈ S be a root of f (X).
    (a) The root ζ is a unit in S, and its inverse is also a root of f (X).
    (b) The identity ζ = ζ −1 holds if and only if S is a ring of characteristic
        3, and in this case, ζ = −1.
Proof. (a) Note f (ζ) = 0 demands ζ(1 − ζ) = 1. Thus, f (ζ −1) = f (1 − ζ) =
(1 − ζ)2 − 1 + ζ + 1 = 1 − 2ζ + ζ 2 + ζ = 1 − ζ + ζ 2 = f (ζ) = 0.
(b) If ζ = ζ −1 = 1−ζ, then 1 = 2ζ. This clearly cannot be if char(S) = 2,
so proceed assuming 2 6= 0, and ζ −1 = 2 = ζ. Then 22 −2+1 = 0, equivalent
to 3 = 0. Conversely, if char(S) = 3, then f (X) = (X + 1)2 .           
Theorem 2.15. Let Z ⊗ MTS denote the category of linear MTS, and
Z[ζ]-Mod that of modules over the Eisenstein integers. There is a faithful,
dense functor
                     F : Z[ζ]-Mod → Z ⊗ MTS.
Proof. Note that a Z[ζ]-module is specified by a pair (M, R), where M is an
abelian group, and R, an automorphism of M annihilated by the polynomial
X 2 − X + 1, represents the action of ζ. That R is an automorphism follows
from Lemma 2.14 applied to S = End(M). This observation permits a map
F : (M, R) 7→ Lin(M, R) between objects. If we can show that every Z[ζ]-
module homomorphism is a homomorphism of quasigroups, then F : f 7→ f
is a faithful, functorial correspondence between morphisms. Indeed, given
a module homomorphism f : (M, R) → (N, T ), we find (xR)f = (xζ )f =
(xf )ζ = (xf )T . Thus,


                        (xy)f = (xR + y(1 − R))f
                               = (xR)f + yf − (yR)f
                               = (xf )T + yf − (yf )T
                               = (xf )T + (yf )(1 − T )
                               = (xf )(yf ).
Now, if Lin(M, R) is Mendelsohn, then (M, R) is a Z[ζ]-module. This con-
firms the density of F .                                              

2.3. The Eisenstein integers. The goal of this section is to recall some
basic structure of the Eisenstein integers.
Remark 2.16. In most of the number theory literature, (cf. [17, 19], for
example) the Eisenstein integers are presented as Z[ω] = Z[X]/(X 2 +X +1),
                      MTS AND THE EISENSTEIN INTEGERS                              9

using {1, e2πi/3 } as an integral basis. However, the map
                       √              √ !                √
                   1     3        1      3         −1      3
(2.7)                +     i 7→     +      i −1=       +     i
                   2    2         2     2           2     2

is a ring isomorphism mapping Z[eπi/3 ] onto Z[e2πi/3 ].
  The Eisenstein integers have a faithful representation in M2 (Z) given by

                                                          
                                                0 −1
(2.8)                           ζ 7→                           ,
                                                1 1
and thus may be viewed as the Z-algebra of integral matrices of the form

                                                                      
                      a 0               0 −b                       a −b
(2.9)                           +                      =                       .
                      0 a               b b                        b a+b
In fact,
                                                          
                                            a −b
(2.10)         (a + bζ)N := det                                = a2 + ab + b2
                                            b a+b
gives Z[ζ] the structure of a Euclidean domain [19, Prop. 1.4.2]. Notice,
then, that Z[ζ] is a PID, ensuring complete decomposability of any finitely
generated module into a direct sum of cyclic modules:
Theorem 2.17. Let (M, R) be a finitely generated Z[ζ]-module. Then there
is a finite sequence of prime powers (which may include 0) π1n1 , . . . , πlnl ∈
Z[ζ] so that

                                        l
                                        M
(2.11)                   (M, R) ∼
                                =               (Z[ζ]/(πini ), Ri )
                                         i=1

where each Ri is an abelian group automorphism on Z[ζ]/(πini ).
Corollary 2.18. Let M be a finite abelian group, and Lin(M, R) a linear
MTS. Then there is a finite sequence of prime powers π1n1 , . . . , πlnl ∈ Z[ζ] so
that
                                        l
                                        Y
(2.12)                Lin(M, R) ∼
                                =               Lin (Z[ζ]/(πini ), Ri ) ,
                                        i=1

where each Ri is an abelian group automorphism on Z[ζ]/(πini ).
10                                   A. W. NOWAK

Proof. The arbitrary linear MTS Lin(M, R) is the image of the finite Z[ζ]-
module (M, R) under the functor F of Theorem 2.15. Since F : f 7→ f
injects morphisms, the isomorphism
                                      l
                                      M
                         (M, R) ∼
                                =            (Z[ζ]/(πini ), Ri )
                                       i=1

translates to a quasigroup isomorphism of the form (2.12), and we may,
without regard to potential (co)continuity issues associated with F , conflate
direct sum in one category with direct product in another since our indices
are finite.                                                                 

   Because the functor of Theorem 2.15 is not an equivalence, there is not
necessarily a one-to-one correspondence between subquasigroups of a linear
MTS and its Z[ζ]-submodules. The following corollary, therefore, should
not be read as a complete characterization of the subquasigroup lattice of
a linear MTS.
Corollary 2.19. Let M be a finite abelian group, and Lin(M, R) a linear
MTS with direct product decomposition
                                      l
                                      Y
                    Lin(M, R) ∼
                              =             Lin (Z[ζ]/(πini ), Ri ) .
                                      i=1

Each factor Lin(Z[ζ]/(πini ), Ri ) (and by the universal property of the direct
product, Lin(M, R) itself ) contains a chain of subquasigroups corresponding
to the ideal lattice
                                        
(2.13) (0 + (πini )) ≤ πini −1 + (πini ) ≤ · · · ≤ (πi + (πini )) ≤ (1 + (πini ))
of the quotient ring Z[ζ]/(πini ).
Proof. Let (M, R) be a Z[ζ]-module with submodule (M ′ , R′ ). It suffices
to show that Lin(M ′ , R′ ) is a subquasigroup of Lin(M, R). This follows
immediately from Theorem 2.15, for the Z[ζ]-module inclusion M ′ ֒→ M
specifying M ′ as a submodule is an injective quasigroup homomorphism
under F.                                                                

  The group of units of the Eisenstein integers, Z[ζ]× = {±1, ±ζ, ±ζ},
consists of the sixth roots of unity in C× . Primes in Z[ζ] belong to, up to
association by units, three pairwise disjoint classes [19, Prop. 9.1.4]:
     (1) π, where πN ≡ 1 mod 3 is prime in Z;
     (2) p, where p is prime in Z, and p ≡ 2 mod 3;
     (3) 1 + ζ.
                     MTS AND THE EISENSTEIN INTEGERS                          11

Do note that none of the primes in class (1) are rational, i.e., equal to p + 0ζ
for some p ∈ Z. The second class, however, does consist entirely of rational
prime representatives.
2.3.1. Quotients of Z[ζ]. The classification of linear Mendelsohn triple sys-
tems depends upon the nature of the quotients presented by (2.11). Our
discussion is taken from [5, 25], and our proofs are abridged adaptations
these authors’ results. Note that in these works, the cubic root of unity
ω = e2πi/3 is the preferred algebra generator.
  For an arbitrary commutative, unital ring S, we may define
                         S[ζ] = S[X]/(X 2 − X + 1).
One may consider this S-algebra as the subalgebra of M2 (S) consisting of
matrices of the form (2.9).
  Before classifying quotients of Z[ζ] by primary ideals, we collect some
lemmas on more general Eisenstein quotients and the nature of irrational
Eisenstein primes.
Lemma 2.20. Let a+bζ ∈ Z[ζ], so that gcd(a, b) = 1. Fix k = (a+bζ)N =
a2 + ab + b2 . Then Z[ζ]/(a + bζ) ∼
                                  = Z/k .
Proof. Because gcd(a, b) = 1, b is a unit in Z/k . The map
              Z[ζ] → Z/k ; x + yζ 7→ (x + y) − ab−1 y     mod k
is a surjective ring homomorphism with kernel (a+bζ) (cf. [5, Th. 2.5]). 
Lemma 2.21. Let π ∈ Z[ζ] be prime so that πN ≡ 1 mod 3 is a rational
prime.
   (a) π and its conjugate are not associates. That is, there is no unit
       u ∈ Z[ζ]× so that uπ = π.
   (b) Let n ≥ 1, and π n = a + bζ. Then gcd(a, b) = 1.
Proof. (a) Let π = x + yζ. Then π = x + yζ = (x + y) − yζ. If we assume
u(x + yζ) = (x + y) − yζ for each u ∈ Z[ζ]× , we arrive at three types of
contradictions:
   (1) π is a rational prime;
   (2) πN = 3z 2 ≡ 0 mod 3 for some z ∈ {x, y};
   (3) πN = z 2 is prime in Z for some z ∈ {x, y}.
When u = 1, we get a type-(1) contradiction. Type-(2) arises for u =
−1, ζ, ζ. Assuming u = −ζ, −ζ results in type-(3) contradictions.
   (b) To the contrary, assume gcd(a, b) > 1. Then there is some prime
integer p | a, b so that π n = a + bζ = p(r + sζ) where r, s ∈ Z. If p = 3, then
(πN)n = (π n )N = 9(r 2 + rs + s2 ) ≡ 0 mod 3 is a contradiction. Assuming
p ≡ 2 mod 3 yields, because p would itself be an Eisenstein prime, distinct
12                                A. W. NOWAK
                                                         Q
prime factorizations in the UFD Z[ζ] : a + bζ = π n = p ( σi ), yet another
contradiction. We are left to consider the case p ≡ 1 mod 3. It follows
p = σσ splits into irrational primes. By unique factorization, π and σ
must be associaties, that is, σ = uπ for some u ∈ Z[ζ]× , and what’s more,
p = σσ = (uπ)(uπ) = ππ. Invoking the fact that Z[ζ] is a UFD once again,
π and π must be associate, contradicting (a).                            
Lemma 2.22. Suppose a + bζ ∈ Z[ζ] is associated to a positive, rational
integer k. Then Z[ζ]/(a + bζ) = Z[ζ]/(k) ∼
                                         = Z/k [ζ].
Proof. Note that (k) = (a + bζ). The map
                    x + yζ 7→ (x mod k) + (y        mod k)ζ
is a surjective homomorphism with kernel (k) (cf. [5, Th. 2.1]).                
Theorem 2.23. Let n ≥ 1. We may partition the collection of primary
ideals in Z[ζ] into four classes. These, along with their respective quotient
rings are summarized below.
    (a) Suppose π is an irrational prime. That is, p = πN ≡ 1 mod 3 is
        prime in Z. Then Z[ζ]/(π n ) ∼
                                     = Z/pn .
   (b) Suppose p ≡ 2 mod 3 is a rational prime in Z[ζ]. Then Z[ζ]/(pn ) ∼  =
        Z/pn [ζ]
    (c) Suppose n = 2k is even. Then Z[ζ]/((1 + ζ)n ) ∼= Z/3k [ζ].
   (d) Suppose n = 2k + 1 is odd. Then
               Z[ζ]/((1 + ζ)n ) ∼
                                = Z[X]/(3k+1 , 3k X, X 2 − X + 1).
Proof. (a) This is a direct consequence of Lemmas 2.20, 2.21.
     (b) This is a direct consequence of Lemma 2.22.
   (c) Since (1 + ζ)n = ((1 + ζ)2)k = (3ζ)k = 3k ζ k , (1 + ζ)n is associated with
the positive, rational integer 3k . By Lemma 2.22, Z[ζ]/(1 + ζ)n ∼     = Z/3k [ζ].
                                                                               
   (d) We denote our ideal J = (1 + ζ)2k+1 = 3k ζ k (1 + ζ) = 3k (1 + ζ) .
It suffices to show that
(2.14)         C = {(a + bζ) + J | 0 ≤ a ≤ 3k+1 − 1, 0 ≤ b ≤ 3k − 1}
constitutes a set of distinct coset representatives, as
                Z[ζ]/(1 + ζ)2k+1 = (1 + ζ)2k+1N = 32k+1 = |C|.
Suppose that (a − c) + (b − d)ζ ∈ J, where 0 ≤ a, c ≤ 3k+1 − 1, and
0 ≤ b, d ≤ 3k − 1. Then
(2.15)                  (a − c) + (b − d)ζ = z3k (1 + ζ)
                    MTS AND THE EISENSTEIN INTEGERS                         13

for some z ∈ Z[ζ]. Multiply both sides of (2.15) by (2 − ζ). Then
             z3k+1 = [2(a − c) + (b − d)] + [(b − d) − (a − c)] ζ
                   =: X + Y ζ.
Thus, 3k+1 | X, Y ; so 3k+1 | X + 2Y = 3(b − d) =⇒ 3k | (b − d). By
assumption on the range of values for b and d, b = d. Since 3k+1 | Y =
(b − d) − (a − c) = 0 − (a − c) = c − a, we may conclude a = c. Hence,
(2.14) does in fact consist of distinct coset representatives.       

                 3. Distributive, Non-ramified MTS
3.1. Direct product decomposition. For the remainder of the paper,
the reader may assume f (X) refers to the polynomial X 2 − X + 1. In light
of the fact that, as a rational prime, 3 is ramified in Z[ζ], we make the
following definition.
Definition 3.1. Let Lin(M, R) be a linear MTS of order n. If 3 ∤ n, we say
that Lin(M, R) is a distributive, non-ramified (DNR, for short) MTS.
  The following lemma and its proof appear under Lemma 2.2 in [13].
Lemma 3.2 ([13]). Let p be a prime, n ≥ 1. Then f (X) ∈ Z/pn [X] has
  (a) two distinct roots modulo pn if p ≡ 1 mod 3;
  (b) no roots pn if p ≡ 2 mod 3;
  (c) a double root modulo 3 and no roots modulo 3n for n ≥ 2.
Proposition 3.3. Suppose π ∈ Z[ζ] is an irrational prime with p = πN ≡
1 mod 3, and that n ≥ 1. Let Lin(Z[ζ]/(π n ), R) be a linear Mendelsohn
pique, a±1 the distinct roots of f (X) ∈ Z/pn [X]. Then Lin(Z[ζ]/(π n ), R) is
isomorphic to either Lin(Z/pn , a) or Lin(Z/pn , a−1 ), where a±1 also stand
for right multiplication by the corresponding roots.
Proof. It is clear from Theorem 2.23(a) that R must correspond to an
abelian group automorphism of Z/pn , all of which arise from multiplica-
tion by units. Then Lin(Z[ζ]/(π n ), R) is Mendelsohn if and only if the unit
in question is a root of f (X).                                            
   Next, we generalize the argument of [13, Th. 2.12] from matrices over
finite fields to matrices over Z/pn . The presence of zero divisors means
that extra care must be taken when addressing characteristic and minimal
polynomials of matrices.
Lemma 3.4. Let p be a prime congruent to 2 modulo 3, and n ≥ 1. Suppose
S is any of the following rings: Z, Z/pn , or Z/3n . For any A ∈ M2 (S) such
that f (A) = 0, we have 1 = det(A) = Tr(A). Therefore, f (X) is equal to
det(I2 X − A), the characteristic polynomial of A.
14                              A. W. NOWAK

Proof. We treat S = Z/3 as a special case. Since S is a field in this scenario,
the Cayley-Hamilton theorem dictates that f (X) must be the characteristic
polynomial of A, for it is monic and its degree matches the dimension of A.
   Now, let                                
                                      a b
                              A=              .
                                      c d
We will establish some facts that hold over any commutative, unital ground
ring. By Lemma 2.14, A is invertible and det(A) ∈ S × . Moreover,
                                                                     
                  −1    d −b          −1                 1 − a −b
(3.1)    (det(A))                 = A = I2 − A =                          .
                       −c a                               −c 1 − d
Then b = (det(A))−1 b, c = (det(A))−1 c, and 1 − a = d(det(A))−1 . If at least
one of b or c is a unit in S, then det(A) = 1. If S is an integral domain
and at least one of b or c is nonzero, det(A) = 1. If det(A) = 1, then
1 − a = d =⇒ Tr(A) = 1. We proceed to a case-by-case argument by
contradiction.
   Suppose S = Z, a domain. If both b = c = 0, then a and d are integral
roots of f (X), but f (X) is irreducible over Z, a contradiction.
   Assume S = Z/pn . For b and c to both be non-invertible means that
p | b, c. Hence, if we take the entries of A modulo p, we get a diagonal
matrix annihilated by f (X), contradicting Lemma 3.2.(b).
   Let S = Z/3n , where n ≥ 2. By analyzing congruence relations for 2 × 2
integral matrices modulo 9 in GAP, we were able to verify that no matrix
in M2 (Z/9 ) annihilated by f (X) has both off-diagonal entries divisible by 3.
Conclude that the result holds for S = Z/9 . Suppose that n ≥ 3, and that
3 | b, c. Then taking the entries of A modulo 9 yields a matrix annihilated
by f (X) over Z/9 with off-diagonal entries divisible by 3, contradicting our
calculations in GAP.                                                         
Proposition 3.5. Suppose p ≡ 2 mod 3 is a rational prime in Z[ζ] and
n ≥ 1. Let Lin(Z[ζ]/(pn ), R) be a linear MTS, and M = (Z/pn )2 . Then
Lin(Z[ζ]/(pn ), R) ∼
                   = Lin(M, T ), where
                                              
                                        0 −1
(3.2)                         T =
                                        1 1
is the companion matrix of f (X) ∈ Z/pn [X].
Proof. That Z[ζ]/(pn ) and (Z/pn )2 are isomorphic as abelian groups is a
direct consequence of Theorem 2.23.(b). Let A ∈ M2 (Z/pn ) be a matrix
representation of R. By Theorem 2.12, it suffices to show A is similar to
(3.2). By Lemma 3.4, f (X) is the characteristic polynomial of A. We invoke
Theorem 1 in [28], which states that A is similar to the companion of its
                      MTS AND THE EISENSTEIN INTEGERS                                       15

characteristic polynomial if and only if there is some v ∈ M so that the
matrix
                                       
                                     v
(3.3)
                                    vA
is invertible; this result applies to matrices with elements from arbitrary
commutative, unital rings. Recall Z/pn is a local ring with unique maximal
ideal m generated by p + (pn ). Taking the entries of A modulo p gives
rise to an action on the quotient M/Mm ∼     = (Z/p )2 , a vector space. This
automorphism, we’ll call it A, also has f (X) as its characteristic polynomial,
and because f (X) does not split in Z/p , it has no eigenvalues. Hence,
{v, vA} is a basis for M/Mm whenever v 6= 0. By Nakayama’s lemma
(applied to the special case of local rings), such a basis lifts to a minimal
generating set {v, vA} of M, and minimal generating sets for free modules
over local rings are bases [23, Th. 2.3]. Conclude that there is some v 6= 0
for which the matrix (3.3) is invertible, and that A is similar to (3.2). 
Remark 3.6. Given a prime p ≡ 2 mod 3 and n ≥ 1, we take the linear
MTS Lin((Z/pn )2 , T ) (cf. Prop. 3.5) as the standard representative for the
single isomorphism class of distributive Mendelsohn quasigroups on (Z/pn )2 .
We adopt the notation Lin(Z/pn [ζ]) when referring to this quasigroup.
Theorem 3.7. Let Q be a distributive Mendelsohn quasigroup of order
n = pr11 · · · prkk q1s1 · · · qlsl , where each pi is a prime congruent to 1 modulo 3,
and each qi is a prime congruent to 2 modulo 3. Then
                                                       !                         !
                     Y k      Y                          Yl  Y               
                                              t
(3.4)       Q∼  =                    Lin Z/(p j ), aj
                                      i                  ×        Lin Z/ uj [ζ]
                                                                        qi
                                                                                   ,
                i=1     j                           i=1   j
                                                t   P                   P
where each aj is a root of f (X) modulo pij ,         j tj = ri , and        j u j = si .

Proof. The direct product decomposition afforded by Fischer-Galkin-Smith,
(Theorem 2.10) contains no Moufang loop factors because 3 ∤ n. Therefore,
Q is a direct product of linear MTS. Propositions 3.3 and 3.5 specify the
possible quasigroup isomoprhism classes for the factors, and these agree
with (3.4).                                                            
3.2. Enumeration. For a positive integer n, let d(m) denote the number
of isomorphism classes of distributive MTS of order m. Let l(m) denote the
number of isomorphism classes of linear (distributive) MTS. By the Chi-
nese remainder and Fischer-Galkin-Smith Theorems, in order to compute
arbitrary d(m), it suffices to determine l(pn ) = d(pn ) for all p 6= 3, l(3n ),
and d(3n ) − l(3n ). In [13], the authors gave d(p), and d(p2 ) for all primes
[13, Th. 2.12]. Donovan et. al. also calculated l(pn ) for pn < 1000, and
16                                 A. W. NOWAK

d(33), d(34 ). Moreover, the realization of d(35 ) is part of [20]. Theorem 3.7
allows us to calculate d(pn ) for arbitrary powers, as long as p 6= 3. Note
that d(p2k+1 ) = 0 whenever k ≥ 0, and p ≡ 2 mod 3 [13, Lem. 2.9].
   We think of integer partitions as multisets (X, µ) of positive integers,
where X ⊆ Z+ , and the function µ : X → Z+ determines the multiplicity
of an integer in the partition. Write (X, µ) ⊢ n if (X, µ) is a partition of n.
Let P (n) denote the number of integer partitions of n, and PE (n) signify
the number of partitions consisting only of even parts.
Theorem 3.8. Let p 6= 3 be prime, and n ≥ 1.
     (a) If p ≡ 1 mod 3, then
                                                         !
                                   X        X
(3.5)                  d(pn ) =                   µ(r) + 1 .
                                  (X,µ)⊢n   r∈X

     (b) If p ≡ 2 mod 3, then d(pn ) = PE (n).
Proof. (a) Let Q be a distributive Mendelsohn quasigroup of order pn . By
Theorem 3.7,
                               Y
(3.6)                     Q∼ =     Lin(Z/pri , ai ),
                                     i
        P
where i ri = n. Use (X, µ) to denote the partition of n associated with
this sum. Fix r ∈ X. Then Z/pr appears exactly µ(r) times as a factor in
(3.6). With two choices for MTS structure on µ(r) copies, there are
                        (µ(r) + 2 − 1)!   (µ(r) + 1)!
                                        =
                         µ(r)!(2 − 1)!       µ(r)!
                                        = µ(r) + 1

allowable isomorphism classes attached to (Z/pr )µ(r) . This count applies to
each element of X, verifying the indexing on the innermost sum of (3.5),
while the outermost indexing corresponds to the fact that we had P (n)
choices for the decomposition (3.6).
  (b) Let Q be a distributive Mendelsohn quasigroup of order p2n . We have
                                Y
(3.7)                      Q∼ =   Lin(Z/pri [ζ]),
                                     i
                          2ri
                                             P
with |Lin(Z/pri [ζ])| = p for each i, and       ri = n. Then there is a
one-to-one correspondence between choices of the decomposition (3.7) (i.e.,
isomorphism classes) and integer partitions of 2n consisting solely of even
parts.                                                                   
                    MTS AND THE EISENSTEIN INTEGERS                          17

                          4. The Ramified Case
   Classifying distributive MTS whose order is divisible by 3 presents two
issues: 1.) The fact that 3 = (1 + ζ)(1 + ζ) is ramified in Z[ζ] complicates
the direct product decomposition for CML-linear MTS, and 2.) the potential
presence of nonassociative CML in the direct product decomposition voids
our technique of relying solely on the representation theory of the Eisenstein
integers. Issue 2.) is beyond the scope of this paper. This section elaborates
issue 1.) and presents partial results towards a resolution. By Corollary 2.18,
we may, at least, state the following decomposition theorem.
Theorem 4.1. Let Q be a linear Mendelsohn quasigroup of order 3n . Then
there is a finite sequence of positive integers r1 , . . . , rl such that
                            l
                            Y
(4.1)                  Q∼
                        =         Lin(Z[ζ]/(1 + ζ)ri , Ri ),
                            i=1
        P
where    i ri = n, and each Ri is an automorphism of the abelian group
underlying Z[ζ]/(1 + ζ)ri .
   What’s more, we will prove that if ri = 2k > 2 is even, then we have
Lin(Z[ζ]/(1 + ζ)ri , Ri ) ∼
                          = Lin((Z/3k )2 , T ), where T is the companion matrix
of f (X) ∈ Z/3k [X]. Proposition 4.2, equivalent to Theorem 2.12.(iii) in [13],
clarifies the case of ri = 2.
Proposition 4.2. A Mendelsohn quasigroup Lin(Z[ζ]/(1 + ζ)2 , R) is iso-
morphic to either Lin((Z/3 )2 , −I2 ), or Lin((Z/3 )2 , T ), where
                                              
                                        0 −1
(4.2)                          T =
                                        1 1
is the companion matrix of f (X).
Proof. By Theorem, 2.23.(c), (Z/3 )2 is the abelian group underlying
Z[ζ]/(1 + ζ)2. Similarity classes of (Z/3 )2 -automorphisms are represented by
rational canonical matrices. Matrices annihilated by f (X) = (X + 1)2 over
Z/3 [X] have two possible RCFs. Those are, −I2 and T .                      
  The following lemma is needed for the case of classifying higher k-values.
Lemma 4.3. Let k ≥ 2, A ∈ M2 (Z). If A ≡ −I2 mod 3, then f (A) 6≡ 0
mod 3k .
Proof. The last paragraph of the proof of Lemma 3.4 furnishes a sufficient
argument.                                                               
Proposition 4.4. Let k ≥ 2, and Lin(Z[ζ]/(1 + ζ)2k , R) be a Mendelsohn
quasigroup and M = (Z/3k )2 . Then Lin(Z[ζ]/(1 + ζ)2k , R) ∼
                                                           = Lin(M, T ),
where
18                                A. W. NOWAK


                                                
                                          0 −1
(4.3)                           T =
                                          1 1
is the companion matrix of f (X).
Proof. Theorem 2.23.(c) exhibits an abelian group isomorphism
Z[ζ]/(1 + ζ)2k ∼= (Z/3k )2 . Let A denote a matrix representation of R.
Because k ≥ 2, f (X) has no roots in Z/3k (cf. Lemma 3.2(c)), and
det(I2 X − A) = f (X). Just as in the proof of Proposition 3.5, it suffices to
show that A is similar to the companion matrix of its characteristic poly-
nomial by producing a v ∈ (Z/3k )2 that makes the transpose of (v vA)
invertible.
  Define A to be the matrix consisting of the entries of A taken modulo
3. Then A acts on M/Mm ∼     = (Z/3 )2 , where m = (3 + (3k )) is the unique
maximal ideal of Z/3k . Recall that in Z/3 , det(XI2 −A) = f (X) = (X +1)2 .
Let W denote the eigenspace of A associated with −1. Then dim(W ) = 1
or 2. By Lemma 4.3, A 6= −I2 , so dim(W ) = 1. Pick v ∈ W ⊥ . Then
{v, vA} forms a basis of M/Mm. Once again, apply Nakayama’s lemma,
and we have {v, vA} as a basis for the free Z/3k -module M. Conclude A is
similar to the companion of f (X).                                          
4.1. Odd powers of 1 + ζ: mixed congruence. In this section, we con-
sider possible MTS structures on Z[ζ]/(1 + ζ)2k+1 . Upon examination of
MTS on Z[ζ]/(1 + ζ)2k+1 for arbitrary k, we are presented with a mixed
congruence representation theory. To explain, let G = Z/3k ⊕ Z/3k+1 , πk :
Z → Z/3k and πk+1 : Z → Z/3k+1 be natural projections, and π = πk ⊕ πk+1 .
Theorem 2.23.(d) tells us it is enough to describe conjugacy classes of el-
ements annihilated by f (X) in Aut(G). We use the work presented in a
concise, highly readable note by Hillar and Rhea to translate this problem
into terms of matrix algebra [18]. Consider the subset
(4.4)                   R3 = {(aij ) ∈ M2 (Z) : 3 | a21 }
of 2 × 2 integral matrices. This set is a subalgebra of M2 (Z) [18, Lm. 3.2],
and
(4.5)       ψ : R3 → End(G); A 7→ ((x1 , x2 )π 7→ ((x1 , x2 )A)π)
is a surjective ring homomorphism [18, Th. 3.3] with kernel
(4.6)         {(aij ) ∈ M2 (Z) : 3k | a11 , a12 and 3k+1 | a21 , a22 }
[18, Lm. 3.4]. Furthermore, an endomorphism Aψ ∈ End(G) is an automor-
phism if and only if (A mod 3) ∈ GL2 (Z/3 ) [18, Th. 3.6]. The enumeration
techniques of Donovan et. al. classify all MTS on Z[ζ]/(1+ζ), Z[ζ]/(1+ζ)3,
and Z[ζ]/(1 + ζ)5.
                    MTS AND THE EISENSTEIN INTEGERS                        19

Proposition 4.5. Let Lin(Z[ζ]/(1+ζ)2k+1, R) be a Mendelsohn quasigroup,
M1 = Z/3 ⊕ Z/9 , M2 = Z/9 ⊕ Z/27 ,
                                        
                                   2 −1
                          T =              ,
                                   3 −1
and ψ the ring homomorphism (4.5).
   (a) If k = 0, then Lin(Z[ζ]/(1 + ζ)2k+1, R) ∼
                                               = Lin(Z/3 , −1).
   (b) If k = 1, Then Lin(Z[ζ]/(1 + ζ)2k+1, R) ∼
                                               = Lin(M1 , T ψ ).
   (c) If k = 2, Then Lin(Z[ζ]/(1 + ζ)2k+1, R) ∼
                                               = Lin(M2 , T ψ ).
Proof. (a) Quite simply, this follows from the field isomorphism
Z[ζ]/(1 + ζ) ∼
             = GF(3)
  (b) Table 1 in [13] tells us that there are 3 isomorphism classes of linear
MTS of order 33 . The possible Eisenstein module decompositions are
    (1) (Z[ζ]/(1 + ζ))3 ;
    (2) Z[ζ]/(1 + ζ)2 ⊕ Z[ζ]/(1 + ζ);
    (3) Z[ζ]/(1 + ζ)3;
The first must correspond to −I3 ∈ M3 (Z/3 ), and the second, by Proposition
4.4, to T ⊕ (−1), where T is the companion of f (X) ∈ Z/3 [X]. This leaves
us with Lin(M1 , T ψ ) as the only possible linear MTS structure on (3).
   (c) Donovan et. al.’s enumeration relates 7 isomorphism classes of order-
 5
3 linear MTS. There are 7 integer partitions of 5, so for each decomposition
of the form (4.1), there is exactly one isomorphism class. In particular, the
Z[ζ]-module Z[ζ]/(1 + ζ)5 gives rise to one isomorphism class.             
  Based upon the evidence proffered by small examples in Proposition 4.5,
we make the following conjecture.
Conjecture 4.6. Given k ≥ 3 and an MTS Lin(Z[ζ]/(1 + ζ)2k+1 , R), there
is a quasigroup isomorphism Lin(Z[ζ]/(1 + ζ)2k+1, R) ∼
                                                     = Lin(M, T ψ ), where
                           ψ
M = Z/3k ⊕ Z/3k+1 , and T is defined along the lines of Proposition 4.5.
Moreover, the enumeration of order-3n , linear MTS is given by l(3n ) =
P (n).
4.1.1. Lifting. The following discussion presents techniques for lifting the
mixed congruence representation theory into M2 (Z). Take n ≥ 1. The
projection Z → Z/n extends naturally to a map between matrix groups
SL2 (Z) → SL2 (Z/n ), furnishing a short exact sequence
(4.7)             1 → Γ(n) → SL2 (Z) → SL2 (Z/n ) → 1.
The kernel Γ(n) is referred to as the principal congruence subgroup of level
n. A subgroup of SL2 (Z) is a congruence subgroup if it contains a principal
congruence subgroup of any level. The Hecke congruence subgroup of level
20                                 A. W. NOWAK

n, denoted Γ0 (n), is the preimage of upper-triangular matrices under the
projection SL2 (Z) → SL2 (Z/n ) [11, Sec 1.2]. Notice that the group of
determinant-one units of the matrix subalgebra R3 is precisely Γ0 (3).
Lemma 4.7. All elements in M2 (Z) annihilated by the polynomial f (X)
have determinant 1, and they lie in the same SL2 (Z)-conjugacy class.
Proof. Suppose A ∈ M2 (Z), and that f (A) = 0. By Lemma 3.4, we have
det(A) = Tr(A) = 1. Thus, A ∈ SL2 (Z). In [8, Th. 1], it is shown that
the number of SL2 (Z)-conjugacy classes whose constituents have trace t is
equal to the number of equivalence classes of binary quadratic forms with
discriminant t2 − 4. Up to equivalence, there is only one binary quadratic
form with discriminant 12 − 4 = −3.                                     
Lemma 4.8. Suppose A ∈ Γ0 (3), and f (A) = 0. Then there exists some
P ∈ Γ0 (3) so that
                                        
                      −1          2 −1
(4.8)                P AP =                .
                                  3 −1
Proof. Lemma 4.7 tells of a P ∈ SL2 (Z) for which (4.8) holds. We prove
that any such P must belong to Γ0 (3). Our argument relies on the fact that
when the entries of A and P are taken modulo 3, we get invertible matrices
in SL2 (Z/3 ). Now,
                                         
                      −1         −1 −1
                     P AP ≡                   mod 3.
                                   0 −1
We claim that either
                                          
                                   −1 −1
(4.9)                     A≡                     mod 3,
                                    0 −1
or
                                          
                                   −1 1
(4.10)                    A≡                     mod 3.
                                    0 −1
Notice that f (A) = 0 ≡ 0 mod 3. The only upper-triangular matrices in
SL2 (Z/3 ) annihilated by f (X) are (4.9), (4.10), and −I2 . However, since
f (A) = 0 ≡ 0 mod 9 we cannot have A ≡ −I2 mod 3, for this would
contradict Lemma 4.3. Thus, (4.9) or (4.10) holds. A straightforward com-
putation in GAP verifies that the only elements of SL2 (Z/3 ) conjugating
(4.9) to itself, or (4.10) to (4.9) contain a zero in the lower left-hand entry.
Thus, P is upper-triangular in SL2 (Z/3 ), so P ∈ Γ0 (3).                     
     For our next proposition, we define
(4.11)      C = {α ∈ Aut(G) | ∃A ∈ Γ0 (3) (Aψ = α ∧ A2 − A + I2 = 0)}.
Proposition 4.9. All members of C are conjugate.
                    MTS AND THE EISENSTEIN INTEGERS                        21

Proof. Let α ∈ C and A ∈ Γ0 (3) so that Aψ = α, and f (A) = 0 over Z. We
show α is conjugate to
                                        ψ
                                   2 −1
                          γ=                .
                                   3 −1
By Lemma 4.8, there is some P ∈ Γ0 (3) so that (4.8) holds. Therefore,
γ = (P −1 AP )ψ = (P ψ )−1 αP ψ .                                   
Example 4.10. The key to proving Conjecture 4.6 may be showing that
all members of Aut(G) annihilated by f (X) belong to C. This is the case
for G = Z/3 ⊕ Z/9 . Matrix representatives for the six automorphisms
annihilated by f (X) and corresponding lifts into Γ0 (3) are given below:
                                           
                         2 2         2 −1
                                ≡                ;
                         3 8         3 −1
                                             
                         2 1          2     1
                                ≡                    ;
                         6 8         −3 −1
                                             
                         2 2          5 −1
                                ≡                  ;
                         3 5         21 −4
                                                
                         2 1           5      1
                                ≡                       ;
                         6 5         −21 −4
                                              
                         2 2         26 −31
                                ≡                     ;
                         3 2         21 −25
                                                  
                         2 1          26      31
                                ≡                         .
                         6 2         −21 −25
These matrix representations were obtained by implementing the procedure
outlined in the proof of [18, Th. 4.1] in GAP.

           5. Combinatorial Properties of Linear MTS
5.1. Purity.
Definition 5.1. A Mendelsohn triple system (Q, B) is pure if whenever
a, b ∈ Q, we have (a b ab) ∈ B =⇒ (b a ab) ∈
                                           / B.
  Definition 5.1 is equivalent to anticommutativity of the underlying quasi-
group. The class of anticommutative quasigroups is specified in Q by the
quasi-identity (one defined by implication; cf. [6, Def. V.2.24])
(5.1)                      xy = yx =⇒ x = y.
Hence, the class of anticommutative quasigroups forms a quasivariety, or a
class of algebras defined by quasi-identities. Because Steiner triple systems
22                               A. W. NOWAK

are equivalent to MTS whose underlying quasigroup is commutative, purity
can be seen as a quality of MTS which are maximally non-Steiner.
  Constructing linear MTS over finite fields, Mendelsohn proved the exis-
tence of pure MTS of order p for p ≡ 1 mod 3 and of order p2 for p ≡ 2
mod 3 [24, Ths. 6, 7]. The existence spectrum of pure MTS was expanded
using linear techniques [12], until Bennett and Mendelsohn showed that the
existence spectrum of pure MTS matches (with the exception of order 3)
that of all MTS. That it to say, a pure MTS of order n exists, with the
exception of n = 1, 3, 6, if and only if n ≡ 0, 1 mod 3 [3].
Lemma 5.2. Let Q1 and Q2 be nonempty quasigroups. The direct product
Q1 × Q2 is anticommutative if and only if each of Q1 and Q2 are anticom-
mutative.
Proof. Quasivarities are closed under direct product [6, Th. V.2.25]. Hence,
the product of anticommutative quasigroups is anticommutative. To ob-
tain the other direction, we prove the contrapositive. Suppose Q1 is not
anticommutative and that a, b ∈ Q1 are distinct elements that commute.
Then for any x ∈ Q2 (recall we assume each quasigroup to be nonempty),
(a, x) 6= (b, x), while (a, x)(b, x) = (ab, x2 ) = (ba, x2 ) = (b, x)(a, x). 
Proposition 5.3. Every DNR MTS is pure.
Proof. By Lemma 5.2, it suffices to show that for p ≡ 1 mod 3, Lin(Z/pn , a)
is pure, and that for p ≡ 2 mod 3, Lin(Z/pn [ζ]) is pure. In either case,
xy = yx means xR + y(1 − R) = yR + x(1 − R) =⇒ x(2R − 1) = y(2R − 1),
so it will suffice to show 2R − 1 is invertible.
   The case of (Z/p , a) is covered in [24, Th. 6]. If 2a − 1 were not invertible
in Z/p , then 2a − 1 = 0 =⇒ a = 2−1 . By Lemma 2.14, f (2) = 3 = 0,
a contradiction. Furthermore, by way of contradiction, suppose a ∈ Z,
f (a) ≡ 0 mod pn , and 2a − 1 is not a unit modulo pn , where n > 1. This
means that 2a − 1 = mpk for some m ∈ Z and 1 ≤ k ≤ n, whereby f (a) ≡ 0
mod p, and 2a − 1 ≡ 0 mod p, which contradicts the n = 1 case.
   Fix p ≡ 2 mod 3. We use
                                               
                                         0 −1
                                A=
                                         1 1
to represent Lin(Z/pn [ζ]). Then
                                                        
                                                 −1 −2
                      det (2A − I2 ) = det
                                                  2  1
                                     = 3,
which is a unit modulo pn , so 2A − I2 is invertible.                          
                    MTS AND THE EISENSTEIN INTEGERS                         23

Proposition 5.4. Let M be an abelian group of order 3n , R ∈ Aut(M)
such that Lin(M, R) is Mendelsohn. Then M is not a pure MTS.
Proof. By Lemma 5.2, it suffices to show that any MTS of the form
Lin(Z[ζ]/(1 + ζ)n , R) is not pure. Note Z[ζ]/(1 + ζ) ∼
                                                      = Z/3 , so if n = 1, the
system is Steiner.
   Henceforth, assume n ≥ 2. According to the discussion of mixed congru-
ence in Section 4.1, whether n is even or odd, R can be represented by a
2 × 2 integral matrix; call it A. By Lemma 3.4 —dropping the second row
of A down a level of congruence if n is odd— there is some k ≥ 1 such that
det(A) ≡ Tr(A) ≡ 1 mod 3k . Consider
                                                       
                                     2a11 − 1    2a12
                 P := 2A − I2 =                           .
                                       2a21    2a22 − 1
We claim that P is not invertible. It suffices to show det(P ) ≡ 0 mod 3.
In fact,
               det(P ) = 4a11 a22 − 2a11 − 2a22 + 1 − 4a12 a21
                      = 4(a11 a22 − a12 a21 ) − 2(a11 + a22 ) + 1
                      = 4 det(A) − 2Tr(A) + 1
                      ≡3     mod 3k
                      ≡0     mod 3.
With P singular, we may choose some nonzero
                   v ∈ KerP = {v ∈ M | vA + vA = v}.
Since 2 ∤ |M|, v 6= −v. Moreover, v(−v) = vA − v + vA = v − v = 0 =
−v + v = (−v)A + v − vA = (−v)v. Conclude there exist distinct vectors
commuting under the quasigroup operation given by R.                
Theorem 5.5. Let M be a finite abelian group of order n, and Lin(M, R)
a linear MTS. Then Lin(M, R) is pure if and only if 3 ∤ n. That is, a linear
MTS is pure if and only if it is non-ramified.
                          Q
Proof. Let Lin(M, R) = i Qi be the decomposition of Corollary 2.18. By
Lemma 5.2, Lin(M, R) is pure if and only if each Qi is anticommutative.
Propositions 5.3 and 5.4 reveal that a given factor Qi is anticommutative if
and only if 3 ∤ |Qi |. Therefore, Lin(M, R) is pure if and only if each Qi is
anticommutative if and only if 3 ∤ |Qi | for all i if and only if 3 ∤ n.   
24                                A. W. NOWAK

5.2. The Converse of Linear MTS.
5.2.1. Self-Converse MTS. Let ∗ : Q2 → Q be a binary operation on a set
Q, and τ : (x, y) 7→ (y, x) the twist on Q2 . We define the opposite of ∗ to be
the binary operation τ ∗ : (x, y) 7→ y ∗ x. Given a quasigroup (Q, ·, /, \), its
opposite quasigroup is the quadruple (Q, ◦, \\, //), where ◦, \\, and // denote
the opposite operations of multiplication, left division, and right division
respectively. Recall that a Mendelsohn quasigroup has the form (Q, ·, ◦, ◦),
so its opposite will be (Q, ◦, ·, ·). This has a combinatorial interpretation.
Definition 5.6. Let (Q, B) be an MTS. The converse of (Q, B) is given by
(Q, B−1 ), where B−1 = {(b a ab) | (a b ab) ∈ B}.
Definition 5.7. Let (Q, B) be an MTS with corresponding quasigroup
(Q, ·, ◦, ◦). We say that (Q, B) is self-converse if (Q, ·, ◦, ◦) is isomorphic to
its opposite (Q, ◦, ·, ·). A CML-linear MTS Lin(M, R) is self-converse if and
only if Lin(M, R) ∼ = Lin(M, 1 − R) = Lin(M, R−1 ).
   The term self-converse comes from graph theory. The converse of a di-
graph consists of the same set of points, with arrows reversed. In fact, in
order to obtain the converse of an MTS, one may take the Cayley graph
with respect to multiplication in the underlying quasigroup and reverse ar-
rows. The examination of self-converse MTS first appears in the literature
with Colbourn and Rosa’s survey on directed triple systems [9]. Just as
in the case of pure systems, it was shown that the existence spectrum of
self-converse MTS matches the existence spectrum of arbitrary MTS [7].
We characterize self-converse DNR MTS and conjecture a complete charac-
terization of entropic self-converse MTS.
Lemma 5.8. Let Lin(M  Q 1 , R1 ) and Lin(M2 , R2 ) be Mendelsohn quasigroups.
The direct product i Lin(Mi , Ri ) is self-converse if and only if each factor
Lin(Mi , Ri ) is self-converse.
                             Q                  ∼ Lin(M1 × M2 , R±1 × R±1 ).
Proof. Begin by noticing i Lin(Mi , Ri±1 ) =                             1      2
                                                                    −1
We can extend isomorphisms
                         Q      f i : Lin(Mi
                                           Q , Ri ) → Lin(M   i , Ri   ) uniquely to
                                                           −1
the product f1 × f2 : i Lin(Mi , Ri ) → i Lin(Mi , Ri );Qthis proves suffi-
ciency.
Q        Conversely, we can restrict an isomorphism f : i Lin(Mi , Ri ) →
               −1                                                           −1
   i Lin(Mi , Ri ) to isomorphisms f |0×Mi : Lin(Mi , Ri ) → Lin(Mi , Ri ), ver-
ifying necessity.                                                                 
Theorem 5.9. Let M be a finite abelian group of order n, and Lin(M, R)
a DNR MTS. Then Lin(M, R) is self-converse if and only if for each prime
p | n, we have p ≡ 2 mod 3.
Proof. The MTS Lin(M, R) is self-converse if and only if each factor in its
direct product decomposition (3.4) is self-converse. Propositions 3.3 and
                      MTS AND THE EISENSTEIN INTEGERS                      25

3.5 reveal that this is possible if and only if each factor is of the form
Lin(Z/pn [ζ]) for some p ≡ 2 mod 3.                                      
  Conjecture 4.6 implies the following:
Conjecture 5.10. Let M be a finite abelian group, and Lin(M, R) an MTS.
Then Lin(M, R) is self-converse if and only if no prime dividing the order
of M is congruent to 1 modulo 3.
5.2.2. Self-Orthogonal MTS.
Definition 5.11. Two quasigroups on the same set of symbols (Q, ·) and
(Q, ∗) are orthogonal if for every a, b ∈ Q the system of equations
                                     x·y =a
                                     x∗y =b
as a unique solution. A quasigroup Q is self-orthogonal if it is orthogonal
to its opposite.
Lemma 5.12. Let (Q, ·, /, \) be a quasigroup with distinct, commuting el-
ements. Then (Q, ·, /, \) is not self-orthogonal.
Proof. Choose distinct, commuting elements q, q ′ ∈ Q, and fix a = q · q ′ =
q ′ · q. With respect to the system of equations
                                     x·y =a
                                     x ◦ y = a,
the ordered pairs (q, q ′), (q ′ , q) constitute distinct solutions.       
  The above lemma demonstrates that self-orthogonal quasigroups are nec-
essarily anticommutative. In general, the converse does not hold. However,
Di Paola and Nemeth showed that any MTS linear over a field which is pure
(anticommutative) is necessarily self-orthogonal [12, Th. 7]. We prove that
their result extends to quotients of Z[ζ] by primary ideals.
Theorem 5.13. Let M be a finite abelian group, and Lin(M, R) a linear
MTS. Then Lin(M, R) is self-orthogonal if and only if it is non-ramified if
and only if it is pure.
Proof. Note that a quasigroup is self orthogonal if and only if x1 y1 = x2 y2
and y1 x1 = y2 x2 =⇒ x1 = x2 and y1 = y2 . With this characterization,
one may prove —employing a quasivariety argument identical to that of
the proof of Lemma 5.2— that the direct product of quasigroups is self-
orthogonal if and only if each factor is self-orthogonal. Thus, the fact that
ramified linear MTS are not self-orthogonal follows directly from Proposi-
tion 5.4 and Lemma 5.12. This proves that all self-orthogonal linear MTS
are non-ramified.
26                              A. W. NOWAK

   Next, to prove the converse, we have to establish self-orthogonality of
Lin(Z/pn , a) whenever p ≡ 1 mod 3, and Lin(Z/pn [ζ]) whenever p ≡ 2
mod 3. But first, we make a few observations regarding an arbitrary linear
MTS Lin(M, R). Suppose x1 , x2 , y1 , y2 ∈ M so that x1 y1 = x2 y2 and y1 x1 =
y2 x2 . Recall 1 − R = R−1 = −R2 . Then by hypothesis,
(5.2)                    x1 R − y1 R2 = x2 R − y2 R2 ,
and
(5.3)                    y1 R − x1 R2 = y2 R − x2 R2 .
Now multiply (5.2) and (5.3) by R−1 and rearrange terms in order to obtain
(5.4)                      x1 − x2 = (y1 − y2 )R,
and
(5.5)                      y1 − y2 = (x1 − x2 )R.
Substituting the right-hand side of (5.5) in for y1 − y2 in (5.4) yields
(5.6)                      x1 − x2 = (x1 − x2 )R2 .
Similarly,
(5.7)                      y1 − y2 = (y1 − y2 )R2 .
   Now, assume we are working in Lin(Z/pn , a). If x1 − x2 6= 0, in order for
(5.6) to hold, a2 − 1 must be a zero divisor in Z/pn , so p | a2 − 1. Thus, a
is a square root of 1 modulo p, and if this is the case, then a ≡ ±1 mod p.
We also have a2 − a + 1 ≡ 0 mod p. Clearly then, a cannot be congruent
to 1, so it must be congruent to −1 modulo p. However, f (−1) ≡ 0 mod p
if and only if p = 3 by Lemma 2.14.(b), contradicting our assumption that
p ≡ 1 mod 3. We are left to conclude x1 = x2 ; similarly y1 = y2 .
   The case of Lin(Z/pn [ζ]) is more concrete. By Proposition 3.5, we can
choose R so that R2 is represented by
                                          
                                  −1 −1
                                              .
                                   1    0
Suppose x1 − x2 = (a, b) 6= 0. That is,
                            (a, b) = (a, b)R2
                                   = (b − a, −a).
Then b = −a = 2a, so that 0 = 3a. Since, p does not divide 3, it is invertible
in Z/pn . Conclude a = −b = 0, a contradiction. Thus, x1 −x2 = 0 = y1 −y2 .
   We have thus proven the equivalence of linear MTS being non-ramfied and
self-orthogonal. The equivalence of the former with purity was established
in Theorem 5.5.                                                             
                     MTS AND THE EISENSTEIN INTEGERS                           27

                        6. Reverse-Linearization
  We return to the alternative presentation Z[X]/(X 2 + X + 1) for the
Eisenstein integers. Since X 2 − X + 1 arises when constructing CML-linear
quasigroups that satisfy idempotence (1.2) and semisymmetry (1.5), it is
only natural to ask if there is a quasigroup variety whose linear theory rests
on X 2 + X + 1. Forcing a CML-linear quasigroup to be semisymmetric
requires L = R−1 , and R3 + 1 = 0. Further imposing idempotence leads to
R2 −R+1 = 0. To produce R2 +R+1 = 0, we would like the automorphism
to be not order 6, but rather order 3, as R3 − 1 = (R − 1)(R2 + R + 1),
whence the following definition.
Definition 6.1. The variety of right Eisenstein quasigroups, denoted RE,
is generated by (2.1)-(2.4) and
(6.1)                            (yx · x)x = y.
The variety LE of left Eisenstein quasigroups is defined by (2.1)-(2.4), and
(6.2)                            x(x · xy) = y.
Proposition 6.2. Suppose Lin(M, R, L) is a CML-linear pique. Then this
structure belongs to RE if and only if R2 + R + 1 = 0, and Lin(M, R, L)
belongs to LE if and only if L2 + L + 1 = 0.
Proof. The linearization of (yx · x)x is
(6.3)       yR3 + xLR2 + xLR + xL = yR3 + xL(R2 + R + 1).
If (6.1) holds in Lin(M, R, L), then substituting y = 0 means that 0 =
xL(R2 + R + 1) for all x ∈ M. Since L is an automorphism, R2 + R + 1 = 0.
Conversely, if we take a CML-linear pique Lin(M, R, L), and we assume
R2 + R + 1 = 0, then R3 − 1 = (R − 1)(R2 + R + 1) = 0, so we find that
yR3 + xL(R2 + R + 1) = yR3 = y. Proof of the characterization for CML-
linear piques in LE follows by an identical argument; just switch the roles
of L and R.                                                              
Remark 6.3. Although (6.1) guarantees R2 + R + 1 = 0 in a CML-linear
pique Lin(M, R, L), it says nothing of L. Hence, a Theorem 2.15-type result
for Z ⊗ RE would relate RE not to the Eisenstein integers, but rather to
Z[ζ] ⊗Z Z[L, L−1 ]. A search for conditions on quasigroup words furnishing
some p(R) ∈ Z[R, R−1 ] so that L = p(R) –and thus producing a functor
Z[ζ]-Mod → Z ⊗ V, where V is a subvariety of RE– is reserved for future
research.
  Our final result involves the notion of quasigroup homotopy. Let (Q, ·)
and (Q′ , ∗) be quasigroups. A triple of functions (f1 , f2 , f3 ) mapping Q into
Q′ is a homotopy if for all x, y ∈ Q, (x)f1 ∗ (y)f2 = (x · y)f3. If each of
28                                  A. W. NOWAK

the fi are bijections, then (f1 , f2 , f3 ) is an isotopy. An isotopy of the form
(f1 , f2 , 1Q ) : (Q, ·) → (Q, ∗) is principal [30]. Homotopy is a vital aspect of
nonassociative geometry [29]. Specifically, every 3-web is coordinatized by
Qtp(⊤, Q), the set of quasigroup homotopies from a singleton into some
quasigroup Q. Isotopes of Q yield different coordinatizations of the same
3-web (cf. [34, Th. 1]).
Theorem 6.4. Every distributive Mendelsohn quasigroup is principally iso-
topic to a left Eisenstein quasigroup.
Proof. The case of the empty quasigroup is true by the fact that this
structure may be viewed as both distributive and left Eisenstein. Let
Lin(M, R, 1 − R) be a CML-linear pique which is Mendelsohn; by Theo-
rem 2.9, this is the same thing as fixing an arbitrary nonempty, distribu-
tive Mendelsohn quasigroup. We claim Lin(M, −R, R2 ) lies in LE, and
(−1, −1, 1) is a principal isotopy from Lin(M, −R, R2 ) onto the CML-linear
pique Lin(M, R, 1 − R). Note that (R2 )2 + R2 + 1 = R3 (R) + R2 + 1 =
−R + R2 + 1 = 0, so Lin(M, −R, R2 ) is in LE by Proposition 6.2. Further-
more,
                         (x · y)1M = −xR + yR2
                                    = −xR + y(R − 1)
                                    = −xR + (−y)(1 − R)
                                    = x(−1M ) ∗ y(−1M ),
verifies (−1, −1, 1) : Lin(M, −R, R2 ) → Lin(R, 1 − R) is an isotopy.                

                              Acknowledgements
  The author would like to thank his doctoral advisor, Jonathan D. H.
Smith, for helping him to prepare the manuscript, and for pointing out
the connection between the ramified classification problem of Section 4 and
congruence subgroups.

                                   References
 [1] N. Andruskiewitsch and M. Graña, From racks to pointed Hopf algebras, Adv. Math.,
     178 (2003) 177-243.
 [2] V. D. Belousov, On structure of distributive quasigroups, Math. Sb. (N. S.), 50(92)
     1960, 267-298 (Russian).
 [3] F. E. Bennett and N. S. Mendelsohn, On pure cyclic triple systems and semisym-
     metric quasigroups, Ars Combin., 5 (1978), 13-22.
 [4] R. H. Bruck, Some results in the theory of quasigroups, Trans. Amer. Math. Soc.,
     55 (1944), 19-52.
 [5] V. Buçaj, Finding factors of factor rings over the Eisenstein integers, Int. Math.
     Forum, 9 (2014), 1521-1537.
                       MTS AND THE EISENSTEIN INTEGERS                                 29

 [6] S. Burris and H. P. Sankappanavar, A Course in Universal Algebra, The Millennium
     Edition, 2012, .
 [7] Y. Chang, G. Yang and Q. Kang, The spectrum of self-converse MTS, Ars Combin.,
     44 (1996), 273-281.
 [8] S. Chowla, J. Cowles, and M. Cowles, On the number of conjugacy classes in SL2 (Z),
     J. Number Theory, 12 (1980), 372-377.
 [9] C. J. Colbourn and A. Rosa, Directed and Mendelsohn triple systems, in Contem-
     porary Design Theory: A Collection of Surveys, Wiley, Hoboken, NJ, 97-136.
[10] P. Dehernoy, Braids and Self-Distributivity, Birkhäuser, Basel, 2000.
[11] F. Diamond and J. Shurman, A First Course in Modular Forms, Springer, New
     York, 2005.
[12] J. W. Di Paola and E. Nemeth, Generalized triple systems and medial quasigroups, in
     Proc. Seventh Conf. Combinatorics, Graph Theory, and Computing, 1976, Congres-
     sus Numerantium, No. XVII (Utilitas Math., Winnipeg Manitoba, 1976), 298-306.
[13] D. M. Donovan, T. S. Griggs, T. A. McCourt, J. Opršal, and D. Stanovský, Dis-
     tributive and anti-distributive Mendelsohn triple systems, Canadian Math. Bull., 59
     (2016), 36-49.
[14] B. Fischer, Distributive quasigruppen endlicher ordnung, Math. Z., 83 (1964), 267-
     303 (German).
[15] V. M. Galkin, Finite distributive quasigroups, Mat. Zametki, 24 (1978), 39-41 (Rus-
     sian).
[16] The GAP Group, GAP – Groups, Algorithms, and Programming, Version 4.10.1 ;
     2019, https://www.gap-system.org.
[17] G. H. Hardy and E. M Wright, An Introduction to the Theory of Numbers, 4th
     edition, Oxford Univ. Press, Oxford, 1960.
[18] C. J. Hillar and D. L. Rhea, Automorphisms of finite abelian groups, Amer. Math.
     Monthly, 114 (2007), 917-923.
[19] K. Ireland and M. Rosen, A Classical Introduction to Modern Number Theory, 2nd
     edition, Springer, Berlin, 1990.
[20] P. Jedlička, D. Stanovský, and P. Vojtěchovský, Distributive and trimedial quasi-
     groups of order 243, Discrete Math., 340 (2017), 404-415.
[21] D. Joyce, A classifying invariant of knots, the knot quandle, J. Pure Appl. Algebra,
     23 (1982), 37-65.
[22] T. Kepka and P. Nêmec, Commutative Moufang loops and distributive groupoids of
     small orders, Czechoslovak Math. J., 31 (1981), 633-669.
[23] H. Matsumura, Commutative Ring Theory, Cambridge Univ. Press, Cambridge UK,
     1989.
[24] N. S. Mendelsohn, A natural generalization of Steiner triple systems, Computers
     in number theory (Proc. Sci. Res. Council Atlas Sympos. no. 2, Oxford, 1969),
     Academic Press, London, 1971, 323–338.
[25] M. Misaghian, Factor rings and their decomposition in the Eisenstein integers ring
     Z[ω], Armenian J. Math., 5 (2013), 58-68.
[26] D. C. Murdoch, Structure of abelian quasi-groups, Trans. Amer. Math. Soc., 49
     (1941), 392-409.
[27] P. T. Nagy and K. Strambach, Loops, their cores and symmetric spaces, Israel J.
     Math., 105 (1998), 285-322.
[28] V. Prokip, On similarity of matrices over commutative rings, Linear Algebra Appl.,
     399 (2005), 225-233.
30                                   A. W. NOWAK

[29] L. Sabinin, Smooth Quasigroups and Loops, Springer, Dordrecht, 1999.
[30] A. Sade, Quasigroupes demi-symétriques. Isotopies préservant la demi-symétrie,
     Math. Nacr., 33 (1967), 177-188 (French).
[31] A. Sade, Quasigroupes demi-symétriques. III. Constructions linéares, A-maps, Ann.
     Soc. Sci. Bruxelles Sér I., 81 (1967), 5-17 (French).
[32] J. D. H. Smith, Finite distributive quasigroups, Math. Proc. Cambridge Philos. Soc.,
     80 (1976), 37-41.
[33] J. D. H. Smith, An Introduction to Quasigroups and Their Representations, CRC
     Press, Boca Raton, FL, 2007.
[34] J. D. H. Smith, Quasigroup homotopies, semisymmetrization, and reversible au-
     tomata, Internat. J. Algebra Comput., 18 (2008), 1203-1221.
[35] D. Stanovský, A guide to self-distributive quasigroups, or Latin quandles, Quasi-
     groups and Related Systems, 23 (2015), 129-163.
[36] K. Toyoda, On axioms of linear functions, Proc. Imp. Acad. Tokyo, 17 (1941),
     221-227.

