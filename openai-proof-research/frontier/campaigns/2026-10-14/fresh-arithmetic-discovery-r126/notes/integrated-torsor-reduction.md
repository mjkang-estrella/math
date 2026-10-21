# Integrated reduction: arithmetic transport and generic torsor compression

PREFREEZE / no nominee. This is a record of paid reductions and unsuccessful feasibility work, not a frozen theorem or an author-proof intake. All source operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. No correctness, contribution, acceptance or count is assigned.

## 1. The actual input and the question being tested

The second and only developed family is essential dimension of finite constant groups, equivalently compression of generic finite torsors. The first family navigation (arithmetic dynamics) was null. No third direction is pursued. The narrow second-family catalogue search also found no direct source theorem. Source031 was then examined as a possible input to arithmetic descent of torsors; anabelian reconstruction itself is not proposed as a new target.

Source031, introduction `thm:main`, says exactly: for number fields F1,F2 and possibly infinite solvably closed Galois extensions Ei/Fi, every continuous homomorphism alpha:G1->G2 with open image is induced by a unique field embedding j:E2->E1, satisfying g j=j alpha(g). Here Gi=Gal(Ei/Fi). The kernel is unrestricted. Solvably closed means no nontrivial abelian algebraic extension, not algebraically closed. We retain this distinction: finite torsors under discussion must be split by Ei unless Ei is an algebraic closure.

All six operative source sections were read. In particular the proof does more than identify an abstract isomorphism: normalizer extension and regular Kummer amplification, character/Frobenius detection, uniform missed-prime bounds, matching residue characteristics, and compactness produce one conjugation at all finite quotients. The final cyclotomic criterion gives the actual embedding. Consequently compatibility at arbitrarily many finite quotients, or its simultaneous nature, cannot be counted again as a missing operation. Neither the signed character module nor the uniform Kummer bound is developed as a new research family or a new claim here.

The classical endpoint was checked against Hoshi's September2022 revised author manuscript, Theorem3.4 and its proof, with the cited Corollary2.8 and proof of Theorem2.6 also read. The paper is not asserted byte-identical to the published2025 article. Hoshi already reconstructs compatible finite fields and passes to their union. An assertion that a prescribed family of finite torsors can be transported compatibly is therefore not substantive merely because the source's theorem title mentions embeddings.

## 2. Finite etale objects: the full paid base-change operation

Let X be a finite continuous left G2-set. Its finite etale algebra over F2 is

    B_X = Map_G2(X,E2),

where equivariance means f(gx)=g f(x). This notation uses the usual pointwise operations; the Galois-equivariant function algebra is contravariant in finite sets. Over E2 it becomes E2^X. Pull X back by alpha. The analogous invariant algebra over F1 is B_(alpha*X).

There is a canonical map

    B_X tensor_(F2,j) F1 -> B_(alpha*X),
    f tensor a |-> (x |-> a j(f(x))).

It is an isomorphism. One can check it after the faithfully flat extension F1->E1. Then both sides become E1^X, and the displayed map is the identity under the splitting identifications. The equivariance relation g j=j alpha(g) is exactly the compatibility needed for these identifications. Both sides have F1-dimension |X|. No primitive element for a disconnected etale algebra, independent choice of embeddings for individual factors, or separability hypothesis beyond finite etale descent is missing.

The construction is functorial in X and respects finite disjoint unions, products, equivariant maps, and commuting finite-group actions. Thus it transports finite constant Gamma-torsors split by E2, together with their morphisms, and agrees with ordinary extension of scalars along j|F2. Composition of two source homomorphisms agrees with composition of the reconstructed embeddings in the opposite direction: the composite satisfies the same equivariance relation, and source uniqueness identifies it. This pays coherent transport across a finite diagram and, objectwise, arbitrary diagrams of finite objects.

This is not generally an equivalence. Put H=alpha(G1), a closed open subgroup of G2, and N=ker alpha. Pullback factors as restriction of finite G2-sets to H followed by inflation along G1->H. Inflation is fully faithful, with essential image the finite G1-sets on which N acts trivially. Restriction to H is faithful but need not be full; it can merge isomorphism classes and split connected objects.

For a transitive object X=G2/U, with U open, its pulled-back components are indexed by the finite double cosets

    H \ G2 / U.

For a representative g, the component stabilizer in H is H intersect g U g^(-1), and its degree over F1 is

    [H : H intersect g U g^(-1)].

The sum of these degrees is [G2:U]. Pulling further back to G1 gives stabilizer alpha^(-1)(g U g^(-1)). These formulas account for the entire product decomposition after scalar extension, including nonnormal U. They are the usual orbit decomposition, not a new arithmetic splitting theorem.

## 3. The cocycle and automorphism formulas retain the kernel

Fix a finite constant group Gamma. Choose a geometric point in a Gamma-torsor. Its Galois action is given by a continuous homomorphism rho:G2->Gamma, up to conjugation in Gamma. Pullback is

    [rho] |-> [rho alpha].

Its geometric automorphisms over the base form C_Gamma(rho(G2)); after pullback they form C_Gamma(rho(H)). The latter can be larger. A connected Gamma-torsor corresponds to surjective rho. After pullback its number of connected components is [Gamma:rho(H)], and each component has degree |rho(H)|. This is compatible with the double-coset formula, without asserting that every component is again a Gamma-torsor.

If alpha is surjective, pullback on H1 is injective. Indeed any conjugacy between rho1 alpha and rho2 alpha is a conjugacy between rho1 and rho2 because every element of G2 has a preimage. Its image is exactly the conjugacy classes represented by homomorphisms G1->Gamma killing N. A continuous map killing N descends continuously along the compact Hausdorff quotient G1/N=G2. The property of killing N is conjugacy invariant. Automorphism groups are unchanged in this surjective case.

If alpha is merely open, injection is false even for Gamma=C2. Take F2=Q, F1=Q(sqrt(2)), E1=E2=Qbar and alpha the inclusion G_F1->G_Q. The quadratic torsor Q[s]/(s^2-2) and the split torsor Q x Q are nonisomorphic over Q, but both become split over F1. The source embedding is the identity of Qbar. This is a concrete consequence of ordinary base change, not a counterexample to any pinned theorem.

All of these statements extend by the standard twisted-cocycle formulas to a finite etale group scheme with its coefficient action transported along alpha, but no such generalization is nominated here. The constant case is already sufficient to test compression.

## 4. Strongest classical integration: one generic torsor pays all specializations

Let k be a characteristic-zero field (in particular, a number field), Gamma a finite constant group, and V a faithful finite-dimensional k-representation. Remove the union of the fixed linear subspaces V^g for nonidentity g. The result U is a nonempty Gamma-invariant open, with free action, and U->U/Gamma is a finite etale Gamma-torsor. Its generic fiber is over K=k(V)^Gamma.

This torsor is versal, not just a source of some number-field examples. Here is the standard proof in the form needed for composition. For any extension L/k and any Gamma-torsor T/L, twist V and U by T. The contracted product T times^Gamma V is an L-vector space, by descent of vector spaces; the twisted U is a nonempty open in it. Since L is infinite, it has an L-point. Unwinding this point gives an equivariant morphism T->U, hence realizes T as the pullback of U->U/Gamma at an L-point of the quotient. The same argument works after replacing U by any invariant nonempty open.

Suppose an actual Gamma-equivariant dominant rational compression V --> Y with Y generically free has been constructed. Restrict to an invariant open on which it is defined and lands in the free locus. The preceding twisting argument then applies to every torsor. The image point on Y/Gamma has residue field L0 inside L, with trdeg_k L0 <= dim Y, and the pulled-back generic finite etale family supplies a Gamma-torsor over L0 whose scalar extension is T. Thus

    ed_k(Gamma) <= dim Y.

Conversely, a descent of the generic torsor to a finitely generated subfield K0 of K produces a faithful Gamma-field inside k(V), and hence a rational Gamma-compression of V. Faithfulness retains the full group, not just an orbit count or a quotient. Buhler-Reichstein1997 Lemmas2.2 and2.7 and Theorem3.1 give this field/variety equivalence and independence of faithful representation. Their actual proof includes equivariant interpolation on the regular representation and movement out of an indeterminacy locus. Merkurjev's survey Propositions3.10-3.13 gives the stronger torsor/versal formulation and the twisted-vector-bundle proof. These proofs, not only titles, were read before this note.

Consequently a putative contribution consisting only of 'transport number-field torsors, choose a faithful representation, and use the generic object to treat all of them' is already paid. It proves the classical bound ed_k(Gamma)<=dim V; it does not construct a smaller Y. Likewise, a rational map into a variety with a nontrivial generic stabilizer would not suffice, since it discards part of the torsor data.

The source031 reconstruction can be inserted before or after this scalar-extension construction, but it adds no dimension decrease. For number fields k contained in F, any Gamma-torsor over F has ed_k(T)=0: F itself is an admissible field of definition and trdeg_k F=0. This remains true whether or not the torsor is connected, whether or not its splitting field is large, and whether or not a smaller number field of definition exists. Essential dimension measures transcendence parameters, not absolute degree, discriminant, number of ramified primes, or size of a defining polynomial.

## 5. Explicit generic diagnostics: arbitrary arithmetic fibers do not bound compression

For r>=1 and k a number field, set

    K=k(t1,...,tr),
    L=K(s1,...,sr),  si^2=ti,
    Gamma=(C2)^r.

The squareclasses of the ti are independent: taking the valuation at the divisor ti=0 sends a relation product tj^epsilon_j = square to epsilon_i=0 mod2. Therefore [L:K]=2^r, and Gamma acts independently by changing the signs of the si. In fact L=k(s1,...,sr) is the rational function field of the faithful diagonal r-dimensional representation, and K=L^Gamma. This is its generic torsor. It is not merely an arbitrary faithful action of a group on a low-dimensional variety; it is versal by section4.

Buhler-Reichstein1997 Corollary5.5 and Theorem6.1 already give

    ed_k((C2)^r)=r.

Here k contains the required primitive second root of unity. The actual lower-bound proof was read: Theorem5.3 uses a central order-p subgroup detected by a one-dimensional character, together with the restriction on larger central cyclic subgroups. A valuation along the character hyperplane is nontrivial on any faithful compressed subfield; its residue field loses at least one transcendence parameter. The inertia argument forces the quotient group to act faithfully on that residue field. Repeating for direct products of C2 proves the lower bound r; the diagonal representation supplies the upper bound. None of the character-detection or central-cyclic hypotheses is dropped. This is not a new lower-bound proof.

For any tuple (a1,...,ar) of nonzero elements of a number field F/k, the specialization is the etale algebra

    F[z1,...,zr]/(z1^2-a1,...,zr^2-ar),

a Gamma-torsor even when it is disconnected. Every such torsor has ed_k=0, while the generic one has ed_k=r. Over Q one can choose distinct rational primes ai; the same independent valuations give connected specializations of degree 2^r. Hence even restricting to connected arithmetic examples does not change the comparison.

For r=1 the generic lower bound has an elementary independent check: k is algebraically closed in k(t). A transcendence-degree-zero intermediate field containing k must equal k. If the class of t descended from a in k*, then t/a would be a square in k(t), contradicting its odd valuation at t=0. Thus the generic class has essential dimension1. This is a diagnostic, not a new theorem nominated for the campaign.

The family demonstrates precisely why arbitrarily many successful arithmetic reconstructions, even compatible ones, do not by themselves provide a compression. It is not an impossibility theorem for using arithmetic in essential dimension, and it does not say that every generic descent problem is unsolvable. It identifies the loss in the proposed inference: specialization replaces a transcendental field by an algebraic one. Applying source031 to the latter does not yield an inclusion of a lower-transcendence subfield in the former.

## 6. Could regular Kummer amplification furnish the missing variety?

The source's `lem:quotient-amplification` constructs L/L1 by adjoining square roots of m sets of conjugates. Valuations at selected split primes make their classes independent; the kernel is a sum of m regular F2[R1]-modules. This controls invariant-space dimensions in a larger finite quotient. It does not parametrize all Gamma-torsors in fewer transcendence variables. Inserting the construction into section4 yields particular torsors over algebraic fields, already of essential dimension0, or a new faithful representation with extra coordinates. Neither step supplies a compression.

The strongest apparent alternative is to make the chosen Kummer elements variable and then quotient the resulting parameter space. The independent-variable calculation above shows what that does in the elementary abelian case: it recovers the usual generic diagonal representation, whose r parameters are already incompressible by the primary theorem. This is a fully paid test, not merely the failure of a naive source-title match. For nonabelian groups, an actual lower-dimensional generically free versal target and a dominant equivariant map would still have to be constructed. No such construction was found here. Declaring an unspecified rational map, a finite table of arithmetic realizations, or the minimization defining essential dimension to be the desired operation would restate the question.

The original-history overlap is limited and explicit. r61's entire frozen scope and proof-attempt note were read: its all-injective-endomorphisms target is unchanged and its header reports it classical-primary-paid after Uchida1981. It is not retried. i05's actual cubic Kummer independence and Galois intersection argument was read at lines185-218, with its original target context1-47. Its finite Frobenius/large-factor distribution problem is untouched. OA057/r12's exact scope and candidate1-65 were read: it uses disjoint branch valuations to retain all root orders in a special-orbifold construction. Nothing here weakens, replaces, or claims a new version of that theorem. Other history hits are navigation and do not clear their full archives. These reads occurred before this integrated note.

## 7. What is and is not concluded

Paid: source031 reconstructs the actual unique equivariant field embedding; classical Galois descent transports the whole finite-etale and split-torsor categories with exact kernel, component and automorphism behavior; the classical versal-representation construction handles all field extensions and all torsors; the primary lower-bound argument pays the complete elementary-abelian generic example. Arithmetic specialization does not supply a dimension reduction.

Unpaid: no nonroutine compression of a concrete generic torsor, new versal variety, uniform parameter reduction, or source-dependent essential-dimension calculation was closed. There is not a proof-feasible exact new theorem to freeze. The positive arithmetic transport formulas and the negative specialization diagnostic are routine compositions. They are not offered as findings, technical replacements for old full targets, or universal obstructions.

The disposition is PREFREEZE / no nominee. Transitive primary coverage is incomplete, catalogues were narrow and partly null, and history isolation has explicitly recorded errors and coarse omissions. No exhaustive-family, perfect-isolation or worldwide-priority conclusion follows. All previous scopes/proofs/dispositions and the campaign count remain unchanged; the parent alone integrates and reviews.
