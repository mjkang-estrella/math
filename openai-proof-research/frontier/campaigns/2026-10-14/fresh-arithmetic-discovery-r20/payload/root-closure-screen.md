# Artin root closure: full-scope screen, unresolved

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0. The stipulated upstream revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No upstream truth audit is attempted.

## Exact target and disposition

For every finite Coxeter matrix M, allowing arbitrary finite labels and infinity, let A=A_M. For every parabolic P=a A_X a^{-1}, every g in A and every integer n>=1, prove g^n in P implies g in P. The cases P={1}, P=A, periodic words, all ranks and all types are included. Equivalently PC(g^n)=PC(g), with PC defined using the stipulated full parabolic intersection theorem. There is no spherical, FC, even, two-dimensional or other restriction. This is the target screened, not a proved/frozen nominee. No runtime claim is attached: the intended result is structural, not an algorithm.

Status: unresolved. The potential new step is finite-orbit rigidity for the source's relative framing detectors. This packet proves an obstruction to a generic direct-sum extension of one source lemma, not an obstruction to the target theorem. It contributes zero campaign count.

## Exact source interface

Pinned Parabolic intersections in Artin groups: cat:action gives invertible bimodule twists B_x and preserves bigraded Hom cohomology. cat:family gives E_L(x)=B_x P_(f,L), with each member indecomposable and connected minimal color support. The frame f has label2 with X and label3 with S minus X; the construction also retains an auxiliary vertex o. stab:initial / stab:single-detector identify the initial stabilizer with A_X. stab:parabolic identifies H(Y,x), the stabilizer of the single transported label family E_L(x), as a parabolic. The proof uses rank induction, ht:minima and ht:containment, and the null-layer obstruction null:obstruction.

Crucially null:hom / null:middle applies to Y^l(E_L(z)) and Y^k(E_H(z)) with the SAME z. Autoequivalence identifies their actual Hom cohomology with the framing-projective Hom, whose only diagonal dimensions are already exhausted by identity and token. Hence all permanent length-one classes vanish. null:injection separately uses actual Hom vanishing in negative total degree. Neither statement is made for mixed E_L(x),E_H(y).

## Conditional finite-orbit mechanism

Conjugate P to A_X. If g^n is in A_X, then B_g permutes the finite set Omega of isomorphism classes of the complete label families E(g^i), 0<=i<n. Define H to be the subgroup of A preserving this finite set, and K its pointwise stabilizer. Then g is in H, K is normal of finite index in H, and K is the finite intersection of conjugates of A_X, so K is parabolic by the stipulated source. If one could prove that H itself is parabolic, then the standard additional fact that a proper parabolic has infinite index in a containing parabolic would give H=K. Thus g fixes E(1), implying g in A_X.

This is a conditional reduction, not a proof of H being parabolic. Its supporting infinite-index fact follows from two already established primary interfaces. By the parabolic-inside-parabolic theorem (Blufstein--Paris arXiv:2204.05142v2 Theorem1.1; also Hagen--Martin--Sartori Theorem4.15), conjugate a proper included parabolic to A_Z inside A_Y, with Z a proper subset of Y. Choose s in Y minus Z. The exponent-sum map sending every standard generator to1 shows that s^m is geodesic of length |m|. Charney--Paris arXiv:1401.7634v1, Theorem1.2, states that EVERY geodesic for an element of A_Z uses only Z letters. Thus s^m is not in A_Z for m nonzero, and the cosets s^k A_Z are pairwise distinct. This proves the required infinite index and leaves exactly the new H-parabolic claim unpaid. These supporting deductions are not nominees.

The hoped-for new argument was to apply harmonic heights to the direct sum over Omega. This makes the height invariant under H and retains nonnegative finite generator arrays. However mixed Hom blocks appear, so the null-layer proof cannot simply be reused. Applying heights separately avoids mixed Hom but creates a different unpaid obligation: simultaneous minima and connected minimum paths for a finite tuple. The source's connectivity theorem is for a single transported family; it does not give connectivity of intersections of its minimum loci. The spherical no-chain argument uses an indecomposable member and could potentially be retained componentwise. That observation does not repair the missing null-layer interface.

## A concrete failure of the generic mixed-family Hom claim

Use the actual source algebra for S={s}, X=empty, with framing vertices f and o. All three pairwise labels are3, and there is one fusion label. Keep o; this is not a replacement two-vertex algebra. The projective subcalculation involves only s,f. Let a:P_s->P_f be the length-one arrow and t_s the token. Products of total positive path length at least3 vanish. Internal placement is denoted <u>, and [1] lowers cochain placement by1.

Set T=B_s. The evaluation cone gives

E0=P_f,
E1=T P_f=[P_s<1> in degree -1 --a--> P_f in degree0].

Before cancellation, T E1 has degree -2 terms P_s<1> plus P_s<3>, degree -1 terms P_s<1> plus P_s<1>, and degree0 term P_f. With the degree -1 terms ordered as Z tensor E1 and M_s tensor P_f, the two differentials are

D_-2 = [[1,t_s],[-1,0]],   D_-1=[a,a].

The identity pair cancels. Equivalently change the degree -1 coordinates from (v,w) to (v,w+v), and change the degree -2 unit coordinate u to u+t_s r. This isolates an identity differential and leaves

E2=T^2 P_f=[P_s<3> in degree -2 --t_s--> P_s<1> in degree -1 --a--> P_f in degree0].

This model is minimal, since both remaining differentials are radical. Its levels (cochain plus internal placement) are1,0,0. Consequently Y^1(E2) is the single projective P_s<3> in degree -2, while Y^0(E0)=P_f in degree0. Their linear Hom has a one-dimensional length-one space and zero differential, so

h_1(Y^0(E0),Y^1(E2))=1.

Its bidegree is (n,v)=(-2,4), satisfying n+v=1-0+1=2. The presence of o does not alter this off-diagonal arrow space. This refutes the proposed extension of null:middle to arbitrary finite sums of transported families. It does NOT contradict null:middle, whose common-transport hypothesis is absent, and it does NOT give a finite periodic orbit: {E0,E2} has not been shown to be an orbit of a finite-order permutation. It is not a counterexample to root closure. Exact finite algebra diagnostics check the cone cancellation and the nonzero middle class.

Finite periodicity could still supply a new positivity/vanishing statement or a different height construction, but no such implication has been proved here. The finite orbit condition only gives B_g^n E(1) isomorphic to E(1); it does not identify Hom(E(g^i),E(g^j)) with Hom(E(1),E(1)) when i-j is not divisible by the orbit length.

## A second exact reformulation, not a solution

Root closure for every parabolic is equivalent to torsion-freeness of N_A(Q)/Q for every parabolic Q, assuming parabolic closures exist. Forward: if h normalizes Q and (hQ)^n=Q, root closure gives h in Q. Reverse: put Q=PC(g^n). Conjugation-equivariance of PC and commutation of g with g^n show g normalizes Q. Since g^n is in Q, quotient torsion-freeness gives g in Q, hence in every parabolic containing g^n. This demonstrates precisely why assuming torsion-freeness of the normalizer quotient would simply replace the missing target with an equivalent one.

## What the primary pure retraction does resolve

Write theta:A->W for the standard Coxeter quotient and CA=ker(theta). Blufstein--Paris arXiv:2204.05142v2, Proposition2.3, constructs a set-retraction pi_X:A->A_X whose restriction CA->CA intersect A_X is a group homomorphism. Lemma2.4 proves: for beta in CA and alpha in A_X, if beta alpha beta^{-1} is in A_X, then it equals pi_X(beta) alpha pi_X(beta)^{-1}. The complete proof of these statements and their Theorem1.1 was read; this is not a claim that the odd-label deletion retraction exists.

The stipulated K(pi,1) theorem gives torsion-freeness of A, as explicitly recorded among its consequences. Consequently the following SUPPORTING partial result follows. It is not a substitute nominee.

**Relative-pure support lemma.** Let Q=A_X, g in N_A(Q), n>=1, and g^n in Q. If theta(g) is in W_X, then g is in Q.

Proof. Choose u in Q with theta(u)=theta(g). Set beta=g u^{-1}. Then beta is pure and normalizes Q. Put b=pi_X(beta) in Q intersect CA and c=b^{-1} beta. By Lemma2.4 applied to every alpha in Q, c centralizes Q. Also c is pure and pi_X(c)=1 by the homomorphism property. Thus g=b c u=h c with h=b u in Q, and c commutes with h. Hence c^n=h^{-n}g^n lies in Q. It is pure, so the retraction identity and homomorphism property give c^n=pi_X(c^n)=pi_X(c)^n=1. Torsion-freeness forces c=1, and g=h is in Q. QED.

For arbitrary parabolic P containing g^n, set Q=PC(g^n), conjugate it to standard position, and observe that g normalizes Q. If g is pure, then the lemma applies (purity is conjugation invariant). Therefore the full root-closure target is proved by these interfaces for pure roots, but the unrestricted root is not settled.

More exactly, theta induces a homomorphism

N_A(A_X)/A_X -> N_W(W_X)/W_X.

The kernel is torsion-free by the relative-pure support lemma. If an element of finite order d in the first quotient existed, its image in the Coxeter quotient would have exactly order d: any smaller image order would leave a finite-order element in the torsion-free kernel. Thus the remaining obstruction is genuinely nontrivial finite-order Coxeter-normalizer motion. It is not legitimate to conclude that the whole quotient is torsion-free from its kernel. The target quotient is not assumed to be an Artin group.

Even the rank-two commuting Coxeter example shows that the Coxeter target can have torsion: W=<s,t | s^2=t^2=1,st=ts>, X={s}, and tW_X has order2. Its Artin lift A=Z^2 has torsion-free quotient A/A_X=Z, so this example is NOT a counterexample; it illustrates exactly why torsion in the Coxeter quotient must be ruled out at the level of possible finite-order lifts, not by falsely asserting that the Coxeter quotient is torsion-free. No such no-lift proof for arbitrary M is completed here.

## Primary operations and what remains unpaid

Antolin--Foniqi, arXiv:2305.17292v1, Theorem1.3 and complete Section3, prove root closure for even Artin FC-type groups. Their induction on the number of labels>2 and number of vertices uses a visual splitting when there is a missing edge, and for a universal vertex v uses a retraction rho_v and a kernel presented as a new EAFC Artin group of smaller complexity. Lemma3.4 controls parabolic closure inside that kernel. These are substantive operations beyond mere intersection closure. The retraction sending all other generators to1 cannot be transported to an arbitrary odd-labelled edge: xsx=sxs would map to x^2=x, impossible in the infinite cyclic target. This is a failure of that operation, not a counterexample to the full root-closure claim.

Hagen--Martin--Sartori, arXiv:2503.20620v1 and the corresponding passages of v2, Definition4.17 lists normalizer structure separately from the intersection property. Definition5.9 / Theorem5.10 treat root closure as additional structure and quote it in the two-dimensional case. The original Godelle proof is not read here. Their Lemma5.11 uses root closure to equate Fix(g) and Fix-infinity(g); it cannot supply root closure from the intersection theorem.

The center conjecture is already paid: Jankiewicz--Schreve, arXiv:2201.06591v1, Theorem3, derives it from K(pi,1); the pinned K(pi,1) introduction itself includes this consequence. The parabolic source introduction also already includes arbitrary intersections with finite witnesses, parabolic closure, membership/word problems, and non-clique acylindrical hyperbolicity consequences. None is nominated.

Convexity does not by itself give the required conclusion for arbitrary roots. It immediately handles a positive word g because a positive representative of g^n is geodesic by exponent sum, but the target includes arbitrary signed words. A torsion-free abstract counterexample to the implication "convex subgroup implies root-closed" is Z with generating set {a,a^2}: the subgroup generated by a^2 is convex for that generating set, but a^2 lies in it and a does not. This is not an Artin counterexample and is not used to dispute any source theorem. A suitable general straightening of cyclic geodesics would be an additional unproved Artin-specific input; no such statement is assumed.

The unchanged full target needs a genuinely new finite-orbit rigidity theorem, or an argument excluding finite-order lifts of nontrivial finite Coxeter-normalizer motion, or another mechanism that handles arbitrary labels. No formal proof interface can honestly treat that theorem as established. No manuscript, release candidate, or new-to-literature assertion is produced.
