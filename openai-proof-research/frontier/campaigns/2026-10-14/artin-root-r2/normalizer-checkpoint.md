# Complete normalizer argument checkpoint

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Status: proposed complete proof of unchanged full R, conditional only on the stipulated pinned theorems and the explicitly cited published/preprint primary retraction interface. Not independently reviewed or counted. Contribution is an elementary source composition, not a self-certified substantial discovery.

Let A be any original finite-rank Artin group, theta:A->W the Coxeter map, Q=A_I, and N=N_A(Q). Digne--Godelle--Michel, arXiv:2407.07459v2, Lemma 2.7 (TeX label mult2), supplies a set retraction rho_I:A->Q such that for any a with theta(a) in N_W(W_I), there is a diagram automorphism alpha_a of Q with

    rho_I(a b)=rho_I(a) alpha_a(rho_I(b))  (every b in A).

This is an arbitrary-type statement. It is not an assumed arbitrary-type Artin ribbon-generation theorem. The primary TeX at lines 858--874 agrees with the HTML; its proof uses Proposition 2.6(7),(8), i.e. the established product formula and the Coxeter ribbon representative. Definition 1.14 supplies the permutation giving alpha_a. In particular alpha_a is bijective and fixes 1. The source only says rho_I is a set retraction globally; no global homomorphism is asserted.

Every a in N meets the image hypothesis, because theta(a) W_I theta(a)^-1 = theta(a Q a^-1)=W_I. Define

    K={k in N:rho_I(k)=1}.

1. K is a subgroup. Identity belongs. If k,l in K then rho_I(kl)=1 alpha_k(1)=1. If k in K, apply the product formula to k k^-1 to get 1=alpha_k(rho_I(k^-1)); injectivity gives rho_I(k^-1)=1. Products and inverses stay in N.
2. K intersects Q trivially because rho_I restricts to the identity on Q.
3. For n in N put q=rho_I(n) and k=q^-1 n. Then q in Q, k in N, and Proposition 2.6(7), applied to q^-1, gives rho_I(k)=q^-1 rho_I(n)=1. Thus n=qk. (Equivalently use Lemma 2.9(1).)
4. Restrict the quotient homomorphism N->N/Q to K. It is injective by (2), surjective by (3), and a homomorphism by (1). Hence N/Q is isomorphic to the actual subgroup K of A. Pinned torsion-freeness of A therefore implies torsion-freeness of N/Q. This inference uses the newly proved embedding, not torsion-freeness of an arbitrary quotient.

Conjugation gives the same for every parabolic Q. Now if g^m in P and m>0, let Q=PC(g^m). Pinned arbitrary intersections make Q parabolic and Q<=P. Conjugation equivariance of PC follows by conjugating its defining intersection. Since g centralizes g^m it normalizes Q. Thus gQ has finite order in N_A(Q)/Q, which is torsion free by (4). Consequently g in Q<=P. Negative powers reduce by inversion in P; m=+/-1 are included. Empty S, Q=1 and Q=A are also included. This proves the full original R relative to the stated inputs.

No layer, cross-Hom, direct-sum null vanishing, CAT(0) metric, unique-root theorem, or finite-index parabolicity inference is used. Every r11 method objection remains valid. No manuscript or Lean package is authorized or produced.
