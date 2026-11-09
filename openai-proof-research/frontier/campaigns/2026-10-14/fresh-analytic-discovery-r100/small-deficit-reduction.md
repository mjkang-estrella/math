# Complete small-absolute-deficit analytic reduction

Author supporting assembly, now incorporating the collaborative author proof of the global tensor statement GR below. This is NOT a replacement for the parent-anchored all-deficit scope, a complete candidate, or an independent review. Original calculations and parent author assistance are identified in §9. All tensor and matrix Frobenius norms below are unnormalized sums of squares.

## 1. The global algebraic input and small-deficit conclusion

For a fully symmetric real cubic tensor S on R^m write S_r for its matrix slices and

 R(S)^2 = ||sum_r S_r²-I||F² +sum_(r<s)||[S_r,S_s]||F²,
 O_m = {sum_i u_i^tensor3 : (u_i) an orthonormal basis of R^m}.

**GR (uniform global entrance).** There is one number rho>0 such that, for every m>=1 and every such S,

    R(S)<=rho implies distF(S,O_m)<=1/sqrt(6).

GR is supplied with rho=10^(-6) by the collaborative author proof in fresh-arithmetic-discovery-r67/associativity-correction.md and normalization-and-entrance.md, using channel-reformulation.md. Exact identities and hashes are recorded in §9, and the mechanism is spelled out in §6. These are author proofs, not independent review verdicts. The premise is global: it does not assume S already close to O_m. The source's exact equality classification, fixed-dimensional compactness, and near-orthogonal tensor perturbation results alone do not supply it.

**Author theorem (small absolute deficit only).** Using the pinned source101 inputs and the assembled algebraic proof, there exist absolute constants delta0>0 and C<infinity such that every integer m>=1 and every centered isotropic log-concave density f on R^m with delta=h(f)-m<=delta0 satisfy

    inf_(U in O(m)) W2²(f dx, Law(U(E-1))) <= C delta,        (1)

where E has m independent mean-one exponential coordinates. Restricted supports are included. Constants do not depend on m, f, or Hessian bounds used in approximation.

This conclusion treats only a small absolute deficit. The unchanged full target also requires delta0<delta much smaller than m; that remains separate and is not inferred from (1).

## 2. Conventions and paid source remainder

Let gamma_m be standard Gaussian measure. For a matrix field K define

    C(K)_rij = partial_r K_ij-partial_i K_rj.

This curl vanishes for a **symmetric Jacobian**, in particular a Hessian. It need not vanish for an arbitrary vector-map Jacobian. Its L2 norm is at most twice the full gradient norm. Every change of orthonormal basis below rotates all three tensor indices, including the derivative index.

Set q(a)=phi(a)/Phi(-a), t(a)=-log Phi(-a). Source transport.tex proves 0<q'<1 and q''>=0. In fact q''>0: its survival-function submultiplicativity is strict for u,v>0 because the hazard q is strictly increasing. Integration gives Var(X_a)<(E X_a)², and q''=q(d²+qd-1)>0.

For a smooth density with positive finite lower/upper potential-Hessian bounds, source tr:normalization supplies symmetric P>0 and a smooth Brenier gradient F transporting gamma_m to P applied to the density. Put

    J=DF, A=q^(-1)(J), E A=0,
    X_r=E[x_r A], L(x)=sum_r x_r X_r, Y=A-L,
    B=sum_r X_r², T_rij=(X_r)_ij.

T is symmetric in its LAST TWO indices only. The entropy gap is affine invariant. Source mat:entropy-smooth and the retained final chaos slack give

    ||Y||2²<=1000 delta,
    ||gradient Y||2²<=2000 delta,
    sum_i omega(lambda_i(B))<=2000 delta.                    (2)

The gradient estimate uses the ACTUAL final proof matrix.tex526–590: at chaos degree d>=2, retain the coefficient

    k_d=1/500+(d-2)(1+68/d)/50 >=d/1000.

For d=2 this is equality; for d>=3 already (d-2)/50>=d/1000. Source's signed deficit is -2delta. This is paid proof reuse, not a new entropy theorem.

The weight is exactly

 omega(lambda)=3(lambda-1)²/(37+3lambda)
   *[3/20+(49/100)*37/(37+3lambda)]
   *min(13/100,32/(25sqrt(lambda))).

Let eta=inf{omega(lambda):lambda>=0, lambda outside (1/2,3/2)}. Continuity, its sole zero at1, and its growth to infinity imply eta>0. If delta<=eta/4000, (2) places every eigenvalue in (1/2,3/2). On [1/2,3/2], direct substitution bounds omega(lambda)>=(lambda-1)²/200. Consequently

    ||B||op<=2,  ||B-I||F<=sqrt(400000) sqrt(delta).           (3)

No sum over dimensions has been bounded by a factor m.

## 3. The matrix column estimate and strong curl

Use Fourier convention q''(s)=integral alpha(t) exp(its)dt and set M=integral|alpha(t)|dt<infinity. To justify finiteness, q'',q''' belong to L2(R). On the negative tail this follows by differentiating phi(a)/Phi(-a), with denominator at least1/2. On the positive tail,

 q(a)=a/F0(a^-2), F0(u)=integral_0^infinity exp(-v-u v²/2)dv.

Dominated differentiation makes F0 smooth at u=0 with all finite derivatives. Taylor's formula with differentiated remainders gives q(a)=a+a^-1+O(a^-3) through three derivatives, hence q''=O(a^-3), q'''=O(a^-4). Plancherel and Cauchy–Schwarz with weight (1+t²)^-1 give alpha in L1. Thus M is an absolute finite number.

For symmetric H,D and symmetric matrices V_r with sum V_r²<=bI, finite-matrix spectral calculus and the second-divided-difference simplex formula give

    (sum_r ||D²q(H)[D,V_r]||F²)^(1/2)
        <= M sqrt(b)||D||F.                                  (4)

Indeed, the representation is the integral against alpha(t)dt of the two products U D V V_r W and U V_r V D W over the time simplex of area1/2, where the displayed U,V,W are common unitary functions of H. Each product has family norm at most sqrt(b)||D||F, since, for example, sum_r||D V V_r||F²=tr(D*D V B V*)<=b||D||F². Minkowski and the two simplex volumes prove (4). It can also be obtained by twice differentiating the integrated exponential formula for q; no distributional Fourier transform of q itself is required. Absolute convergence follows from alpha in L1 and finite matrices.

Integrating (4) along H=L+sY and using Frobenius contraction of Dq gives

 ||gradient(q(L)-q(A))||2
    <=M sqrt(||B||op)||Y||2+||gradient Y||2.

The chain rule is legitimate for the smooth normalized field; its weak extension follows by local Sobolev approximation and the same bounds. Since q(A)=DF is symmetric, its chosen curl vanishes. With

    a0=2sqrt(2000)(1+M),

we obtain

    ||C(q(L))||2<=a0 sqrt(delta).                            (5)

Also ||q(L)-J||2<=sqrt(1000 delta) by source spectral Lipschitz contraction.

## 4. Opposite-input symmetry extraction

This step is parent author assistance, checked here. Write U_rij=T_rij-T_irj and c1=min_[−4,4]q'>0. At x diagonalize L(x), and use the SAME basis at -x; its eigenvalues there are the negatives. For a triple of indices put s=T_rij, z=T_irj and

 alpha=q[a_i,a_j], beta=q[a_r,a_j],
 alpha'=q[-a_i,-a_j], beta'=q[-a_r,-a_j].

The two curl entries in this basis are

    alpha(s-z)+(alpha-beta)z,
    alpha'(s-z)+(alpha'-beta')z.

Convexity of q makes alpha-beta and alpha'-beta' have opposite signs (or zero). A convex combination therefore cancels z, leaving a coefficient of s-z at least c1 whenever all three eigenvalues have absolute value<=4. If both differences vanish either equation suffices. Jensen gives, on this spectral triple block,

    |U_rij|² <= (|C(q(L))(x)_rij|²
                    +|C(q(L))(-x)_rij|²)/c1².                (6)

The coefficients U are constant in fixed coordinates. If P4(x) is L(x)'s spectral projection onto [-4,4], then E L²=B and (3) imply

 E||P4(x)^tensor3 U||F²
    >=(1-3||B||op/16)||U||F² >=||U||F²/2.

The bound uses the union estimate for the three commuting tensor-factor projections; each high-index contribution is at most E||L acting on that index U||²/16. There is no random eigenvector differentiation. Integrating (6), using Gaussian symmetry and (5), proves

    ||U||F<=2a0 sqrt(delta)/c1.

Let S be the FULL orthogonal symmetrization of T. For a last-two-symmetric tensor the exact projection identity is

    ||T-S||F²=||T-swap12(T)||F²/3=||U||F²/3.

It follows either by expanding the three distinct permutations or by noting their equal pairwise inner products. Set e0=2a0/(sqrt(3)c1). Then

    e:=||T-S||F<=e0 sqrt(delta).                              (7)

## 5. Transfer to the symmetric tensor and commutator control

Let S_r be the slices, L_S=sum x_r S_r, B_S=sum S_r². Matrix row/column Cauchy–Schwarz gives

    ||B_S-B||F <=2sqrt(||B||op)e+e².                          (8)

For the linear term, regard the family X_r as a block row and the errors S_r-X_r as a block column; the row operator norm is sqrt(||B||op), and the column Hilbert–Schmidt norm is e. The quadratic term is bounded by e².

Require additionally delta<=1 and e0 sqrt(delta)<=1/10. Then (3), including the sharper B<=3I/2, and (8) imply ||B_S||op<2. Define

    b0=sqrt(400000)+2sqrt(2)e0+e0².

Thus ||B_S-I||F<=b0 sqrt(delta). Full curl transfer is also valid: apply (4) to L_S-L and the original X_r, then add Dq(L_S)[S_r-X_r]. It gives

 ||C(q(L_S))||2 <=[a0+2(1+M sqrt(2))e0]sqrt(delta).            (9)

In particular the transfer introduces no dimension loss. For the commutator estimate below it suffices to retain the simpler zeroth-order comparison

    ||q(L_S)-J||2 <=j0 sqrt(delta), j0=sqrt(1000)+e0.          (10)

Here J remains a SYMMETRIC weak Jacobian/Hessian, so its r,i curl vanishes.

For completeness, the global conditional commutator test is proved next. For ANY fully symmetric S with ||B_S||op<=2 put K=q(L_S) and

    Phi_rij =sum_a[(L_S)_ia S_raj-(L_S)_ra S_iaj].

This is antisymmetric in r,i and linear in Gaussian x. Its coefficient slices are commutators, up to an irrelevant sign convention, so

    C0²:=E||Phi||F²=sum_(r,i)||[S_r,S_i]||F².

Rotating all indices into an eigenbasis of L_S, full symmetry and the divided-difference derivative formula give EXACTLY

    C(K)_rij=q[a_i,a_r,a_j] Phi_rij.                          (11)

Let c2=min_{a,b,c in [-6,6]} q[a,b,c]>0. Strict positivity follows from q''>0 and the simplex representation. For any linear Gaussian tensor Z=sum x_r Z_r and L_S acting on one tensor index, Wick's formula yields

    E||L_S Z||²<=3||B_S||op sum_r||Z_r||².                    (12)

The three pairings respectively give sum_(r,s)||S_r Z_s||², ||sum_r S_r Z_r||², and sum_(r,s)<S_r Z_s,S_s Z_r>. The first two are bounded by ||B_S||op sum||Z_s||² using the column/row operator norms; the third is bounded by the first using Cauchy–Schwarz. Passive tensor indices do not affect these estimates.

The Phi energy in triples with at least one eigenvalue outside [-6,6] is therefore at most 9||B_S||op C0²/36<=C0²/2. From (11), positivity everywhere, and positivity c2 on the retained block,

    E<C(K),Phi>>=(c2/2)C0².                                 (13)

Write delta_r=x_r-partial_r for the Gaussian adjoint. Since Phi is antisymmetric,

    (D*Phi)_ij=2sum_r delta_r Phi_rij.

The Gaussian quadratic-chaos identity implies ||D*Phi||2²<=8C0²: for Phi_rij=sum_s Z_rijs x_s, the polynomials delta_r x_s=x_rx_s−1_(r=s) have quadratic variance at most twice the coefficient Frobenius sum. Integration by parts against K-J, whose J curl vanishes, and (10) now give

    (c2/2)C0² <=sqrt(8)j0 sqrt(delta) C0.

If C0=0 there is nothing to divide; otherwise cancel it. Compact cutoffs justify integration by parts: K and its first derivatives have Gaussian polynomial growth, Phi is polynomial, J is L2, and the Gaussian adjoint cutoff errors tend to zero in L2. Equivalently approximate Phi in the adjoint graph norm. This never differentiates the L2 error itself. Consequently

    (sum_(r<s)||[S_r,S_s]||F²)^(1/2)
        <=4j0 sqrt(delta)/c2.

Set D0=(b0²+16j0²/c2²)^(1/2). We have proved

    R(S)<=D0 sqrt(delta).                                   (14)

All constants in (14) are absolute, before GR is used.

## 6. Global correction followed by the local algebra estimate

Here is the quantitative global correction supplied by the r67 author modules. For a fully symmetric tensor write a for the Hilbert–Schmidt associator norm and beta=||B-I||F; then a²=2 sum_(r<s)||[S_r,S_s]||F². The reshuffling identity ||K-JJ*||HS=a, with K(E)=sum S_r E S_r and J the tensor flattening, makes K bounded below by -a. Symmetric congruence on all three modes has Gram derivative E B+B E+4K(E). For beta,a<=10^(-3), this derivative has inverse norm at most1. The r67 second-derivative bound64 and contraction on ||E||F<=2beta give an exact B=I normalization N, with ||N(S)-S||F<=8beta and a(N(S))<=a(S)+40beta. All norms and constants are independent of dimension.

At B=I, the Hochschild homotopy correction replaces S_abc by U_abc=Tr(S_a S_b S_c). The explicit associator identity and mixed Gram contraction in associativity-correction.md give ||U-S||F<=a, a(U)<=4a² and ||B(U)-I||F<=2a². Normalize U again. Hence a_next<=84a² and the displacement is at most2a. Starting at R<=rho=10^(-6), initial normalization costs8R and leaves a0<=42R. Iteration halves a at each step, so its total subsequent displacement is at most4a0<=168R. The limit is fully symmetric, B=I, and associative. Its real symmetric slices commute, so simultaneous orthogonal diagonalization and full tensor symmetry leave only diagonal cubic coefficients; B=I forces each coefficient to be plus or minus1, absorbed into basis signs. Thus dist(S,O_m)<=176R<1/sqrt(6). This is a convergent correction in each fixed tensor space with uniform constants, not a compactness argument across dimensions. The cited modules contain the contraction, index identities, and Hilbert–Schmidt contraction estimates used here.

If delta<=rho²/D0², this proven author-level GR puts S within 1/sqrt(6) of O_m. The following already proved local estimate then applies:

    distF(S,O_m)<=sqrt(2) R(S).                              (15)

Its proof is included to expose the uniformity. Rotate a closest orbit point to Q0=sum e_i^tensor3 and write S=Q0+H. Orthogonality to the orbit tangent says H_iij=H_ijj for i<j. The squared normal norm is sum H_iii²+(3/2)sum_(i<j)(H_iij+H_ijj)²+6sum_(i<j<k)H_ijk². Linearizing B−I and the unordered commutator family gives squared norm

    4sum H_iii²+4sum_(i<j)(H_iij+H_ijj)²
           +12sum_(i<j<k)H_ijk² >=2||H||F².

The combined quadratic remainder is at most sqrt(3)||H||F², using ||sum H_r²||F<=||H||F² and sum_(r<s)||[H_r,H_s]||F²<=2||H||F⁴. Thus R(S)>=sqrt(2)d−sqrt(3)d²>=d/sqrt(2) when d<=1/sqrt(6). This proves (15).

Choose Q=sum_i u_i^tensor3 with ||S-Q||F<=sqrt(2)D0 sqrt(delta). Let U have columns u_i. Its pencil is L_Q(x)=U diag(U^t x)U^t, and its Gaussian transport is the explicit centered map

    F_Q(x)=U(t(U^t x)-1),  D F_Q=q(L_Q).

F_Q has mean0, covariance I, and law U(E-1). Scalar q Lipschitz and Gaussian orthogonality give

 ||DF-DF_Q||2 <=||Y||2+||T-S||F+||S-Q||F
      <=k0 sqrt(delta),
 k0=sqrt(1000)+e0+sqrt(2)D0.

Center F if necessary. Gaussian Poincare, componentwise and summed, yields

    E|F-F_Q|²<=k0² delta.                                   (16)

No dimension factor enters Poincare. Both maps lie in H1(gamma): F has finite second moments and the source derivative bounds for each fixed smooth law; F_Q has exponential-product second moments and q's linear growth.

## 7. Return to isotropic coordinates

For a centered isotropic original X, the Gaussian realization X=P^(-1)F has that law. F_Q is also centered isotropic. Parent's normalization coupling lemma says

    E|X-F_Q|²<=4E|PX-F_Q|².

To prove it, diagonalize symmetric P>0 orthogonally. In each coordinate both X_i and (F_Q)_i have L2 norm1; reverse triangle gives |p_i−1|<=||p_iX_i−(F_Q)_i||2. Ordinary triangle then gives ||X_i−(F_Q)_i||2<=2||p_iX_i−(F_Q)_i||2. Square and sum. This is valid with arbitrary dependence and needs no lower bound on P or upper bound on P inverse. Combining with (16) proves (1) for smooth laws, with C=4k0².

## 8. Thresholds and all nonsmooth densities

Define

 delta_star=min{eta/4000,1,1/(100e0²),rho²/D0²},
 delta0=delta_star/2, C=4k0².

All are absolute; delta0 is positive with the explicit rho=10^(-6). The smooth proof works throughout delta<=delta_star.

For a fixed dimension and arbitrary centered isotropic log-concave f with delta<=delta0, apply the ACTUALLY READ source geo:approximation. It gives smooth strongly convex f_j, means a_j->0, covariance C_j->I, entropy h(f_j)->h(f), and common exponential-tail domination. Let X_j=C_j^(-1/2)(Y_j-a_j), Y_j~f_j. These laws are isotropic and remain in the smooth class, with Hessian bounds allowed to depend on j. Their entropy deficits converge to delta; hence delta_j<=delta_star eventually. Weak convergence plus second-moment convergence, or directly the common tails and converging affine maps, gives W2(Law(X_j),f dx)->0.

Apply the smooth estimate with the SAME C to these X_j. For this fixed m, compactness of O(m) supplies a convergent subsequence of their minimizing/near-minimizing U_j. If U_j->U, coupling to the same E gives E|(U_j−U)(E-1)|²=||U_j−U||F²->0. The W2 triangle inequality passes the bound to f. This includes delta=0 and arbitrary restricted supports. Fixed-dimensional compactness here only passes a previously uniform estimate to a limit; it does not produce the uniform constant. No uniformity of the source approximation over m or over all f is needed.

## 9. Attribution, reading limits, and outstanding full-scope obligations

Source inputs: tr:normalization, tr:q-properties, mat:entropy-smooth and its final proof526–590, spectral Lipschitz lemma, geo:approximation (read in full). The full source normalization proof and scalar certificate have not been audited; their stipulated results are used. Exact odeco classification is classical supporting algebra (Boralevi–Draisma–Horobet–Robeva, actual Section3.1 read), and does not imply GR.

Parent author assistance: opposite-input symmetry extraction, exact symmetrization bookkeeping, and normalization coupling; parent also independently derived the Fourier column argument. Original author modules: retained-gradient observation, Fourier column proof, conditional symmetric curl/Wick test, local algebra correction, and their assembly. All are collaborative author work, not independent review. Parent support record is discovery-analytic-r100-parent/quantitative-curl-support.json; source and primary receipt files record retained identities.

The r67 collaborative algebra proof removes the former unproved GR premise at author level. It does NOT prove the intermediate/all-deficit part of the frozen target, certify novelty, supply an independent review, or nominate a small-deficit substitute. The r102 assistant and this author continue the all-deficit obligation. The frozen scope-status.json is unchanged.

Exact r67 dependencies, read in full by this author before integration:

- channel-reformulation.md: SHA256 dbff22dc94c0038d8e1f554e0859c65641fd23de1056a4bd3b79ec6384847c97.
- associativity-correction.md: SHA256 18c86f972ab68443f918bc9ad0f2a7cfd0ca8082059a63eecf0b981d41a2e0bb.
- normalization-and-entrance.md: SHA256 3960aa42c48ea1bde2b4d5dffecd0c674d6c7ec603d6f1c1739c8ef9928743db.

All paths are relative to sibling fresh-arithmetic-discovery-r67/. The arithmetic author supplied the associativity correction and iteration; the parent supplied and corroborated the symmetric normalization derivative and dimension-free bounds. Classical Hochschild/Bianchi machinery and exact odeco identification retain their original attribution. The previous version of this file, SHA256 73857ebb4dc5427db397f2bf44aa9c44373258c261d060fcbdc55bd335865add, explicitly left GR conditional. This update records the later author proof and does not backdate its availability.
