# Symmetric normalization and uniform global entrance

AUTHOR DRAFT for collaborative checking, not an independent gate. This continues associativity-correction.md and preserves every dimension in the entropy candidate. No prescribed unit or initial proximity to an orthogonal tensor is assumed.

Proposed conclusion: for every m≥1 and fully symmetric real cubic T on R^m,

R(T)≤10^(-6)  implies  dist_F(T,O_m)≤176R(T)<1/sqrt6.     (GR)

Here R²=beta²+C, beta=||B−I||F, C=Σ_(r<s)||[X_r,X_s]||F² and O_m={Σu_i^tensor3: (u_i) orthonormal}. The already established local lemma would then improve the conclusion to dist≤sqrt2 R on this same residual range. The proof below is a direct global correction, not an appeal to fixed-dimensional compactness.

## 1. Exact normalization with dimension-independent bounds

Let a=||A(T)||HS=sqrt(2C). Suppose beta≤10^(-3) and a≤10^(-3). For symmetric E, put P=I+E and T_P(x,y,z)=T(Px,Py,Pz). Define F(E)=B(T_P)−I.

The derivative at zero is

L(E)=DF(0)[E]=EB+BE+4K(E), K(E)=Σ_i X_i E X_i.             (1)

It is selfadjoint on the Hilbert space of symmetric matrices. By channel-reformulation.md, K differs by HS norm a from the positive superoperator S=JJ*. Therefore its smallest eigenvalue is at least −a. Consequently

<E,L(E)>≥[2(1−beta)−4a]||E||F²≥||E||F²,
||L^(-1)||op≤1.                                         (2)

No inverse involving the dimension is used.

For explicit second derivative bounds, write b=||B(T)||op≤1.1. If ||E||op≤r≤0.1 and p=1+r, then

||D T_P[H]||F≤3p²sqrt b ||H||F,
||D² T_P[H,K]||F≤6p sqrt b ||H||F||K||F,
||J_(T_P)||op≤p³sqrt b.

Each single-mode action is bounded by ||H acting on T||F²=tr(H^t H B)≤b||H||F²; the other mode actions cost their operator norms. Thus no estimate uses ||T||F≈sqrt m. Differentiating the Gram matrix gives

||D²F(E)[H,K]||F≤30p⁴ b ||H||F||K||F≤64||H||F||K||F.     (3)

For the Gram products, use ||M*N||F≤||M||op||N||F for a term involving the unperturbed flattening, and the Frobenius-product bound for the two first derivatives.

Consider the closed Frobenius ball ||E||F≤2beta and the map

G(E)=−L^(-1){F(0)+F(E)−F(0)−L(E)}.

By(3), its norm is at most beta+32||E||F²≤beta+128beta²≤2beta. Its Lipschitz constant on the ball is at most128beta<1. The contraction theorem gives a fixed point E with F(E)=0. This is a finite-dimensional complete ball for each m, with the same constants in every m. Also P is positive definite, since ||E||op≤0.002.

Let N(T)=T_(I+E). Integrating the first derivative bound yields

B(N(T))=I,
||N(T)−T||F≤8beta.                                      (4)

For any fully symmetric H, expansion of the two associator compositions gives

||A(T+H)−A(T)||HS≤4sqrt b ||H||F+2||H||F².

Each linear contraction uses one flattening of T with operator norm sqrt b and one flattening of H with HS norm ||H||F. This avoids the false bound ||H⊗I||HS=sqrt m||H||HS. From(4), beta≤0.001, and b≤1.1,

a(N(T))≤a(T)+40beta.                                    (5)

This proves the exact normalization interface needed between correction steps. Existence, not a unique canonical normalization across all inputs, is sufficient.

## 2. Quadratic iteration at exact B=I

First normalize the initial tensor T, whose R≤10^(-6). Its beta≤R and a≤sqrt2 R meet the lemma's premises. Write T0=N(T). Then

B(T0)=I,
||T0−T||F≤8R,
a0:=a(T0)≤42R<10^(-3).                                  (6)

Given Tk with B(Tk)=I and ak≤10^(-3), form Uk with entries Tr(X_a X_b X_c), as in associativity-correction.md. That note proves

||Uk−Tk||F≤ak,
a(Uk)≤4ak²,
beta(Uk)≤2ak².                                          (7)

Both residuals in(7) are below0.001, so Tk+1=N(Uk) is defined. Equations(4) and(5) yield

B(Tk+1)=I,
a{k+1}≤84ak²≤ak/2,
||Tk+1−Tk||F≤ak+16ak²≤2ak.                              (8)

Thus Σak≤2a0 and the total tensor displacement after the first normalization is at most4a0≤168R. The sequence converges in the finite-dimensional tensor space for the given m, without any compactness argument varying m. Call its limit T_infinity. Continuity of the polynomial constraints gives

B(T_infinity)=I, A(T_infinity)=0,
||T_infinity−T||F≤176R.                                 (9)

Every Tk is fully symmetric, so the limit is fully symmetric.

## 3. Exact zero identification

For completeness, the exact identification is elementary and agrees with the credited Boralevi–Draisma–Horobet–Robeva characterization. A=0 implies all real symmetric slices commute, hence they are simultaneously diagonalizable in an orthonormal basis. In this basis T_rij=0 for i≠j. Full symmetry also forces T_rii=0 when r≠i, so only T_iii=lambda_i remain. B=I forces lambda_i²=1. Changing the sign of basis vector i absorbs lambda_i. Thus T_infinity∈O_m.

Combining with(9) proves the proposed GR bound. Since176·10^(-6)<1/sqrt6, the author's local-tensor-correction lemma applies to the ORIGINAL T and then yields dist_F(T,O_m)≤sqrt2 R(T).

## Attribution and limits

The Hochschild contracting-homotopy idea and exact Gerstenhaber Bianchi identity are classical operations. The exact odeco characterization is already credited by the main author. The normalization derivative and explicit bound64 were independently derived in parent author collaboration and supplied in messages during development; this is corroboration, not an independent gate. The proposed new bridge is their compatible implementation with full cubic symmetry, total HS error, exact isotropization, and a dimension-independent convergent correction. No literature novelty or campaign acceptance is inferred merely from this proof draft.

This closes only the algebraic GR premise if all displayed identities withstand review. It does not independently prove the analytic source101 reduction, approximation for nonsmooth laws, or the moderate/large-deficit portion of the full entropy target. Those remain with the main author and other assigned author assistance.
