# Direct associativity correction in total Hilbert–Schmidt norm

AUTHOR DRAFT: a proposed closure of the global entrance step, for collaborative checking. This is not an independent campaign review. All spaces are finite dimensional real Hilbert spaces. All tensor and Hilbert–Schmidt norms are unnormalized. The cubic is fully symmetric throughout.

Let multiplication mu(x,y)=x*y have structure tensor T. Let

A(x,y,z)=(x*y)*z−x*(y*z),
a=||A||HS, B=mu mu*, beta=||B−I||F.

Here mu is viewed as a linear map V⊗V→V. Full symmetry identifies its flattening Gram matrix with B=ΣX_r². Also

a²=Σ_(r,s)||[X_r,X_s]||F²=2C.

## 1. A contracting homotopy with no unit or dimension factor

For a k-linear cochain f:V^k→V, k≥1, put

(hf)(x1,...,x{k−1})=Σ_i e_i*f(e_i,x1,...,x{k−1}).

In coordinates this contracts the flattened matrix of mu against a reshaping of f. Therefore

||hf||HS≤sqrt(||B||op)||f||HS.                            (1)

This is not a bound using the norm of the Casimir tensor or a unit: such bounds would introduce sqrt(dim V). Full metric symmetry gives the exact Casimir centrality identity

Σ_i e_i⊗(e_i*x)=Σ_i(e_i*x)⊗e_i,

because L_x is selfadjoint. No associativity assumption is involved.

Use the usual Hochschild expression

(delta f)(x1,...,x{k+1})
=x1*f(x2,...,x{k+1})
 +Σ_{j=1}^k(−1)^j f(x1,...,x_j*x{j+1},...,x{k+1})
 +(−1)^{k+1} f(x1,...,xk)*x{k+1}.

Even for nonassociative mu, direct cancellation and the exact centrality identity give

(h delta f+delta h f)(x1,...,xk)
=B f(x1,...,xk)
 −Σ_i A(x1,e_i,f(e_i,x2,...,xk))
 +(−1)^k Σ_i A(e_i,f(e_i,x1,...,x{k−1}),xk).              (2)

To verify (2), the first term of h delta f is Σ_i e_i*(e_i*f)=Bf. The internal merged-input terms cancel pairwise. The remaining initial pair is

Σ_i [x1*(e_i*f(e_i,...))−e_i*f(e_i*x1,...)]
=−Σ_i A(x1,e_i,f(e_i,...)),

where centrality moves x1 from the argument of f to the first multiplication factor. The final pair is exactly the last associator term in (2). Each error term in (2) contracts two indices between A and f, so its total HS norm is at most a||f||HS by the Frobenius bound for a matrix product. This estimate has no identity tensor left uncontracted and no dimension factor.

The exact Bianchi identity delta A=0 follows by expanding its ten terms and cancelling identical binary bracketings; equivalently it is Gerstenhaber Jacobi. The signs here give

D A_mu[H]=−delta H,
A(mu+H)=A(mu)−delta H+A(H).                              (3)

## 2. Correction when B=I

Put H=hA. Applying (2) with k=3 and f=A, and using delta A=0, gives

delta H=A−Q1−Q2,
||Q1||HS,||Q2||HS≤a².

Since ||H||HS≤a by(1), and the two quadratic compositions in A(H) each have HS norm≤||H||HS²,

||A(mu+H)||HS≤4a².                                      (4)

The crucial compatibility is that H is again a fully symmetric cubic when B=I. Direct contraction gives

H_abc=Tr(X_a X_b X_c)−Σ_k B_ak T_kbc.

The trace of three real symmetric matrices is fully symmetric (cyclicity and reversal generate every permutation). Thus if B=I,

mu+H has cubic U_abc=Tr(X_a X_b X_c).                    (5)

No projection of H onto symmetric tensors is needed.

## 3. The isometry error is quadratic as well

For B=I the slices X_a are Frobenius orthonormal. Let K(Y)=Σ_r X_r Y X_r, and set

V_ab=<X_a,K(X_b)>, D=I−V.

The Dirichlet identity is

D_ab=(1/2)Σ_r <[X_r,X_a],[X_r,X_b]>.

Indeed, expand the commutators, use symmetry and cyclic trace, and use Σ_r X_r²=I. Consequently D is positive semidefinite and tr D=C=a²/2. In particular ||D||F≤a²/2.

The mixed Gram contraction is Σ_ij T_aij U_bij=V_ab. (Equivalently, Σ_ij T_aij X_i X_j=K(X_a), by full symmetry.) Hence, writing H=U−T,

B(U)−I=−2D+Gram(H),
||B(U)−I||F≤a²+||H||HS²≤2a².                            (6)

Equations(4) and(6) provide a quadratic improvement of both errors with tensor displacement at most a. They use full symmetry, the exact B=I constraint, and TOTAL HS associator norm. The generic almost-commuting-matrix problem is not substituted for this interface.

The remaining normalization and iteration are supplied in normalization-and-entrance.md. Classical Hochschild contraction and Gerstenhaber identities are explicitly credited; the quantitative symmetric total-HS implementation and its compatibility with exact isotropization are the proposed author bridge, not asserted literature novelty.
