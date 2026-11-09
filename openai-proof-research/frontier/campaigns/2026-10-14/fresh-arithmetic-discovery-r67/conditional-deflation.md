# Conditional deflation with a dimension-independent error budget

Author calculation, not a closure. This isolates exactly what a uniform lower bound for the maximum cubic value would buy. Fix 0<c≤1 and suppose the following UNPROVED premise holds in every dimension: every symmetric cubic U with R(U)≤c²/100 has max_{|v|=1}U(v,v,v)≥c. Under this premise,

dist_F(T,O)²≤(18/c²)R(T)² whenever R(T)≤c²/100.             (A)

The premise is the small-maximum branch, not an established consequence of B≈I. The proof below shows that successive dimension reduction does not introduce a further dimension factor once that premise is paid.

Choose a maximizing unit vector v and write lambda=T(v,v,v)≥c. Stationarity gives T(v,v)=lambda v. In an orthonormal tangent eigenbasis of L_v, put mu_i=T(v,e_i,e_i), M=Σmu_i², D=diag(mu_i), and S=T restricted to v-perp. The Hessian of the cubic restricted to the sphere gives mu_i≤lambda/2. Matrices have the block forms

X_0=diag(lambda,D),
X_i=[[0,mu_i e_i^t],[mu_i e_i,S_i]].

Therefore, with C0=Σ_i||[X_0,X_i]||F²,

C0≥2Σ_i mu_i²(lambda−mu_i)²≥(lambda²/2)M,
M≤2C0/c².                                                (1)

Write E=B(T)−I and define the defect discarded by compression

D0=E00²+2Σ_i E0i²+C0.

The exact residual B identity is B(S)−I=E_perp−2diag(mu_i²). Consequently

||B(S)−I||F²≤||E||F²−E00²−2Σ_i E0i²+4||E||F M+4M².       (2)

For i<j tangent, the lower-right block of the original commutator is

[S_i,S_j]+mu_i mu_j(E_ij−E_ji).

The squared sum of the added skew matrices is 2Σ_(i<j)mu_i²mu_j²≤M². The other blocks of the original commutators contribute nonnegative squares. Hence, by the triangle inequality in the direct sum of all matrix blocks,

sqrt(C(S))≤sqrt(C(T)−C0)+M.

Combining this with (2), and R=R(T), yields

R(S)²≤R²−D0+6RM+5M².                                    (3)

Since M≤2D0/c² and also M≤2R²/c², the final two terms are at most

[12R/c²+20R²/c⁴]D0.

For R≤c²/100 this bracket is at most0.122<1/2. Thus

R(S)²≤R(T)²−D0/2.                                       (4)

In particular S stays within the same small-residual regime, so the UNPROVED premise can be applied at the next step. Continue until the space is exhausted. If the successive discarded quantities are D_k and M_k, (4) and(1) give

ΣD_k≤2R(T)²,
ΣM_k≤4R(T)²/c²,
max M_k≤2R(T)²/c².                                       (5)

The successive mixed cubic blocks are mutually Frobenius orthogonal: a mixed coefficient is assigned to the first extracted direction appearing in it. Stationarity eliminates terms containing that first direction twice; diagonalization makes its remaining block have norm²3M_k. If v_k are the final orthonormal basis vectors and lambda_k their extracted cubic values, then

||T−Σlambda_k v_k^tensor3||F²=3ΣM_k.

Also B(T_k)00=lambda_k²+M_k, so

(lambda_k−1)²=(E_k,00−M_k)²/(lambda_k+1)²
≤2E_k,00²+2M_k².

Thus Σ(lambda_k−1)²≤4R(T)²+16R(T)^4/c⁴. These pure diagonal errors are orthogonal to the mixed errors. Adding and using c≤1 and R(T)≤c²/100 gives (A), with room in the stated constant18/c².

No positive conclusion is drawn without the uniform maximum premise. This argument provides a summable global bookkeeping mechanism, not the missing entrance itself. It uses ordinary spectral/Hessian calculations, not an approximate-odeco theorem from the literature.
